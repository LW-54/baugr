//! Domain-agnostic integration tests, value-derived conditional promise proofs,
//! static upper-bound discharge tests, invariant proofs, and purity guards for `baugr` v0.3.

use std::collections::BTreeSet;
use std::fs;
use std::path::Path;

use baugr::{
    AgentSet, AgreementConflict, Binding, Body, BodyAlgebra, BudgetDeficit, CoarseGrainError, Cond,
    ConditionWarning, DeriveAlgebra, EvalError, HierarchyError, LinkKind, LocalView, MaxOne,
    NodeKind, Obs, Promise, PromiseSystem, ProviderCardinalityError, QuorumLaw, QuorumShortfall,
    ResolutionView, ResourceMonoid, SstError, SstGraph, SstNode, SymmetricMeet, Unbounded,
    UniqueProviderLaw, ValencyLaw, directory_of, project_sst,
};

#[derive(Clone, Debug, PartialEq, Eq)]
struct PowerOffer {
    voltage: u16,
    max_watts: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct PowerUse {
    voltage: u16,
    watts: u32,
}

struct GridAlgebra;

impl BodyAlgebra for GridAlgebra {
    type Offer = PowerOffer;
    type Use = PowerUse;
    type Overlap = u32;
    fn overlap(&self, o: &PowerOffer, u: &PowerUse) -> Option<u32> {
        if o.voltage != u.voltage {
            return None;
        }
        (u.watts <= o.max_watts).then_some(u.watts)
    }
}

fn build_microgrid() -> PromiseSystem<&'static str, &'static str, GridAlgebra> {
    let mut sys = PromiseSystem::new(GridAlgebra);
    sys.add_promise(Promise::offer(
        "grid:mains",
        "grid",
        AgentSet::All,
        PowerOffer {
            voltage: 230,
            max_watts: 5000,
        },
    ));
    sys.add_promise(Promise::accept(
        "bat:sense_grid",
        "battery",
        AgentSet::single("grid"),
        PowerUse {
            voltage: 230,
            watts: 0,
        },
    ));
    sys.add_promise(
        Promise::offer(
            "bat:backup",
            "battery",
            AgentSet::All,
            PowerOffer {
                voltage: 230,
                max_watts: 1500,
            },
        )
        .when(!Cond::assisted("bat:sense_grid")),
    );
    sys.add_promise(Promise::accept(
        "hosp:draw",
        "hospital",
        AgentSet::of(["grid", "battery"]),
        PowerUse {
            voltage: 230,
            watts: 1000,
        },
    ));
    sys
}

#[test]
fn domain_microgrid_stratified_failover_self_assessment_and_static_discharge() {
    let mut sys = build_microgrid();

    // Static upper-bound discharge (Lean theorem `static_discharge_universal`):
    // Even though `bat:backup` is OFF under optimistic α, `static_upper_bound()` includes
    // its worst-case 1000W hospital load and proves 1000W <= 1500W for ALL runtime scenarios α!
    let upper = sys.static_upper_bound();
    assert!(
        ResolutionView::new(&sys, &upper)
            .check_valency("bat:backup", 1500_u32, |b| b.overlap)
            .is_ok()
    );

    // Normal operation: mains kept -> battery backup stays off; hospital uniquely uses grid.
    let r_normal = sys.resolve_optimistic().expect("stratified");
    assert!(r_normal.is_quenched("grid:mains"));
    assert!(!r_normal.is_quenched("bat:backup"));
    assert!(
        ResolutionView::new(&sys, &r_normal)
            .check(&UniqueProviderLaw {
                use_id: "hosp:draw"
            })
            .is_ok()
    );

    // Consistent self-assessment: if battery's own sensor `bat:sense_grid` fails,
    // `Assisted("bat:sense_grid")` becomes false and failover triggers!
    let r_sensor_fail = sys
        .resolve(|obs, p| !(*obs == "battery" && *p == "bat:sense_grid"))
        .expect("stratified");
    assert!(r_sensor_fail.is_quenched("bat:backup"));

    // Outage: mains broken -> battery backup quenches; 1000W <= 1500W valency holds.
    let r_outage = sys.resolve(|_, p| *p != "grid:mains").expect("stratified");
    assert!(r_outage.is_quenched("bat:backup"));
    assert!(
        r_outage
            .bindings
            .iter()
            .any(|b| b.offer_id == "bat:backup" && b.consumer == "hospital" && b.overlap == 1000)
    );
    let cap_law = ValencyLaw {
        offer_id: "bat:backup",
        capacity: 1500_u32,
        weight: |b: &Binding<&str, &str, u32>| b.overlap,
    };
    assert!(ResolutionView::new(&sys, &r_outage).check(&cap_law).is_ok());

    // Add 800W factory load -> `static_upper_bound()` IMMEDIATELY catches the hidden blackout
    // overdraw (1800W > 1500W) even though optimistic α draws 0W from `bat:backup`!
    sys.add_promise(Promise::accept(
        "fact:draw",
        "factory",
        AgentSet::of(["grid", "battery"]),
        PowerUse {
            voltage: 230,
            watts: 800,
        },
    ));
    let upper_over = sys.static_upper_bound();
    let static_err = ResolutionView::new(&sys, &upper_over)
        .check(&cap_law)
        .expect_err("static upper bound catches blackout overdraw");
    assert_eq!(static_err.used, 1800);
    assert_eq!(static_err.capacity, 1500);

    let r_overload = sys.resolve(|_, p| *p != "grid:mains").expect("stratified");
    let err = ResolutionView::new(&sys, &r_overload)
        .check(&cap_law)
        .expect_err("expected valency deficit");
    let dyn_err: &dyn core::error::Error = &err;
    assert!(dyn_err.to_string().contains("1800"));
    assert_eq!(err.used, 1800);
    assert_eq!(err.capacity, 1500);

    // Observer-local split blackout: battery sees grid down while factory sees grid up.
    let r_split = sys
        .resolve(|obs, p| !(*obs == "battery" && *p == "grid:mains"))
        .expect("stratified");
    assert!(r_split.is_quenched("bat:backup"));
    assert!(
        r_split
            .bindings
            .iter()
            .any(|b| b.offer_id == "grid:mains" && b.consumer == "factory")
    );
    assert!(
        r_split
            .bindings
            .iter()
            .any(|b| b.offer_id == "bat:backup" && b.consumer == "factory")
    );
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum AllocOffer {
    Cell(u32),
    Req { watts: u32, prio: u8 },
    Grant(u32),
    DrawNotice(u32),
    Diesel,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum AllocUse {
    AcceptReq,
    ObserveNotice,
    Draw { min: u32, max: u32 },
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum AllocRule {
    PriorityGrant { recipient: &'static str },
    ProportionalGrant { recipient: &'static str },
    PeerResidualUse { pool_cap: u32, max_wanted: u32 },
    ResidualReq { total_wanted: u32 },
}

struct AllocAlg;

impl BodyAlgebra for AllocAlg {
    type Offer = AllocOffer;
    type Use = AllocUse;
    type Overlap = u32;
    fn overlap(&self, o: &AllocOffer, u: &AllocUse) -> Option<u32> {
        match (o, u) {
            (AllocOffer::Req { watts, .. }, AllocUse::AcceptReq)
            | (AllocOffer::DrawNotice(watts), AllocUse::ObserveNotice) => Some(*watts),
            (AllocOffer::Grant(w), AllocUse::Draw { min, max }) if w >= min => Some((*w).min(*max)),
            _ => None,
        }
    }
}

impl DeriveAlgebra<&'static str, &'static str, AllocRule> for AllocAlg {
    fn derive_offer(
        &self,
        rule: &AllocRule,
        obs: &LocalView<'_, &'static str, &'static str, Self>,
    ) -> Option<AllocOffer> {
        let cap: u32 = obs
            .interior_entries()
            .iter()
            .filter_map(|(_, _, b)| match b {
                Body::Offer(AllocOffer::Cell(w)) => Some(*w),
                _ => None,
            })
            .sum();
        match rule {
            AllocRule::PriorityGrant { recipient } => {
                let mut reqs: Vec<(u8, &'static str, u32)> = obs
                    .assisted("bank:recv")
                    .filter_map(|e| match e.offer {
                        AllocOffer::Req { watts, prio } => Some((*prio, *e.promiser, *watts)),
                        _ => None,
                    })
                    .collect();
                reqs.sort_by_key(|(p, a, _)| (*p, *a));
                let mut rem = cap;
                for (_, agent, wanted) in reqs {
                    let g = wanted.min(rem);
                    rem = rem.saturating_sub(g);
                    if agent == *recipient {
                        return (g > 0).then_some(AllocOffer::Grant(g));
                    }
                }
                None
            }
            AllocRule::ProportionalGrant { recipient } => {
                let reqs: Vec<(&'static str, u32)> = obs
                    .assisted("bank:recv")
                    .filter_map(|e| match e.offer {
                        AllocOffer::Req { watts, .. } => Some((*e.promiser, *watts)),
                        _ => None,
                    })
                    .collect();
                let total: u32 = reqs.iter().map(|(_, w)| *w).sum();
                if total == 0 {
                    return None;
                }
                for (agent, wanted) in reqs {
                    if agent == *recipient {
                        let g = if total <= cap {
                            wanted
                        } else {
                            wanted.saturating_mul(cap).checked_div(total).unwrap_or(0)
                        };
                        return (g > 0).then_some(AllocOffer::Grant(g));
                    }
                }
                None
            }
            AllocRule::ResidualReq { total_wanted } => {
                let got: u32 = obs.assisted("clinic:draw").map(|e| e.overlap).sum();
                let left = total_wanted.saturating_sub(got);
                (left > 0).then_some(AllocOffer::Req {
                    watts: left,
                    prio: 1,
                })
            }
            AllocRule::PeerResidualUse { .. } => None,
        }
    }

    fn derive_use(
        &self,
        rule: &AllocRule,
        obs: &LocalView<'_, &'static str, &'static str, Self>,
    ) -> Option<AllocUse> {
        match rule {
            AllocRule::PeerResidualUse {
                pool_cap,
                max_wanted,
            } => {
                let taken: u32 = obs.assisted("clinic:watch_hosp").map(|e| e.overlap).sum();
                let left = pool_cap.saturating_sub(taken).min(*max_wanted);
                (left > 0).then_some(AllocUse::Draw { min: 1, max: left })
            }
            _ => None,
        }
    }
}

fn build_alloc_bank_system() -> Result<
    PromiseSystem<&'static str, &'static str, AllocAlg, AllocRule>,
    HierarchyError<&'static str>,
> {
    let mut sys = PromiseSystem::with_rules(AllocAlg);
    sys.add_superagent("bank", true);
    for (c, pid) in [("c1", "c1:p"), ("c2", "c2:p"), ("c3", "c3:p")] {
        sys.contain("bank", c)?;
        sys.add_promise(Promise::offer(pid, c, AgentSet::All, AllocOffer::Cell(750)));
    }
    sys.add_promise(
        Promise::accept(
            "bank:recv",
            "bank",
            AgentSet::of(["hosp", "clinic"]),
            AllocUse::AcceptReq,
        )
        .with_scope(AgentSet::All),
    );
    sys.add_promise(Promise::offer(
        "hosp:req",
        "hosp",
        AgentSet::single("bank"),
        AllocOffer::Req {
            watts: 1000,
            prio: 1,
        },
    ));
    sys.add_promise(Promise::offer(
        "clinic:req",
        "clinic",
        AgentSet::single("bank"),
        AllocOffer::Req {
            watts: 800,
            prio: 2,
        },
    ));
    let bank_obs = vec![
        Obs::assisted("bank:recv"),
        Obs::interior("c1:p"),
        Obs::interior("c2:p"),
        Obs::interior("c3:p"),
    ];
    sys.add_promise(Promise::derive_offer(
        "bank:grant_hosp",
        "bank",
        AgentSet::single("hosp"),
        bank_obs.clone(),
        AllocRule::PriorityGrant { recipient: "hosp" },
    ));
    sys.add_promise(Promise::derive_offer(
        "bank:grant_clinic",
        "bank",
        AgentSet::single("clinic"),
        bank_obs,
        AllocRule::PriorityGrant {
            recipient: "clinic",
        },
    ));
    sys.add_promise(Promise::accept(
        "hosp:draw",
        "hosp",
        AgentSet::single("bank"),
        AllocUse::Draw {
            min: 1000,
            max: 1000,
        },
    ));
    sys.add_promise(
        Promise::accept(
            "clinic:draw",
            "clinic",
            AgentSet::single("bank"),
            AllocUse::Draw { min: 1, max: 800 },
        )
        .with_scope(AgentSet::All),
    );
    sys.add_promise(Promise::derive_offer(
        "clinic:req_aux",
        "clinic",
        AgentSet::single("aux"),
        vec![Obs::assisted("clinic:draw")],
        AllocRule::ResidualReq { total_wanted: 800 },
    ));
    sys.add_promise(
        Promise::offer(
            "clinic:diesel",
            "clinic",
            AgentSet::single("clinic"),
            AllocOffer::Diesel,
        )
        .when(!Cond::assisted("clinic:draw")),
    );
    Ok(sys)
}

#[test]
fn domain_value_derived_provider_allocation_and_grouped_budget() {
    let mut sys = build_alloc_bank_system().expect("acyclic");

    let r = sys
        .resolve(|obs, p| !(*obs == "bank" && *p == "c1:p"))
        .expect("stratified");
    assert_eq!(r.offer("bank:grant_hosp"), Some(&AllocOffer::Grant(1000)));
    assert_eq!(r.offer("bank:grant_clinic"), Some(&AllocOffer::Grant(500)));
    assert_eq!(
        r.offer("clinic:req_aux"),
        Some(&AllocOffer::Req {
            watts: 300,
            prio: 1
        })
    );
    assert!(!r.is_quenched("clinic:diesel"));

    let view = ResolutionView::new(&sys, &r);
    assert!(
        view.check_budget(
            |_, b| (b.promiser == "bank").then_some((b.promiser, b.overlap)),
            |_| 1500_u32
        )
        .is_ok()
    );
    assert_eq!(
        view.check_budget(
            |_, b| (b.promiser == "bank").then_some((b.promiser, b.overlap)),
            |_| 1400_u32
        ),
        Err(BudgetDeficit {
            group: "bank",
            used: 1500,
            capacity: 1400,
        })
    );

    sys.add_promise(
        Promise::accept(
            "clinic:draw",
            "clinic",
            AgentSet::single("bank"),
            AllocUse::Draw { min: 800, max: 800 },
        )
        .with_scope(AgentSet::All),
    );
    let r_strict = sys
        .resolve(|obs, p| !(*obs == "bank" && *p == "c1:p"))
        .expect("stratified");
    assert!(r_strict.is_quenched("clinic:diesel"));
    let r_solo = sys
        .resolve(|obs, p| !(*obs == "bank" && matches!(*p, "c1:p" | "hosp:req")))
        .expect("stratified");
    assert_eq!(
        r_solo.offer("bank:grant_clinic"),
        Some(&AllocOffer::Grant(800))
    );
    assert!(!r_solo.is_quenched("clinic:diesel"));

    let bank_obs = vec![
        Obs::assisted("bank:recv"),
        Obs::interior("c1:p"),
        Obs::interior("c2:p"),
        Obs::interior("c3:p"),
    ];
    sys.add_promise(Promise::derive_offer(
        "bank:grant_hosp",
        "bank",
        AgentSet::single("hosp"),
        bank_obs.clone(),
        AllocRule::ProportionalGrant { recipient: "hosp" },
    ));
    sys.add_promise(Promise::derive_offer(
        "bank:grant_clinic",
        "bank",
        AgentSet::single("clinic"),
        bank_obs,
        AllocRule::ProportionalGrant {
            recipient: "clinic",
        },
    ));
    let r_prop = sys
        .resolve(|obs, p| !(*obs == "bank" && *p == "c1:p"))
        .expect("stratified");
    assert_eq!(
        r_prop.offer("bank:grant_hosp"),
        Some(&AllocOffer::Grant(833))
    );
    assert_eq!(
        r_prop.offer("bank:grant_clinic"),
        Some(&AllocOffer::Grant(666))
    );
}

#[test]
fn domain_value_derived_peer_residual_and_cycle_rejection() {
    let mut peer = PromiseSystem::with_rules(AllocAlg);
    peer.add_promise(Promise::offer(
        "bus",
        "grid",
        AgentSet::All,
        AllocOffer::Grant(1500),
    ));
    peer.add_promise(Promise::offer(
        "hosp:notice",
        "hosp",
        AgentSet::All,
        AllocOffer::DrawNotice(1000),
    ));
    peer.add_promise(Promise::accept(
        "clinic:watch_hosp",
        "clinic",
        AgentSet::single("hosp"),
        AllocUse::ObserveNotice,
    ));
    peer.add_promise(Promise::derive_use(
        "clinic:draw_leftover",
        "clinic",
        AgentSet::single("grid"),
        vec![Obs::assisted("clinic:watch_hosp")],
        AllocRule::PeerResidualUse {
            pool_cap: 1500,
            max_wanted: 800,
        },
    ));
    let r_peer = peer.resolve_optimistic().expect("stratified");
    assert_eq!(
        r_peer.use_body("clinic:draw_leftover"),
        Some(&AllocUse::Draw { min: 1, max: 500 })
    );
    assert!(
        r_peer
            .bindings
            .iter()
            .any(|b| b.use_id == "clinic:draw_leftover" && b.overlap == 500)
    );

    let mut cyc = PromiseSystem::with_rules(AllocAlg);
    cyc.add_promise(Promise::derive_offer(
        "a",
        "x",
        AgentSet::All,
        vec![Obs::self_promise("b")],
        AllocRule::ResidualReq { total_wanted: 10 },
    ));
    cyc.add_promise(Promise::derive_offer(
        "b",
        "x",
        AgentSet::All,
        vec![Obs::self_promise("a")],
        AllocRule::ResidualReq { total_wanted: 10 },
    ));
    assert!(matches!(
        cyc.resolve_optimistic(),
        Err(EvalError::UnstratifiableCycle(_))
    ));
}

#[test]
fn domain_raft_opaque_superagent_and_irreducible_quorum() {
    #[derive(Clone, Debug, PartialEq, Eq)]
    enum Cap {
        ReplicaVote,
        LinearizableKv,
        AppReady,
    }
    let alg = SymmetricMeet::new(|o: &Cap, u: &Cap| (o == u).then(|| o.clone()));
    let mut sys = PromiseSystem::<&str, &str, _>::new(alg);

    sys.add_superagent("raft", true);
    for n in ["n1", "n2", "n3"] {
        sys.contain("raft", n).expect("acyclic");
        sys.add_promise(Promise::offer(n, n, AgentSet::All, Cap::ReplicaVote));
    }
    assert_eq!(
        sys.contain("raft", "raft"),
        Err(HierarchyError::SelfContainment("raft"))
    );
    assert_eq!(
        sys.contain("n1", "raft"),
        Err(HierarchyError::Cycle {
            superagent: "n1",
            child: "raft",
        })
    );

    sys.add_promise(
        Promise::offer("raft:kv", "raft", AgentSet::All, Cap::LinearizableKv).when(Cond::at_least(
            2,
            vec![
                Cond::interior("n1"),
                Cond::interior("n2"),
                Cond::interior("n3"),
            ],
        )),
    );
    sys.add_promise(Promise::offer(
        "client:local_clock",
        "client",
        AgentSet::All,
        Cap::AppReady,
    ));
    sys.add_promise(Promise::accept(
        "client:use_kv",
        "client",
        AgentSet::single("raft"),
        Cap::LinearizableKv,
    ));
    sys.add_promise(Promise::accept(
        "client:pierce_n1",
        "client",
        AgentSet::single("n1"),
        Cap::ReplicaVote,
    ));
    sys.add_promise(
        Promise::offer("client:app", "client", AgentSet::All, Cap::AppReady)
            .when(Cond::assisted("client:use_kv")),
    );

    let r3 = sys.resolve_optimistic().expect("stratified");
    assert!(r3.is_quenched("raft:kv"));
    assert!(r3.is_quenched("client:app"));
    assert!(!r3.bindings.iter().any(|b| b.use_id == "client:pierce_n1"));

    let r2 = sys.resolve(|_, p| *p != "n3").expect("stratified");
    assert!(r2.is_quenched("raft:kv"));
    let r1 = sys
        .resolve(|_, p| *p != "n2" && *p != "n3")
        .expect("stratified");
    assert!(!r1.is_quenched("raft:kv"));
    assert!(!r1.is_quenched("client:app"));
    assert!(r1.is_quenched("client:local_clock"));

    let dir = directory_of(&sys, &"raft");
    assert!(dir.is_opaque);
    assert_eq!(dir.interior_agents, BTreeSet::from(["n1", "n2", "n3"]));
    assert_eq!(dir.surface_promises, BTreeSet::from(["raft:kv"]));

    let sst = project_sst(&sys);
    let cone = sst.reverse_causal_cone(&SstNode::Promise("client:app"));
    assert!(cone.contains(&SstNode::Promise("raft:kv")));
    assert!(cone.contains(&SstNode::Promise("n1")));
    assert!(!cone.contains(&SstNode::Promise("client:local_clock")));
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum CloudSvc {
    Terms,
    Slot { port: u16, proto_ver: u8 },
    Power,
    Net,
    Dns,
    Tls,
}

struct CloudAlg;

impl BodyAlgebra for CloudAlg {
    type Offer = CloudSvc;
    type Use = CloudSvc;
    type Overlap = (Option<u16>, Option<u8>);
    fn overlap(&self, o: &CloudSvc, u: &CloudSvc) -> Option<Self::Overlap> {
        match (o, u) {
            (CloudSvc::Terms, CloudSvc::Terms)
            | (CloudSvc::Power, CloudSvc::Power)
            | (CloudSvc::Net, CloudSvc::Net)
            | (CloudSvc::Dns, CloudSvc::Dns)
            | (CloudSvc::Tls, CloudSvc::Tls) => Some((None, None)),
            (
                CloudSvc::Slot {
                    port: op,
                    proto_ver: ov,
                },
                CloudSvc::Slot {
                    port: up,
                    proto_ver: uv,
                },
            ) if op == up && ov == uv => Some((Some(*op), Some(*ov))),
            _ => None,
        }
    }
}

fn build_tenancy_fleet()
-> Result<PromiseSystem<&'static str, &'static str, CloudAlg>, HierarchyError<&'static str>> {
    let mut sys = PromiseSystem::new(CloudAlg);
    sys.add_superagent("host1", false);
    sys.contain("host1", "tenant1")?;
    sys.add_superagent("host2", false);
    sys.contain("host2", "tenant2")?;

    sys.add_promise(Promise::accept(
        "h1:accept_terms",
        "host1",
        AgentSet::All,
        CloudSvc::Terms,
    ));
    sys.add_promise(
        Promise::offer(
            "h1:slot_80",
            "host1",
            AgentSet::All,
            CloudSvc::Slot {
                port: 80,
                proto_ver: 2,
            },
        )
        .when(Cond::assisted("h1:accept_terms")),
    );
    sys.add_promise(
        Promise::offer("h1:power", "host1", AgentSet::All, CloudSvc::Power)
            .when(Cond::accepted("h1:slot_80")),
    );
    sys.add_promise(Promise::offer(
        "t1:terms",
        "tenant1",
        AgentSet::single("host1"),
        CloudSvc::Terms,
    ));
    sys.add_promise(Promise::accept(
        "t1:use_slot",
        "tenant1",
        AgentSet::single("host1"),
        CloudSvc::Slot {
            port: 80,
            proto_ver: 2,
        },
    ));
    sys.add_promise(Promise::offer(
        "h2:slot_80",
        "host2",
        AgentSet::single("tenant2"),
        CloudSvc::Slot {
            port: 80,
            proto_ver: 2,
        },
    ));
    sys.add_promise(Promise::accept(
        "t2:use_slot",
        "tenant2",
        AgentSet::single("host2"),
        CloudSvc::Slot {
            port: 80,
            proto_ver: 2,
        },
    ));
    Ok(sys)
}

#[test]
fn domain_tenancy_and_generalized_laws() {
    let mut sys = build_tenancy_fleet().expect("acyclic");

    let r = sys.resolve_optimistic().expect("stratified");
    assert!(r.is_quenched("h1:slot_80"));
    assert!(r.is_quenched("h1:power"));

    let view = ResolutionView::new(&sys, &r);
    let check_ports = |v: &ResolutionView<'_, &'static str, &'static str, CloudAlg>| {
        v.check_disjoint(|s, b| {
            let port = b.overlap.0?;
            let host = s.parent_of(&b.consumer).copied().unwrap_or(b.promiser);
            Some((host, port))
        })
    };
    assert!(check_ports(&view).is_ok());

    assert!(
        view.check_agreement(|_, b| b.overlap.1.map(|ver| ((), ver)))
            .is_ok()
    );
    assert!(
        view.check(&QuorumLaw {
            use_id: "t1:use_slot",
            min_providers: 1
        })
        .is_ok()
    );
    assert_eq!(
        view.check(&QuorumLaw {
            use_id: "t1:use_slot",
            min_providers: 2
        }),
        Err(QuorumShortfall {
            use_id: "t1:use_slot",
            required: 2,
            actual: 1,
        })
    );
    assert_eq!(
        view.check(&UniqueProviderLaw {
            use_id: "nonexistent"
        }),
        Err(ProviderCardinalityError {
            use_id: "nonexistent",
            actual: 0,
        })
    );
    assert!(
        view.check(&ValencyLaw {
            offer_id: "h1:slot_80",
            capacity: (MaxOne::One, Unbounded),
            weight: |_: &Binding<_, _, _>| (MaxOne::One, Unbounded),
        })
        .is_ok()
    );
    assert_eq!(MaxOne::One.add(&MaxOne::One), MaxOne::Overflow);

    sys.contain("host1", "tenant1b").expect("acyclic");
    sys.add_promise(Promise::accept(
        "t1b:use_slot",
        "tenant1b",
        AgentSet::single("host1"),
        CloudSvc::Slot {
            port: 80,
            proto_ver: 2,
        },
    ));
    let r_collide = sys.resolve_optimistic().expect("stratified");
    let err = check_ports(&ResolutionView::new(&sys, &r_collide))
        .expect_err("expected per-host port collision");
    assert_eq!(err.key, ("host1", 80));

    sys.add_promise(Promise::offer(
        "h2:slot_443",
        "host2",
        AgentSet::single("tenant2"),
        CloudSvc::Slot {
            port: 443,
            proto_ver: 3,
        },
    ));
    sys.add_promise(Promise::accept(
        "t2:use_443",
        "tenant2",
        AgentSet::single("host2"),
        CloudSvc::Slot {
            port: 443,
            proto_ver: 3,
        },
    ));
    let r_disagree = sys.resolve_optimistic().expect("stratified");
    let conflict = ResolutionView::new(&sys, &r_disagree)
        .check_agreement(|_, b| b.overlap.1.map(|ver| ((), ver)))
        .expect_err("expected protocol version disagreement");
    assert_eq!(
        conflict,
        AgreementConflict {
            group: (),
            first_value: 2,
            first_binding: ("h1:slot_80", "t1:use_slot"),
            conflicting_value: 3,
            conflicting_binding: ("h2:slot_443", "t2:use_443"),
        }
    );
}

#[test]
fn domain_bidirectional_protocol_complete_info_and_cycles() {
    let mut sys = PromiseSystem::<&str, &str, _>::new(CloudAlg);
    sys.add_promise(Promise::offer(
        "A:net",
        "A",
        AgentSet::single("B"),
        CloudSvc::Net,
    ));
    sys.add_promise(
        Promise::accept("B:use_net", "B", AgentSet::single("A"), CloudSvc::Net)
            .with_scope(AgentSet::of(["B", "A"])),
    );
    sys.add_promise(
        Promise::offer("B:dns", "B", AgentSet::single("A"), CloudSvc::Dns)
            .when(Cond::assisted("B:use_net")),
    );
    sys.add_promise(
        Promise::accept("A:use_dns", "A", AgentSet::single("B"), CloudSvc::Dns)
            .with_scope(AgentSet::single("A")), // Omits B -> triggers complete-info warning!
    );
    sys.add_promise(
        Promise::offer("A:tls", "A", AgentSet::single("B"), CloudSvc::Tls)
            .when(Cond::assisted("A:use_dns")),
    );
    // Also check SelfPromise incomplete info (B cannot see A's private self-promise)!
    sys.add_promise(
        Promise::offer("A:private_flag", "A", AgentSet::single("A"), CloudSvc::Net)
            .with_scope(AgentSet::single("A")),
    );
    sys.add_promise(
        Promise::offer("A:gated", "A", AgentSet::single("B"), CloudSvc::Dns)
            .when(Cond::self_promise("A:private_flag")),
    );

    sys.add_promise(
        Promise::offer("X:loop1", "X", AgentSet::All, CloudSvc::Net)
            .when(Cond::self_promise("X:loop2")),
    );
    sys.add_promise(
        Promise::offer("X:loop2", "X", AgentSet::All, CloudSvc::Net)
            .when(Cond::self_promise("X:loop1")),
    );

    let r = sys.resolve_optimistic().expect("stratified");
    assert!(r.is_quenched("A:tls"));
    assert!(!r.is_quenched("X:loop1"));
    assert!(!r.is_quenched("X:loop2"));

    let warns = sys.check_complete_information();
    assert!(warns.iter().any(|w| w.conditional_promise == "A:tls"
        && w.dependency == "A:use_dns"
        && w.blind_target == "B"));
    assert!(warns.iter().any(|w| w.conditional_promise == "A:gated"
        && w.dependency == "A:private_flag"
        && w.blind_target == "B"));

    let mut bad = PromiseSystem::<&str, &str, _>::new(CloudAlg);
    bad.add_promise(
        Promise::offer("p", "z", AgentSet::All, CloudSvc::Net).when(!Cond::self_promise("q")),
    );
    bad.add_promise(
        Promise::offer("q", "z", AgentSet::All, CloudSvc::Net).when(!Cond::self_promise("p")),
    );
    assert!(matches!(
        bad.resolve_optimistic(),
        Err(EvalError::UnstratifiableCycle(_))
    ));
}

#[test]
fn static_lint_overwrites_null_potent_and_nested_negation() {
    let mut dbl = PromiseSystem::<&str, &str, _>::new(CloudAlg);
    assert!(
        dbl.add_promise(Promise::offer("a", "z", AgentSet::All, CloudSvc::Net))
            .is_none()
    );
    assert!(
        dbl.add_promise(Promise::offer("a", "z", AgentSet::All, CloudSvc::Net))
            .is_some()
    );
    dbl.add_promise(
        Promise::offer("b", "z", AgentSet::All, CloudSvc::Dns).when(!!Cond::self_promise("a")),
    );
    let r_dbl = dbl
        .resolve_optimistic()
        .expect("double negation is positive");
    assert!(r_dbl.is_quenched("b"));
    assert_eq!(r_dbl.strata.get("a"), r_dbl.strata.get("b"));

    let mut lint_sys = PromiseSystem::<&str, &str, _>::new(CloudAlg);
    lint_sys.add_promise(Promise::offer("x:off", "x", AgentSet::All, CloudSvc::Net));
    lint_sys.add_promise(Promise::accept(
        "y:lonely",
        "y",
        AgentSet::single("ghost"),
        CloudSvc::Net,
    ));
    lint_sys.add_promise(
        Promise::offer("y:bad", "y", AgentSet::All, CloudSvc::Dns).when(Cond::all(vec![
            Cond::self_promise("missing"),
            Cond::assisted("x:off"),
            Cond::assisted("y:lonely"),
            Cond::interior("x:off"),
        ])),
    );
    let diagnostics = lint_sys.lint();
    assert!(diagnostics.iter().any(|w| matches!(
        w,
        ConditionWarning::DanglingRef {
            referenced: "missing",
            ..
        }
    )));
    assert!(diagnostics.iter().any(|w| matches!(
        w,
        ConditionWarning::WrongPromiser {
            referenced: "x:off",
            ..
        }
    )));
    assert!(diagnostics.iter().any(|w| matches!(
        w,
        ConditionWarning::WrongPolarity {
            expected_offer: false,
            ..
        }
    )));
    assert!(diagnostics.iter().any(|w| matches!(
        w,
        ConditionWarning::NonInteriorRef {
            referenced: "x:off",
            ..
        }
    )));
    assert!(diagnostics.iter().any(|w| matches!(
        w,
        ConditionWarning::UnsatisfiableMinCount {
            referenced: "y:lonely",
            required: 1,
            max_possible: 0,
            ..
        }
    )));
}

#[test]
fn strict_gamma_3_4_invariants_dual_links_and_coarse_graining() {
    let mut g = SstGraph::new();
    g.add_node("love", NodeKind::Concept).unwrap();
    g.add_node("butterfly", NodeKind::Thing).unwrap();
    g.add_node("wing", NodeKind::Thing).unwrap();
    g.add_node("flight", NodeKind::Event).unwrap();
    g.add_node("landing", NodeKind::Event).unwrap();
    g.add_node("blue", NodeKind::Concept).unwrap();
    g.add_node("sky", NodeKind::Concept).unwrap();

    assert!(g.add_node("flight", NodeKind::Event).is_ok());
    assert_eq!(
        g.add_node("flight", NodeKind::Concept),
        Err(SstError::KindConflict {
            node: "flight",
            existing: NodeKind::Event,
            attempted: NodeKind::Concept,
        })
    );

    assert!(matches!(
        g.add_edge("love", LinkKind::Near, "butterfly"),
        Err(SstError::DisallowedTransition { .. })
    ));
    assert!(
        g.add_edge("butterfly", LinkKind::Contains, "flight")
            .is_err()
    );
    assert!(
        g.add_edge("flight", LinkKind::Expresses, "butterfly")
            .is_err()
    );
    assert!(
        g.add_edge("butterfly", LinkKind::LeadsTo, "flight")
            .is_err()
    );
    assert!(
        g.add_edge("flight", LinkKind::Expresses, "landing")
            .is_err()
    );

    g.add_edge("landing", LinkKind::Follows, "flight").unwrap();
    g.add_edge("flight", LinkKind::Contains, "butterfly")
        .unwrap();
    g.add_edge("butterfly", LinkKind::Contains, "wing").unwrap();
    g.add_edge("butterfly", LinkKind::Expresses, "blue")
        .unwrap();
    g.add_edge("wing", LinkKind::ContainedBy, "butterfly")
        .unwrap();
    g.add_edge("blue", LinkKind::Near, "sky").unwrap();

    assert_eq!(
        g.forward_causal_cone(&"flight"),
        BTreeSet::from(["flight", "landing"])
    );
    assert!(g.sources(LinkKind::LeadsTo).contains("flight"));
    assert!(g.sinks(LinkKind::LeadsTo).contains("landing"));
    assert!(
        g.reachable_along(&"sky", LinkKind::Near, false)
            .contains("blue")
    );

    assert_eq!(
        g.add_edge("ghost", LinkKind::LeadsTo, "flight"),
        Err(SstError::UnknownNode("ghost"))
    );
    g.add_node("takeoff", NodeKind::Event).unwrap();
    g.add_node("hover", NodeKind::Event).unwrap();
    g.add_edge("takeoff", LinkKind::LeadsTo, "flight").unwrap();
    g.add_edge("flight", LinkKind::LeadsTo, "hover").unwrap();
    g.add_edge("hover", LinkKind::LeadsTo, "landing").unwrap();
    assert!(g.branching_points(LinkKind::LeadsTo).contains("flight"));
    assert!(g.appointed_hubs(LinkKind::LeadsTo).contains("landing"));

    let q = g
        .coarse_grain(|n| match *n {
            "butterfly" | "wing" => "insect",
            other => other,
        })
        .expect("homogeneous grain");
    assert_eq!(q.kind_of(&"insect"), Some(NodeKind::Thing));
    assert_eq!(q.axis_edges(LinkKind::Contains).len(), 1);
    assert_eq!(q.axis_edges(LinkKind::Expresses).len(), 1);

    assert!(matches!(
        g.coarse_grain(|n| if *n == "flight" || *n == "butterfly" {
            "bad"
        } else {
            *n
        }),
        Err(CoarseGrainError { grain: "bad", .. })
    ));
}

#[test]
fn l0_purity_boundary_contains_zero_domain_or_io_leakage() {
    fn visit_rs(dir: &Path, out: &mut Vec<std::path::PathBuf>) {
        for entry in fs::read_dir(dir).expect("read dir") {
            let path = entry.expect("dir entry").path();
            if path.is_dir() {
                visit_rs(&path, out);
            } else if path.extension().and_then(|e| e.to_str()) == Some("rs") {
                out.push(path);
            }
        }
    }

    let forbidden = [
        "nixos",
        "systemd",
        "tailscale",
        "cedar",
        "biscuit",
        "sops",
        "nixconf",
        "astrolabe",
        "skidbladnir",
        "ivaldi",
        "verft",
        "std::fs",
        "std::process",
        "clap",
        "toml",
        "serde",
    ];
    let mut files = Vec::new();
    visit_rs(
        &Path::new(env!("CARGO_MANIFEST_DIR")).join("src"),
        &mut files,
    );
    assert!(files.len() >= 8, "expected modular src/ tree");
    for path in files {
        let text = fs::read_to_string(&path)
            .expect("read rs file")
            .to_lowercase();
        for word in &forbidden {
            assert!(
                !text.contains(word),
                "L0 purity violation: `{word}` found in {}",
                path.display()
            );
        }
    }
}
