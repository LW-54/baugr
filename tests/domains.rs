//! Domain-agnostic integration tests, symmetric value-derived conditional promise
//! proofs (`±f(obs) | C`), recursive opaque event-horizon tests, channel-sharp
//! `may_overlap` tests, and L0 purity guards for `baugr` v0.4.

use std::collections::BTreeSet;
use std::fs;
use std::path::Path;

use baugr::{
    AgentSet, Body, BodyAlgebra, CoarseGrainError, Cond, ConditionWarning, DeriveAlgebra,
    EvalError, HierarchyError, LinkKind, LocalView, NodeKind, Obs, Promise, PromiseSystem, SpecRef,
    SstError, SstGraph, SstNode, directory_of, project_sst,
};

#[derive(Clone, Debug, PartialEq, Eq)]
enum PowerOffer {
    Supply { voltage: u16, max_watts: u32 },
    WithinLimit,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct PowerUse {
    voltage: u16,
    watts: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum GridCheckRule {
    CheckAcceptedBudget {
        offer_id: &'static str,
        max_watts: u32,
    },
}

struct GridAlgebra;

impl BodyAlgebra for GridAlgebra {
    type Offer = PowerOffer;
    type Use = PowerUse;
    type Overlap = u32;
    fn overlap(&self, o: &PowerOffer, u: &PowerUse) -> Option<u32> {
        let PowerOffer::Supply { voltage, max_watts } = o else {
            return None;
        };
        if *voltage != u.voltage {
            return None;
        }
        (u.watts <= *max_watts).then_some(u.watts)
    }
}

impl DeriveAlgebra<&'static str, &'static str, GridCheckRule> for GridAlgebra {
    fn may_overlap(
        &self,
        _offer: SpecRef<'_, PowerOffer, GridCheckRule>,
        _use_: SpecRef<'_, PowerUse, GridCheckRule>,
    ) -> bool {
        false
    }

    fn derive_offer(
        &self,
        rule: &GridCheckRule,
        obs: &LocalView<'_, &'static str, &'static str, Self>,
    ) -> Option<PowerOffer> {
        let GridCheckRule::CheckAcceptedBudget {
            offer_id,
            max_watts,
        } = rule;
        let used: u32 = obs.accepted(*offer_id).map(|e| e.overlap).sum();
        (used <= *max_watts).then_some(PowerOffer::WithinLimit)
    }
}

fn build_microgrid() -> PromiseSystem<&'static str, &'static str, GridAlgebra, GridCheckRule> {
    let mut sys = PromiseSystem::with_rules(GridAlgebra);
    sys.add_promise(Promise::offer(
        "grid:mains",
        "grid",
        AgentSet::All,
        PowerOffer::Supply {
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
            PowerOffer::Supply {
                voltage: 230,
                max_watts: 1500,
            },
        )
        .when(!Cond::assisted("bat:sense_grid")),
    );
    // Passive capacity monitor expressed natively in Stratum 1 via `+f(obs)` (no external law!):
    sys.add_promise(Promise::derive_offer(
        "bat:within_limit",
        "battery",
        AgentSet::All,
        [Obs::accepted("bat:backup")],
        GridCheckRule::CheckAcceptedBudget {
            offer_id: "bat:backup",
            max_watts: 1500,
        },
    ));
    sys.add_promise(Promise::accept(
        "hosp:draw",
        "hospital",
        AgentSet::of(["grid", "battery"]),
        PowerUse {
            voltage: 230,
            watts: 1000,
        },
    ));
    // Unique-provider check expressed natively via pure `Cond` (exactly 1 active provider):
    sys.add_promise(
        Promise::offer(
            "hosp:unique_source",
            "hospital",
            AgentSet::All,
            PowerOffer::WithinLimit,
        )
        .when(Cond::all(vec![
            Cond::assisted_quorum("hosp:draw", 1),
            !Cond::assisted_quorum("hosp:draw", 2),
        ])),
    );
    sys
}

#[test]
fn domain_microgrid_stratified_failover_self_assessment_and_native_monitors() {
    let mut sys = build_microgrid();

    // Normal operation: mains kept -> battery backup stays off; hospital has exactly 1 source.
    let r_normal = sys.resolve_optimistic().expect("stratified");
    assert!(r_normal.is_quenched("grid:mains"));
    assert!(!r_normal.is_quenched("bat:backup"));
    assert!(r_normal.is_quenched("hosp:unique_source"));
    assert_eq!(
        r_normal.offer("bat:within_limit"),
        Some(&PowerOffer::WithinLimit)
    );

    // Consistent self-assessment: if battery's own sensor `bat:sense_grid` fails,
    // `Assisted("bat:sense_grid")` becomes false and failover triggers!
    let r_sensor_fail = sys
        .resolve(|obs, p| !(*obs == "battery" && *p == "bat:sense_grid"))
        .expect("stratified");
    assert!(r_sensor_fail.is_quenched("bat:backup"));

    // Outage: mains broken -> battery backup quenches; 1000W <= 1500W stays within limit.
    let r_outage = sys.resolve(|_, p| *p != "grid:mains").expect("stratified");
    assert!(r_outage.is_quenched("bat:backup"));
    assert!(r_outage.is_quenched("hosp:unique_source"));
    assert_eq!(
        r_outage.offer("bat:within_limit"),
        Some(&PowerOffer::WithinLimit)
    );
    assert!(
        r_outage
            .bindings
            .iter()
            .any(|b| b.offer_id == "bat:backup" && b.consumer == "hospital" && b.overlap == 1000)
    );

    // Add 800W factory load -> native Stratum-1 monitor `bat:within_limit` trips (`None`)!
    sys.add_promise(
        Promise::accept(
            "fact:draw",
            "factory",
            AgentSet::of(["grid", "battery"]),
            PowerUse {
                voltage: 230,
                watts: 800,
            },
        )
        .with_scope(AgentSet::All),
    );
    let r_overload = sys.resolve(|_, p| *p != "grid:mains").expect("stratified");
    assert!(!r_overload.is_quenched("bat:within_limit"));

    // Observer-local split blackout: battery sees grid down while hospital & factory see grid up;
    // hospital now sees 2 providers (grid + battery), so `hosp:unique_source` unquenches!
    let r_split = sys
        .resolve(|obs, p| !(*obs == "battery" && *p == "grid:mains"))
        .expect("stratified");
    assert!(r_split.is_quenched("bat:backup"));
    assert!(!r_split.is_quenched("hosp:unique_source"));
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
    Ack(u32),
    DrawNotice(u32),
    Diesel,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum AllocUse {
    AcceptReq,
    AcceptAck,
    ObserveNotice,
    Draw { min: u32, max: u32 },
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum AllocRule {
    PriorityGrant { recipient: &'static str },
    ProportionalGrant { recipient: &'static str },
    PeerResidualUse { pool_cap: u32, max_wanted: u32 },
    ResidualReq { total_wanted: u32 },
    GrantAck { use_id: &'static str },
}

struct AllocAlg;

impl BodyAlgebra for AllocAlg {
    type Offer = AllocOffer;
    type Use = AllocUse;
    type Overlap = u32;
    fn overlap(&self, o: &AllocOffer, u: &AllocUse) -> Option<u32> {
        match (o, u) {
            (AllocOffer::Req { watts, .. }, AllocUse::AcceptReq)
            | (AllocOffer::Ack(watts), AllocUse::AcceptAck)
            | (AllocOffer::DrawNotice(watts), AllocUse::ObserveNotice) => Some(*watts),
            (AllocOffer::Grant(w), AllocUse::Draw { min, max }) if w >= min => Some((*w).min(*max)),
            _ => None,
        }
    }
}

impl DeriveAlgebra<&'static str, &'static str, AllocRule> for AllocAlg {
    fn may_overlap(
        &self,
        offer: SpecRef<'_, AllocOffer, AllocRule>,
        use_: SpecRef<'_, AllocUse, AllocRule>,
    ) -> bool {
        matches!(
            (offer, use_),
            (
                SpecRef::Derived(
                    AllocRule::PriorityGrant { .. } | AllocRule::ProportionalGrant { .. }
                ),
                SpecRef::Fixed(AllocUse::Draw { .. })
                    | SpecRef::Derived(AllocRule::PeerResidualUse { .. })
            ) | (
                SpecRef::Fixed(AllocOffer::Grant(_)),
                SpecRef::Derived(AllocRule::PeerResidualUse { .. })
            ) | (
                SpecRef::Derived(AllocRule::ResidualReq { .. }),
                SpecRef::Fixed(AllocUse::AcceptReq)
            ) | (
                SpecRef::Derived(AllocRule::GrantAck { .. }),
                SpecRef::Fixed(AllocUse::AcceptAck)
            )
        )
    }

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
            AllocRule::GrantAck { use_id } => {
                let got: u32 = obs.assisted(*use_id).map(|e| e.overlap).sum();
                (got > 0).then_some(AllocOffer::Ack(got))
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

fn add_alloc_consumers(sys: &mut PromiseSystem<&'static str, &'static str, AllocAlg, AllocRule>) {
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
    // Multi-protocol round-trip: clinic sends a derived `Ack` back to `bank`!
    // Without `may_overlap`, `clinic:ack -> bank:recv -> bank:grant_clinic -> clinic:draw -> clinic:ack`
    // would be falsely flagged as an `UnstratifiableCycle`!
    sys.add_promise(Promise::derive_offer(
        "clinic:ack",
        "clinic",
        AgentSet::single("bank"),
        [Obs::assisted("clinic:draw")],
        AllocRule::GrantAck {
            use_id: "clinic:draw",
        },
    ));
    sys.add_promise(Promise::derive_offer(
        "clinic:req_aux",
        "clinic",
        AgentSet::single("aux"),
        [Obs::assisted("clinic:draw")],
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
    sys.add_promise(Promise::accept(
        "bank:recv_ack",
        "bank",
        AgentSet::of(["hosp", "clinic"]),
        AllocUse::AcceptAck,
    ));
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
    // Intentionally pass duplicate `Obs::assisted("bank:recv")` to prove `BTreeSet` deduplicates!
    let bank_obs = [
        Obs::assisted("bank:recv"),
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
    add_alloc_consumers(&mut sys);
    Ok(sys)
}

#[test]
fn domain_value_derived_provider_allocation_and_channel_sharpness() {
    let mut sys = build_alloc_bank_system().expect("acyclic");

    // Round-trip `clinic:req -> bank:recv -> bank:grant_clinic -> clinic:draw -> clinic:ack -> bank:recv_ack`
    // stratifies cleanly thanks to `may_overlap` AND never double-counts duplicate `Obs`!
    let r = sys
        .resolve(|obs, p| !(*obs == "bank" && *p == "c1:p"))
        .expect("stratified without spurious cycle");
    assert_eq!(r.offer("bank:grant_hosp"), Some(&AllocOffer::Grant(1000)));
    assert_eq!(r.offer("bank:grant_clinic"), Some(&AllocOffer::Grant(500)));
    assert_eq!(r.offer("clinic:ack"), Some(&AllocOffer::Ack(500)));
    assert_eq!(
        r.offer("clinic:req_aux"),
        Some(&AllocOffer::Req {
            watts: 300,
            prio: 1
        })
    );
    assert!(!r.is_quenched("clinic:diesel"));
    let total_bank_grants: u32 = r
        .bindings
        .iter()
        .filter(|b| b.promiser == "bank")
        .map(|b| b.overlap)
        .sum();
    assert_eq!(total_bank_grants, 1500);

    // Strict clinic (min 800W) rejects 500W -> diesel fires; solo clinic gets 800W -> diesel off.
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

    // Proportional allocation strategy over the exact same Request -> Grant pattern.
    let bank_obs = [
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
        [Obs::assisted("clinic:watch_hosp")],
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
        [Obs::self_promise("b")],
        AllocRule::ResidualReq { total_wanted: 10 },
    ));
    cyc.add_promise(Promise::derive_offer(
        "b",
        "x",
        AgentSet::All,
        [Obs::self_promise("a")],
        AllocRule::ResidualReq { total_wanted: 10 },
    ));
    assert!(matches!(
        cyc.resolve_optimistic(),
        Err(EvalError::UnstratifiableCycle(_))
    ));
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum RaftCap {
    ReplicaVote,
    LinearizableKv,
    AppReady,
}

struct RaftAlg;

impl BodyAlgebra for RaftAlg {
    type Offer = RaftCap;
    type Use = RaftCap;
    type Overlap = RaftCap;
    fn overlap(&self, o: &RaftCap, u: &RaftCap) -> Option<RaftCap> {
        (o == u).then(|| o.clone())
    }
}

fn build_nested_raft_system()
-> Result<PromiseSystem<&'static str, &'static str, RaftAlg>, HierarchyError<&'static str>> {
    let mut sys = PromiseSystem::new(RaftAlg);
    // 3-level nested hierarchy: `dc` (transparent) -> `raft` (OPAQUE) -> `{n1, n2, n3}`
    sys.add_superagent("dc", false);
    sys.add_superagent("raft", true);
    sys.contain("dc", "raft")?;
    for n in ["n1", "n2", "n3"] {
        sys.contain("raft", n)?;
        sys.add_promise(Promise::offer(n, n, AgentSet::All, RaftCap::ReplicaVote));
    }
    sys.add_promise(
        Promise::offer("raft:kv", "raft", AgentSet::All, RaftCap::LinearizableKv).when(
            Cond::at_least(
                2,
                vec![
                    Cond::interior("n1"),
                    Cond::interior("n2"),
                    Cond::interior("n3"),
                ],
            ),
        ),
    );
    sys.add_promise(
        Promise::offer("dc:surface_ok", "dc", AgentSet::All, RaftCap::AppReady)
            .when(Cond::interior("raft:kv")),
    );
    sys.add_promise(
        Promise::offer("dc:pierce_inner", "dc", AgentSet::All, RaftCap::AppReady)
            .when(Cond::interior("n1")),
    );
    sys.add_promise(Promise::offer(
        "client:local_clock",
        "client",
        AgentSet::All,
        RaftCap::AppReady,
    ));
    sys.add_promise(Promise::accept(
        "client:use_kv",
        "client",
        AgentSet::single("raft"),
        RaftCap::LinearizableKv,
    ));
    sys.add_promise(Promise::accept(
        "client:pierce_n1",
        "client",
        AgentSet::single("n1"),
        RaftCap::ReplicaVote,
    ));
    sys.add_promise(
        Promise::offer("client:app", "client", AgentSet::All, RaftCap::AppReady)
            .when(Cond::assisted("client:use_kv")),
    );
    Ok(sys)
}

#[test]
fn domain_raft_opaque_superagent_nested_event_horizon_and_reparent_guard() {
    let mut sys = build_nested_raft_system().expect("acyclic");

    // Idempotent contain succeeds; silent reparenting & cycles are rejected by construction!
    assert!(sys.contain("raft", "n1").is_ok());
    assert_eq!(
        sys.contain("dc", "n1"),
        Err(HierarchyError::AlreadyContained {
            child: "n1",
            existing_parent: "raft",
            attempted_parent: "dc",
        })
    );
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

    // `lint()` explicitly flags `dc:pierce_inner` as `OpaqueWallBlocked`!
    assert!(sys.lint().iter().any(|w| matches!(
        w,
        ConditionWarning::OpaqueWallBlocked {
            promise: "dc:pierce_inner",
            referenced: "n1",
            superagent: "dc",
            target_promiser: "n1",
        }
    )));

    let r3 = sys.resolve_optimistic().expect("stratified");
    assert!(r3.is_quenched("raft:kv"));
    assert!(r3.is_quenched("dc:surface_ok"));
    assert!(!r3.is_quenched("dc:pierce_inner"));
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

    // Event-Horizon Vertex-Cut: `n1` has NO direct `+LeadsTo` edge into `dc:pierce_inner`,
    // and every path from `n1` to `client:app` passes through `raft:kv`.
    let sst = project_sst(&sys);
    let pierce_cone = sst.reverse_causal_cone(&SstNode::Promise("dc:pierce_inner"));
    assert!(!pierce_cone.contains(&SstNode::Promise("n1")));
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

#[derive(Clone, Debug, PartialEq, Eq)]
enum CloudRule {
    ExclusiveLease { tenant: &'static str, port: u16 },
    InteriorUseCount { use_id: &'static str },
}

impl DeriveAlgebra<&'static str, &'static str, CloudRule> for CloudAlg {
    fn may_overlap(
        &self,
        offer: SpecRef<'_, CloudSvc, CloudRule>,
        use_: SpecRef<'_, CloudSvc, CloudRule>,
    ) -> bool {
        matches!(
            (offer, use_),
            (
                SpecRef::Derived(CloudRule::ExclusiveLease { .. }),
                SpecRef::Fixed(CloudSvc::Slot { .. })
            )
        )
    }

    fn derive_offer(
        &self,
        rule: &CloudRule,
        obs: &LocalView<'_, &'static str, &'static str, Self>,
    ) -> Option<CloudSvc> {
        match rule {
            CloudRule::ExclusiveLease { tenant, port } => {
                let mut winners: Vec<(&'static str, u8)> = obs
                    .assisted("h1:recv_reqs")
                    .filter_map(|e| match e.overlap {
                        (Some(p), Some(ver)) if p == *port => Some((*e.promiser, ver)),
                        _ => None,
                    })
                    .collect();
                winners.sort_by_key(|(a, _)| *a);
                let (first, proto_ver) = winners.first().copied()?;
                (first == *tenant).then_some(CloudSvc::Slot {
                    port: *port,
                    proto_ver,
                })
            }
            CloudRule::InteriorUseCount { use_id } => {
                // Exercises symmetric `LocalView::interior_use`!
                obs.interior_use(*use_id).map(|_| CloudSvc::Power)
            }
        }
    }
}

#[test]
fn domain_tenancy_exclusive_port_leasing_protocol_alignment_and_interior_use() {
    let mut sys = PromiseSystem::with_rules(CloudAlg);
    sys.add_superagent("host1", false);
    sys.contain("host1", "tenant1").expect("acyclic");
    sys.contain("host1", "tenant2").expect("acyclic");
    sys.contain("host1", "tenant_v3").expect("acyclic");

    sys.add_promise(
        Promise::accept("h1:accept_terms", "host1", AgentSet::All, CloudSvc::Terms)
            .with_scope(AgentSet::All),
    );
    sys.add_promise(
        Promise::accept(
            "h1:recv_reqs",
            "host1",
            AgentSet::of(["tenant1", "tenant2", "tenant_v3"]),
            CloudSvc::Slot {
                port: 80,
                proto_ver: 2,
            },
        )
        .with_scope(AgentSet::All),
    );
    for (t, req, use_id, lease) in [
        ("tenant1", "t1:req", "t1:use", "h1:lease_t1"),
        ("tenant2", "t2:req", "t2:use", "h1:lease_t2"),
    ] {
        sys.add_promise(Promise::offer(
            req,
            t,
            AgentSet::single("host1"),
            CloudSvc::Slot {
                port: 80,
                proto_ver: 2,
            },
        ));
        sys.add_promise(Promise::accept(
            use_id,
            t,
            AgentSet::single("host1"),
            CloudSvc::Slot {
                port: 80,
                proto_ver: 2,
            },
        ));
        sys.add_promise(
            Promise::derive_offer(
                lease,
                "host1",
                AgentSet::single(t),
                [Obs::assisted("h1:recv_reqs")],
                CloudRule::ExclusiveLease {
                    tenant: t,
                    port: 80,
                },
            )
            .when(Cond::assisted("h1:accept_terms")),
        );
    }
    // Protocol version mismatch (`proto_ver: 3`) is rejected directly by `BodyAlgebra::overlap`.
    sys.add_promise(Promise::offer(
        "t3:req",
        "tenant_v3",
        AgentSet::single("host1"),
        CloudSvc::Slot {
            port: 80,
            proto_ver: 3,
        },
    ));
    sys.add_promise(Promise::offer(
        "t1:terms",
        "tenant1",
        AgentSet::single("host1"),
        CloudSvc::Terms,
    ));
    sys.add_promise(
        Promise::offer("h1:power", "host1", AgentSet::All, CloudSvc::Power)
            .when(Cond::accepted("h1:lease_t1")),
    );
    sys.add_promise(Promise::derive_offer(
        "h1:sees_t1_use",
        "host1",
        AgentSet::All,
        [Obs::interior("t1:use")],
        CloudRule::InteriorUseCount { use_id: "t1:use" },
    ));

    let r = sys.resolve_optimistic().expect("stratified");
    assert_eq!(
        r.offer("h1:lease_t1"),
        Some(&CloudSvc::Slot {
            port: 80,
            proto_ver: 2
        })
    );
    assert_eq!(r.offer("h1:lease_t2"), None);
    assert!(r.is_quenched("h1:power"));
    assert!(r.body("h1:power").is_some());
    assert_eq!(r.offer("h1:sees_t1_use"), Some(&CloudSvc::Power));
    assert!(!r.bindings.iter().any(|b| b.offer_id == "t3:req"));
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
fn static_lint_overwrites_null_potent_unknown_targets_and_nested_negation() {
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
            Cond::at_least(3, vec![Cond::self_promise("y:lonely")]),
        ])),
    );
    let diagnostics = lint_sys.lint();
    assert!(diagnostics.iter().any(|w| matches!(
        w,
        ConditionWarning::UnknownTargetAgent {
            promise: "y:lonely",
            target: "ghost",
        }
    )));
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
            referenced: Some("y:lonely"),
            required: 1,
            max_possible: 0,
            ..
        }
    )));
    assert!(diagnostics.iter().any(|w| matches!(
        w,
        ConditionWarning::UnsatisfiableMinCount {
            referenced: None,
            required: 3,
            max_possible: 1,
            ..
        }
    )));
}

#[test]
fn strict_gamma_3_4_invariants_dual_links_kind_filtered_sources_and_coarse_graining() {
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
    // Unregistered start nodes return an empty cone (never hallucinate `{unknown}`).
    assert!(g.forward_causal_cone(&"typo_node").is_empty());

    // Strict γ(3,4) kind filtering: `LeadsTo` sources/sinks include ONLY `Event` nodes!
    assert_eq!(g.sources(LinkKind::LeadsTo), BTreeSet::from(["flight"]));
    assert_eq!(g.sinks(LinkKind::LeadsTo), BTreeSet::from(["landing"]));
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
