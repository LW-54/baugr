//! Domain-agnostic integration tests and purity guards for `baugr` v0.2.

use std::collections::BTreeSet;
use std::fs;
use std::path::Path;

use baugr::{
    AgentSet, AgreementInScope, Binding, BodyAlgebra, CoarseGrainError, Cond, DisjointInScope,
    EvalError, LinkKind, MaxOne, NodeKind, Promise, PromiseSystem, QuorumLaw, ResolutionView,
    ResourceMonoid, SstError, SstGraph, SstNode, SymmetricMeet, Unbounded, UniqueProviderLaw,
    ValencyLaw, directory_of, project_sst,
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
fn domain_microgrid_stratified_failover_and_monoidal_valency() {
    let mut sys = build_microgrid();

    // Normal operation: mains kept -> battery backup stays off; hospital uniquely uses grid.
    let r_normal = sys.resolve_optimistic().expect("stratified");
    assert!(r_normal.quenched.contains("grid:mains"));
    assert!(!r_normal.quenched.contains("bat:backup"));
    assert!(
        ResolutionView::new(&sys, &r_normal)
            .check(&UniqueProviderLaw {
                use_id: "hosp:draw"
            })
            .is_ok()
    );

    // Outage: mains broken -> battery backup quenches; 1000W <= 1500W valency holds.
    let r_outage = sys.resolve(|_, p| *p != "grid:mains").expect("stratified");
    assert!(r_outage.quenched.contains("bat:backup"));
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

    // Add 800W factory load -> 1800W > 1500W valency deficit!
    sys.add_promise(Promise::accept(
        "fact:draw",
        "factory",
        AgentSet::of(["grid", "battery"]),
        PowerUse {
            voltage: 230,
            watts: 800,
        },
    ));
    let r_overload = sys.resolve(|_, p| *p != "grid:mains").expect("stratified");
    let err = ResolutionView::new(&sys, &r_overload)
        .check(&cap_law)
        .expect_err("expected valency deficit");
    assert_eq!(err.used, 1800);
    assert_eq!(err.capacity, 1500);

    // Observer-local split blackout: battery sees grid down while factory sees grid up.
    let r_split = sys
        .resolve(|obs, p| !(*obs == "battery" && *p == "grid:mains"))
        .expect("stratified");
    assert!(r_split.quenched.contains("bat:backup"));
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
        sys.contain("raft", n);
        sys.add_promise(Promise::offer(n, n, AgentSet::All, Cap::ReplicaVote));
    }
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

    // 3/3 healthy -> raft:kv & client:app quench; external piercing to n1 blocked!
    let r3 = sys.resolve_optimistic().expect("stratified");
    assert!(r3.quenched.contains("raft:kv"));
    assert!(r3.quenched.contains("client:app"));
    assert!(!r3.bindings.iter().any(|b| b.use_id == "client:pierce_n1"));

    // 1 node down -> 2/3 quorum still holds!
    let r2 = sys.resolve(|_, p| *p != "n3").expect("stratified");
    assert!(r2.quenched.contains("raft:kv"));
    assert!(r2.quenched.contains("client:app"));

    // 2 nodes down -> quorum lost, unrelated client:local_clock unaffected!
    let r1 = sys
        .resolve(|_, p| *p != "n2" && *p != "n3")
        .expect("stratified");
    assert!(!r1.quenched.contains("raft:kv"));
    assert!(!r1.quenched.contains("client:app"));
    assert!(r1.quenched.contains("client:local_clock"));

    // Directory π_directory(raft) exposes interior vs surface promises.
    let dir = directory_of(&sys, &"raft");
    assert!(dir.is_opaque);
    assert_eq!(dir.interior_agents, BTreeSet::from(["n1", "n2", "n3"]));
    assert_eq!(dir.interior_promises, BTreeSet::from(["n1", "n2", "n3"]));
    assert_eq!(dir.surface_promises, BTreeSet::from(["raft:kv"]));

    // Event-level reverse causal light cone J⁻(client:app) excludes unrelated client:local_clock!
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

#[test]
fn domain_tenancy_and_scoped_laws() {
    let mut sys = PromiseSystem::<&str, &str, _>::new(CloudAlg);
    // Two separate host superagents (transparent) so per-host port disjointness is scoped!
    sys.add_superagent("host1", false);
    sys.contain("host1", "tenant1");
    sys.add_superagent("host2", false);
    sys.contain("host2", "tenant2");

    // Exact Burgess Tenancy template on host1:
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
    // host2 also binds port 80 independently -> MUST NOT conflict with host1's scoped port law!
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

    let r = sys.resolve_optimistic().expect("stratified");
    assert!(r.quenched.contains("h1:slot_80"));
    assert!(r.quenched.contains("h1:power"));

    let view = ResolutionView::new(&sys, &r);
    let h1_port_law = DisjointInScope::new(
        AgentSet::Set(sys.members_of(&"host1")),
        |b: &Binding<&str, &str, (Option<u16>, Option<u8>)>| b.overlap.0,
    );
    assert!(view.check(&h1_port_law).is_ok());

    let ver_law = AgreementInScope::new(
        AgentSet::All,
        |b: &Binding<&str, &str, (Option<u16>, Option<u8>)>| b.overlap.1,
    );
    assert!(view.check(&ver_law).is_ok());
    assert!(
        view.check(&QuorumLaw {
            use_id: "t1:use_slot",
            min_providers: 1
        })
        .is_ok()
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
}

#[test]
fn domain_bidirectional_protocol_complete_info_and_cycles() {
    let mut sys = PromiseSystem::<&str, &str, _>::new(CloudAlg);
    // Bidirectional layered protocol A:net -> B:dns -> A:tls (zero false agent-level cycle!)
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

    // Positive circular self-dependency -> cleanly stays unquenched!
    sys.add_promise(
        Promise::offer("X:loop1", "X", AgentSet::All, CloudSvc::Net)
            .when(Cond::self_promise("X:loop2")),
    );
    sys.add_promise(
        Promise::offer("X:loop2", "X", AgentSet::All, CloudSvc::Net)
            .when(Cond::self_promise("X:loop1")),
    );

    let r = sys.resolve_optimistic().expect("stratified");
    assert!(r.quenched.contains("A:tls"));
    assert!(!r.quenched.contains("X:loop1"));
    assert!(!r.quenched.contains("X:loop2"));

    let warns = sys.check_complete_information();
    assert!(
        warns
            .iter()
            .any(|w| w.conditional_promise == "A:tls" && w.blind_target == "B")
    );

    // Negative cycle must be rejected cleanly.
    let mut bad = PromiseSystem::<&str, &str, _>::new(CloudAlg);
    bad.add_promise(
        Promise::offer("p", "z", AgentSet::All, CloudSvc::Net).when(!Cond::self_promise("q")),
    );
    bad.add_promise(
        Promise::offer("q", "z", AgentSet::All, CloudSvc::Net).when(!Cond::self_promise("p")),
    );
    assert!(matches!(
        bad.resolve_optimistic(),
        Err(EvalError::UnstratifiableNegativeCycle(_))
    ));
}

#[test]
fn strict_gamma_3_4_rules_and_coarse_graining() {
    let mut g = SstGraph::new();
    g.add_node("love", NodeKind::Concept);
    g.add_node("butterfly", NodeKind::Thing);
    g.add_node("wing", NodeKind::Thing);
    g.add_node("flight", NodeKind::Event);
    g.add_node("landing", NodeKind::Event);
    g.add_node("blue", NodeKind::Concept);

    // Burgess's famous forbidden metaphor: Love (Concept) NEAR Butterfly (Thing) -> REJECTED!
    assert!(matches!(
        g.add_edge("love", LinkKind::Near, "butterfly"),
        Err(SstError::DisallowedTransition { .. })
    ));
    // Thing cannot contain Event; Thing cannot be expressed; Thing cannot lead to Event!
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
    // Strict ADR-0018 A2: Event cannot Express Event directly (must target Concept)!
    assert!(
        g.add_edge("flight", LinkKind::Expresses, "landing")
            .is_err()
    );

    // Valid γ(3,4) edges:
    g.add_edge("flight", LinkKind::LeadsTo, "landing").unwrap();
    g.add_edge("flight", LinkKind::Contains, "butterfly")
        .unwrap();
    g.add_edge("butterfly", LinkKind::Contains, "wing").unwrap();
    g.add_edge("butterfly", LinkKind::Expresses, "blue")
        .unwrap();
    g.add_edge("wing", LinkKind::ContainedBy, "butterfly")
        .unwrap();

    assert_eq!(
        g.forward_causal_cone(&"flight"),
        BTreeSet::from(["flight", "landing"])
    );
    assert!(g.sources(LinkKind::LeadsTo).contains("flight"));
    assert!(g.sinks(LinkKind::LeadsTo).contains("landing"));

    // Kind-homogeneous coarse graining collapses butterfly+wing -> insect (Thing).
    let q = g
        .coarse_grain(|n| match *n {
            "butterfly" | "wing" => "insect",
            other => other,
        })
        .expect("homogeneous grain");
    assert_eq!(q.kind_of(&"insect"), Some(NodeKind::Thing));
    // Internal butterfly<->wing edge dropped; exterior flight->insect & insect->blue preserved!
    assert_eq!(q.axis_edges(LinkKind::Contains).count(), 1);
    assert_eq!(q.axis_edges(LinkKind::Expresses).count(), 1);

    // Inhomogeneous coarse grain (merging Event + Thing) cleanly rejected!
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
    let src_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    for entry in fs::read_dir(&src_dir).expect("read src dir") {
        let path = entry.expect("dir entry").path();
        if path.extension().and_then(|e| e.to_str()) == Some("rs") {
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
}
