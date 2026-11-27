//! Multi-tenant cloud host tenancy with static upper-bound discharge (`static_upper_bound`),
//! simultaneous per-host port disjointness (`DisjointBy`), and fleet protocol agreement (`AgreementBy`).
//!
//! Run with: `cargo run --example tenancy`

use baugr::{AgentSet, BodyAlgebra, Cond, Promise, PromiseSystem, ResolutionView};

#[derive(Clone, Debug, PartialEq, Eq)]
enum Svc {
    Terms,
    Slot { port: u16, proto_ver: u8 },
    Power,
}

struct CloudAlg;

impl BodyAlgebra for CloudAlg {
    type Offer = Svc;
    type Use = Svc;
    type Overlap = (Option<u16>, Option<u8>);

    fn overlap(&self, o: &Svc, u: &Svc) -> Option<Self::Overlap> {
        match (o, u) {
            (Svc::Terms, Svc::Terms) | (Svc::Power, Svc::Power) => Some((None, None)),
            (
                Svc::Slot {
                    port: op,
                    proto_ver: ov,
                },
                Svc::Slot {
                    port: up,
                    proto_ver: uv,
                },
            ) if op == up && ov == uv => Some((Some(*op), Some(*ov))),
            _ => None,
        }
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut sys = PromiseSystem::new(CloudAlg);
    sys.add_superagent("host1", false);
    sys.contain("host1", "tenant1")?;
    sys.add_superagent("host2", false);
    sys.contain("host2", "tenant2")?;

    // Exact Burgess Tenancy pattern on host1:
    sys.add_promise(Promise::accept(
        "h1:accept_terms",
        "host1",
        AgentSet::All,
        Svc::Terms,
    ));
    sys.add_promise(
        Promise::offer(
            "h1:slot_80",
            "host1",
            AgentSet::All,
            Svc::Slot {
                port: 80,
                proto_ver: 2,
            },
        )
        .when(Cond::assisted("h1:accept_terms")),
    );
    sys.add_promise(
        Promise::offer("h1:power", "host1", AgentSet::All, Svc::Power)
            .when(Cond::accepted("h1:slot_80")),
    );
    sys.add_promise(Promise::offer(
        "t1:terms",
        "tenant1",
        AgentSet::single("host1"),
        Svc::Terms,
    ));
    sys.add_promise(Promise::accept(
        "t1:use_slot",
        "tenant1",
        AgentSet::single("host1"),
        Svc::Slot {
            port: 80,
            proto_ver: 2,
        },
    ));

    // host2 independently offers port 80 with protocol version 2.
    sys.add_promise(Promise::offer(
        "h2:slot_80",
        "host2",
        AgentSet::single("tenant2"),
        Svc::Slot {
            port: 80,
            proto_ver: 2,
        },
    ));
    sys.add_promise(Promise::accept(
        "t2:use_slot",
        "tenant2",
        AgentSet::single("host2"),
        Svc::Slot {
            port: 80,
            proto_ver: 2,
        },
    ));

    // Static upper-bound discharge (Lean theorem `static_discharge_universal`):
    // passing downward-closed laws on `B_max(S)` proves them for ALL runtime scenarios α!
    let upper = sys.static_upper_bound();
    let static_view = ResolutionView::new(&sys, &upper);
    static_view.check_disjoint(|sys, b| {
        let port = b.overlap.0?;
        let host = sys.parent_of(&b.consumer).copied().unwrap_or(b.promiser);
        Some((host, port))
    })?;
    static_view.check_agreement(|_, b| b.overlap.1.map(|ver| ((), ver)))?;

    let resolved = sys.resolve_optimistic()?;
    println!(
        "Tenancy statically discharged for all α: {} promises quenched, {} active bindings.",
        resolved.quenched_count(),
        resolved.bindings.len()
    );
    Ok(())
}
