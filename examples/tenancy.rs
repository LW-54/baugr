//! Multi-tenant cloud host tenancy (`arXiv:1505.01716v1` §4.1) using pure voluntary
//! promises and conditions (`Cond::assisted`, `Cond::accepted`, and `+f(obs) | C`):
//! host `host1` accepts tenant terms and port requests, grants each TCP port exclusively
//! to at most one tenant by construction (preventing collisions without external law
//! wrappers), and enables power only once a tenant actually accepts its granted lease.
//!
//! Run with: `cargo run --example tenancy`

use baugr::{
    AgentSet, BodyAlgebra, Cond, DeriveAlgebra, LocalView, Obs, Promise, PromiseSystem, SpecRef,
};

#[derive(Clone, Debug, PartialEq, Eq)]
enum SvcOffer {
    Terms,
    PortReq { port: u16, proto_ver: u8 },
    PortLease { port: u16, proto_ver: u8 },
    Power,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum SvcUse {
    AcceptTerms,
    AcceptPortReqs { required_proto: u8 },
    UseLease { port: u16, proto_ver: u8 },
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum HostRule {
    /// Grants each requested port exclusively to the lexicographically first tenant
    /// that meets the host's protocol requirement (no port collision possible).
    ExclusiveLease { tenant: &'static str, port: u16 },
}

struct CloudAlg;

impl BodyAlgebra for CloudAlg {
    type Offer = SvcOffer;
    type Use = SvcUse;
    type Overlap = Option<(u16, u8)>;

    fn overlap(&self, o: &SvcOffer, u: &SvcUse) -> Option<Self::Overlap> {
        match (o, u) {
            (SvcOffer::Terms, SvcUse::AcceptTerms) => Some(None),
            (SvcOffer::PortReq { port, proto_ver }, SvcUse::AcceptPortReqs { required_proto })
                if proto_ver == required_proto =>
            {
                Some(Some((*port, *proto_ver)))
            }
            (
                SvcOffer::PortLease {
                    port: op,
                    proto_ver: ov,
                },
                SvcUse::UseLease {
                    port: up,
                    proto_ver: uv,
                },
            ) if op == up && ov == uv => Some(Some((*op, *ov))),
            _ => None,
        }
    }
}

impl DeriveAlgebra<&'static str, &'static str, HostRule> for CloudAlg {
    fn may_overlap(
        &self,
        offer: SpecRef<'_, SvcOffer, HostRule>,
        use_: SpecRef<'_, SvcUse, HostRule>,
    ) -> bool {
        matches!(
            (offer, use_),
            (
                SpecRef::Derived(HostRule::ExclusiveLease { .. }),
                SpecRef::Fixed(SvcUse::UseLease { .. })
            )
        )
    }

    fn derive_offer(
        &self,
        rule: &HostRule,
        obs: &LocalView<'_, &'static str, &'static str, Self>,
    ) -> Option<SvcOffer> {
        let HostRule::ExclusiveLease { tenant, port } = rule;
        // Pick the deterministic unique winner requesting `port` on `h1:recv_ports`.
        let mut requesters: Vec<(&'static str, u8)> = obs
            .assisted("h1:recv_ports")
            .filter_map(|e| match e.overlap {
                Some((p, ver)) if p == *port => Some((*e.promiser, ver)),
                _ => None,
            })
            .collect();
        requesters.sort_by_key(|(agent, _)| *agent);
        let (winner, proto_ver) = requesters.first().copied()?;
        (winner == *tenant).then_some(SvcOffer::PortLease {
            port: *port,
            proto_ver,
        })
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut sys = PromiseSystem::with_rules(CloudAlg);
    sys.add_superagent("host1", false);
    sys.contain("host1", "tenant1")?;
    sys.contain("host1", "tenant2")?;

    // Host accepts tenant terms and port requests requiring protocol v2.
    sys.add_promise(
        Promise::accept(
            "h1:accept_terms",
            "host1",
            AgentSet::All,
            SvcUse::AcceptTerms,
        )
        .with_scope(AgentSet::All),
    );
    sys.add_promise(
        Promise::accept(
            "h1:recv_ports",
            "host1",
            AgentSet::of(["tenant1", "tenant2"]),
            SvcUse::AcceptPortReqs { required_proto: 2 },
        )
        .with_scope(AgentSet::All),
    );

    // Both tenants voluntarily request port 80; host1 grants port 80 exclusively to one winner!
    for (t, req_id, use_id, lease_id) in [
        ("tenant1", "t1:req_80", "t1:use_80", "h1:lease_t1"),
        ("tenant2", "t2:req_80", "t2:use_80", "h1:lease_t2"),
    ] {
        sys.add_promise(Promise::offer(
            req_id,
            t,
            AgentSet::single("host1"),
            SvcOffer::PortReq {
                port: 80,
                proto_ver: 2,
            },
        ));
        sys.add_promise(Promise::accept(
            use_id,
            t,
            AgentSet::single("host1"),
            SvcUse::UseLease {
                port: 80,
                proto_ver: 2,
            },
        ));
        sys.add_promise(
            Promise::derive_offer(
                lease_id,
                "host1",
                AgentSet::single(t),
                [Obs::assisted("h1:recv_ports")],
                HostRule::ExclusiveLease {
                    tenant: t,
                    port: 80,
                },
            )
            .when(Cond::assisted("h1:accept_terms")),
        );
    }

    // Tenant1 signs terms; host powers up only once its granted lease is actually accepted.
    sys.add_promise(Promise::offer(
        "t1:terms",
        "tenant1",
        AgentSet::single("host1"),
        SvcOffer::Terms,
    ));
    sys.add_promise(
        Promise::offer("h1:power", "host1", AgentSet::All, SvcOffer::Power)
            .when(Cond::accepted("h1:lease_t1")),
    );

    let resolved = sys.resolve_optimistic()?;
    println!(
        "Exclusive tenancy resolved: lease_t1={:?}, lease_t2={:?}, power_on={}",
        resolved.offer("h1:lease_t1"),
        resolved.offer("h1:lease_t2"),
        resolved.is_quenched("h1:power"),
    );
    Ok(())
}
