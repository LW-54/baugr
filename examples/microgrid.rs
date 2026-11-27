//! Microgrid failover with an opaque 2-of-3 battery-bank superagent, emergent
//! interior-cell capacity, symmetric value-derived promises (`+f(obs) | C` on the
//! provider and `-f(obs)` on the consumer) with channel-sharp `may_overlap`,
//! autonomous consumer handling (partial take + dynamic residual draw from `aux`
//! vs. all-or-nothing local diesel failover), blocked piercing, causal light cones,
//! and superagent directory.
//!
//! Run with: `cargo run --example microgrid`

use baugr::{
    AgentSet, Body, BodyAlgebra, Cond, DeriveAlgebra, HierarchyError, LocalView, Obs, Promise,
    PromiseSystem, SpecRef, SstNode, directory_of, project_sst,
};

#[derive(Clone, Debug, PartialEq, Eq)]
enum GridOffer {
    CellPower { watts: u32 },
    Request { watts: u32, priority: u8 },
    Power { voltage: u16, watts: u32 },
    LocalDiesel { watts: u32 },
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum GridUse {
    AcceptRequests,
    DrawPower {
        voltage: u16,
        min_watts: u32,
        max_watts: u32,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum GridOverlap {
    Requested { watts: u32, priority: u8 },
    Supplied { voltage: u16, watts: u32 },
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum GridRule {
    /// Provider-side `+f(obs) | C`: computes emergent wattage from healthy interior cells,
    /// sorts accepted requests by priority, and grants `recipient` its exact share.
    PriorityGrant { recipient: &'static str },
    /// Consumer-side `-f(obs)`: computes exact residual draw (`total_wanted - received`)
    /// from secondary supplier `aux`, or stays inactive (`None`) when already satisfied.
    ResidualDraw {
        primary_use: &'static str,
        total_wanted: u32,
    },
}

struct GridAlgebra;

impl BodyAlgebra for GridAlgebra {
    type Offer = GridOffer;
    type Use = GridUse;
    type Overlap = GridOverlap;

    fn overlap(&self, o: &GridOffer, u: &GridUse) -> Option<Self::Overlap> {
        match (o, u) {
            (GridOffer::Request { watts, priority }, GridUse::AcceptRequests) => {
                Some(GridOverlap::Requested {
                    watts: *watts,
                    priority: *priority,
                })
            }
            (
                GridOffer::Power { voltage, watts },
                GridUse::DrawPower {
                    voltage: uv,
                    min_watts,
                    max_watts,
                },
            ) if voltage == uv && *watts >= *min_watts => Some(GridOverlap::Supplied {
                voltage: *voltage,
                watts: (*watts).min(*max_watts),
            }),
            _ => None,
        }
    }
}

impl DeriveAlgebra<&'static str, &'static str, GridRule> for GridAlgebra {
    fn may_overlap(
        &self,
        offer: SpecRef<'_, GridOffer, GridRule>,
        use_: SpecRef<'_, GridUse, GridRule>,
    ) -> bool {
        matches!(
            (offer, use_),
            (
                SpecRef::Derived(GridRule::PriorityGrant { .. }),
                SpecRef::Fixed(GridUse::DrawPower { .. })
            ) | (
                SpecRef::Fixed(GridOffer::Power { .. }),
                SpecRef::Derived(GridRule::ResidualDraw { .. })
            )
        )
    }

    fn derive_offer(
        &self,
        rule: &GridRule,
        obs: &LocalView<'_, &'static str, &'static str, Self>,
    ) -> Option<GridOffer> {
        let GridRule::PriorityGrant { recipient } = rule else {
            return None;
        };
        // Emergent capacity = sum of healthy interior cells (1600W with 2/3, 2400W with 3/3).
        let mut total_cap: u32 = 0;
        for (_, _, body) in obs.interior_entries() {
            if let Body::Offer(GridOffer::CellPower { watts }) = body {
                total_cap = total_cap.saturating_add(*watts);
            }
        }
        // Gather active voluntary requests and allocate in deterministic priority order.
        let mut reqs: Vec<(u8, &'static str, u32)> = obs
            .assisted("bank:recv_req")
            .filter_map(|e| match e.overlap {
                GridOverlap::Requested { watts, priority } => Some((priority, *e.promiser, watts)),
                GridOverlap::Supplied { .. } => None,
            })
            .collect();
        reqs.sort_by_key(|(prio, agent, _)| (*prio, *agent));

        let mut remaining = total_cap;
        for (_, agent, wanted) in reqs {
            let granted = wanted.min(remaining);
            remaining = remaining.saturating_sub(granted);
            if agent == *recipient {
                return (granted > 0).then_some(GridOffer::Power {
                    voltage: 230,
                    watts: granted,
                });
            }
        }
        None
    }

    fn derive_use(
        &self,
        rule: &GridRule,
        obs: &LocalView<'_, &'static str, &'static str, Self>,
    ) -> Option<GridUse> {
        let GridRule::ResidualDraw {
            primary_use,
            total_wanted,
        } = rule
        else {
            return None;
        };
        let mut received: u32 = 0;
        for e in obs.assisted(*primary_use) {
            if let GridOverlap::Supplied { watts, .. } = e.overlap {
                received = received.saturating_add(watts);
            }
        }
        let deficit = total_wanted.saturating_sub(received);
        (deficit > 0).then_some(GridUse::DrawPower {
            voltage: 230,
            min_watts: deficit,
            max_watts: deficit,
        })
    }
}

type MicrogridSystem = PromiseSystem<&'static str, &'static str, GridAlgebra, GridRule>;

fn add_battery_bank(sys: &mut MicrogridSystem) -> Result<(), HierarchyError<&'static str>> {
    // 1. Opaque superagent `bank` encapsulating three 800W internal battery cells.
    sys.add_superagent("bank", true);
    for (cell, pid) in [
        ("cell1", "cell1:chg"),
        ("cell2", "cell2:chg"),
        ("cell3", "cell3:chg"),
    ] {
        sys.contain("bank", cell)?;
        sys.add_promise(Promise::offer(
            pid,
            cell,
            AgentSet::All,
            GridOffer::CellPower { watts: 800 },
        ));
    }

    // 2. Municipal mains + secondary `aux` supply + site-visible sensing & request intake.
    sys.add_promise(Promise::offer(
        "grid:mains",
        "grid",
        AgentSet::All,
        GridOffer::Power {
            voltage: 230,
            watts: 5000,
        },
    ));
    sys.add_promise(Promise::offer(
        "aux:power",
        "aux",
        AgentSet::single("clinic"),
        GridOffer::Power {
            voltage: 230,
            watts: 500,
        },
    ));
    sys.add_promise(
        Promise::accept(
            "bank:sense",
            "bank",
            AgentSet::single("grid"),
            GridUse::DrawPower {
                voltage: 230,
                min_watts: 0,
                max_watts: 0,
            },
        )
        .with_scope(AgentSet::All),
    );
    sys.add_promise(
        Promise::accept(
            "bank:recv_req",
            "bank",
            AgentSet::of(["hospital", "clinic"]),
            GridUse::AcceptRequests,
        )
        .with_scope(AgentSet::All),
    );

    // 3. Provider-side `+f(obs) | C`: emergent failover grants bounded by healthy cells!
    let failover_cond = Cond::all(vec![
        !Cond::assisted("bank:sense"),
        Cond::at_least(
            2,
            vec![
                Cond::interior("cell1:chg"),
                Cond::interior("cell2:chg"),
                Cond::interior("cell3:chg"),
            ],
        ),
    ]);
    let bank_obs = [
        Obs::assisted("bank:recv_req"),
        Obs::interior("cell1:chg"),
        Obs::interior("cell2:chg"),
        Obs::interior("cell3:chg"),
    ];
    for (pid, recipient) in [
        ("bank:grant_hosp", "hospital"),
        ("bank:grant_clinic", "clinic"),
    ] {
        sys.add_promise(
            Promise::derive_offer(
                pid,
                "bank",
                AgentSet::single(recipient),
                bank_obs.clone(),
                GridRule::PriorityGrant { recipient },
            )
            .when(failover_cond.clone()),
        );
    }
    Ok(())
}

fn add_consumers(sys: &mut MicrogridSystem, clinic_min_watts: u32) {
    // 4. Consumers voluntarily state their demand & priority to `bank`.
    sys.add_promise(Promise::offer(
        "hosp:req",
        "hospital",
        AgentSet::single("bank"),
        GridOffer::Request {
            watts: 1000,
            priority: 1,
        },
    ));
    sys.add_promise(Promise::offer(
        "clinic:req",
        "clinic",
        AgentSet::single("bank"),
        GridOffer::Request {
            watts: 800,
            priority: 2,
        },
    ));

    // 5. Consumers freely decide how to handle received offers:
    //    - hospital draws 1000W from {grid, bank}; piercing `cell1` directly is blocked!
    //    - clinic draws from `bank` with its own autonomous `min_watts`;
    //      if partially satisfied, consumer-side `-f(obs)` (`derive_use`) dynamically draws
    //      the exact leftover shortfall from `aux`; if denied, `!Cond::assisted` fires diesel!
    sys.add_promise(Promise::accept(
        "hosp:draw",
        "hospital",
        AgentSet::of(["grid", "bank"]),
        GridUse::DrawPower {
            voltage: 230,
            min_watts: 1000,
            max_watts: 1000,
        },
    ));
    sys.add_promise(Promise::accept(
        "hosp:pierce",
        "hospital",
        AgentSet::single("cell1"),
        GridUse::DrawPower {
            voltage: 230,
            min_watts: 1,
            max_watts: 500,
        },
    ));
    sys.add_promise(
        Promise::accept(
            "clinic:draw",
            "clinic",
            AgentSet::single("bank"),
            GridUse::DrawPower {
                voltage: 230,
                min_watts: clinic_min_watts,
                max_watts: 800,
            },
        )
        .with_scope(AgentSet::All),
    );
    sys.add_promise(
        Promise::offer(
            "clinic:diesel",
            "clinic",
            AgentSet::single("clinic"),
            GridOffer::LocalDiesel { watts: 800 },
        )
        .when(!Cond::assisted("clinic:draw")),
    );
    // Consumer-side `-f(obs) | C`: only draws the exact deficit from `aux` when partially served.
    sys.add_promise(
        Promise::derive_use(
            "clinic:draw_aux",
            "clinic",
            AgentSet::single("aux"),
            [Obs::assisted("clinic:draw")],
            GridRule::ResidualDraw {
                primary_use: "clinic:draw",
                total_wanted: 800,
            },
        )
        .when(Cond::assisted("clinic:draw")),
    );
}

fn build_microgrid(clinic_min_watts: u32) -> Result<MicrogridSystem, HierarchyError<&'static str>> {
    let mut sys = PromiseSystem::with_rules(GridAlgebra);
    add_battery_bank(&mut sys)?;
    add_consumers(&mut sys, clinic_min_watts);
    Ok(sys)
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Mode A: Partial clinic (`min_watts = 1`) binds `bank`'s 600W leftover and derives a
    // `-f(obs)` residual draw (`200W`) from `aux`, reaching its full 800W without overdraw!
    let partial_sys = build_microgrid(1)?;
    let warnings = partial_sys.lint();
    if !warnings.is_empty() {
        return Err(format!("unexpected lint warnings: {warnings:?}").into());
    }

    // Outage: mains down at `bank` + `cell1` crashed -> 2 healthy cells = 1600W emergent cap!
    let blackout =
        |obs: &&str, p: &&str| !(*obs == "bank" && matches!(*p, "grid:mains" | "cell1:chg"));
    let partial = partial_sys.resolve(blackout)?;
    let pierce_blocked = !partial.bindings.iter().any(|b| b.use_id == "hosp:pierce");

    // Mode B: Strict all-or-nothing clinic (`min_watts = 800`):
    // - With hospital active, clinic's 600W grant < 800W -> rejected -> local diesel activates!
    // - With hospital offline, bank offers clinic the full 800W -> clinic binds, `draw_aux` stays
    //   `None` (0W deficit), and diesel stays idle!
    let strict_sys = build_microgrid(800)?;
    let strict_shared = strict_sys.resolve(blackout)?;
    let strict_solo =
        strict_sys.resolve(|obs, p| blackout(obs, p) && !(*obs == "bank" && *p == "hosp:req"))?;

    let sst = project_sst(&partial_sys);
    let cone = sst.reverse_causal_cone(&SstNode::Promise("clinic:draw_aux"));
    let dir = directory_of(&partial_sys, &"bank");

    println!(
        "Partial outage (2/3 cells = 1600W): hosp={:?}, clinic={:?}, aux_draw={:?}, pierce_blocked={pierce_blocked}",
        partial.offer("bank:grant_hosp"),
        partial.offer("bank:grant_clinic"),
        partial.use_body("clinic:draw_aux"),
    );
    println!(
        "Strict clinic (min 800W): shared(600W)->diesel={}, solo(800W)->diesel={}, solo_aux={:?}",
        strict_shared.is_quenched("clinic:diesel"),
        strict_solo.is_quenched("clinic:diesel"),
        strict_solo.use_body("clinic:draw_aux"),
    );
    println!(
        "Spacetime & Superagent: J^-(clinic:draw_aux)={} nodes, bank dir={} interior/{} surface",
        cone.len(),
        dir.interior_promises.len(),
        dir.surface_promises.len(),
    );
    Ok(())
}
