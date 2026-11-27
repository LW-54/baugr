//! Microgrid failover with an opaque 2-of-3 battery-bank superagent, observer-local
//! split blackout, blocked piercing, `Accepted` audit trigger, light cones, directory,
//! and collective `ScopeLaw` checks (`valency` + `agreement`).
//!
//! Run with: `cargo run --example microgrid`

use baugr::{
    AgentSet, BodyAlgebra, Cond, HierarchyError, Promise, PromiseSystem, ResolutionView, SstNode,
    directory_of, project_sst,
};

#[derive(Clone, Debug)]
struct PowerOffer {
    voltage: u16,
    max_watts: u32,
}

#[derive(Clone, Debug)]
struct PowerUse {
    voltage: u16,
    watts: u32,
}

struct GridAlgebra;

impl BodyAlgebra for GridAlgebra {
    type Offer = PowerOffer;
    type Use = PowerUse;
    type Overlap = (u16, u32); // agreed (voltage, allocated_watts)

    fn overlap(&self, o: &PowerOffer, u: &PowerUse) -> Option<Self::Overlap> {
        if o.voltage != u.voltage {
            return None;
        }
        (u.watts <= o.max_watts).then_some((o.voltage, u.watts))
    }
}

fn build_microgrid()
-> Result<PromiseSystem<&'static str, &'static str, GridAlgebra>, HierarchyError<&'static str>> {
    let mut sys = PromiseSystem::new(GridAlgebra);

    // 1. Opaque superagent `bank` encapsulating three internal battery cells.
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
            PowerOffer {
                voltage: 230,
                max_watts: 800,
            },
        ));
    }

    // 2. Municipal mains + site-visible grid sensing (target != visibility scope).
    sys.add_promise(Promise::offer(
        "grid:mains",
        "grid",
        AgentSet::All,
        PowerOffer {
            voltage: 230,
            max_watts: 5000,
        },
    ));
    sys.add_promise(
        Promise::accept(
            "bank:sense",
            "bank",
            AgentSet::single("grid"),
            PowerUse {
                voltage: 230,
                watts: 0,
            },
        )
        .with_scope(AgentSet::All),
    );

    // 3. Irreducible emergent failover offer on `bank`'s surface:
    //    quenches iff mains sensing fails AND >= 2 of 3 interior cells are healthy.
    sys.add_promise(
        Promise::offer(
            "bank:backup",
            "bank",
            AgentSet::All,
            PowerOffer {
                voltage: 230,
                max_watts: 1500,
            },
        )
        .when(Cond::all(vec![
            !Cond::assisted("bank:sense"),
            Cond::at_least(
                2,
                vec![
                    Cond::interior("cell1:chg"),
                    Cond::interior("cell2:chg"),
                    Cond::interior("cell3:chg"),
                ],
            ),
        ])),
    );

    // 4. Voluntary acceptance trigger: activates only once someone accepts `bank:backup`.
    sys.add_promise(
        Promise::offer(
            "bank:audit",
            "bank",
            AgentSet::All,
            PowerOffer {
                voltage: 230,
                max_watts: 0,
            },
        )
        .when(Cond::accepted("bank:backup")),
    );

    // 5. Hospital draws 1000W from {grid, bank}; piercing `cell1` directly is blocked!
    sys.add_promise(Promise::accept(
        "hosp:draw",
        "hospital",
        AgentSet::of(["grid", "bank"]),
        PowerUse {
            voltage: 230,
            watts: 1000,
        },
    ));
    sys.add_promise(Promise::accept(
        "hosp:pierce",
        "hospital",
        AgentSet::single("cell1"),
        PowerUse {
            voltage: 230,
            watts: 500,
        },
    ));

    Ok(sys)
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let sys = build_microgrid()?;
    let warnings = sys.lint();
    if !warnings.is_empty() {
        return Err(format!("unexpected lint warnings: {warnings:?}").into());
    }

    // Healthy mains: backup & audit stay idle; piercing cell1 is blocked by opaque wall.
    let healthy = sys.resolve_optimistic()?;
    let healthy_pierced = healthy.bindings.iter().any(|b| b.use_id == "hosp:pierce");

    // Local blackout at `bank` + internal `cell1` crash (2-of-3 quorum survives!).
    let outage =
        sys.resolve(|obs, p| !(*obs == "bank" && matches!(*p, "grid:mains" | "cell1:chg")))?;
    let outage_pierced = outage.bindings.iter().any(|b| b.use_id == "hosp:pierce");

    // Collective laws: 1500W monoidal valency + 230V site-wide agreement C(b).
    let view = ResolutionView::new(&sys, &outage);
    view.check_valency("bank:backup", 1500_u32, |b| b.overlap.1)?;
    view.check_agreement(|_, b| Some(("site-bus", b.overlap.0)))?;

    // Semantic Spacetime γ(3,4) reverse light cone & superagent directory.
    let sst = project_sst(&sys);
    let cone = sst.reverse_causal_cone(&SstNode::Promise("bank:backup"));
    let dir = directory_of(&sys, &"bank");

    println!(
        "Healthy: backup_active={}, pierce_blocked={}",
        healthy.quenched.contains("bank:backup"),
        !healthy_pierced,
    );
    println!(
        "Outage:  backup_active={}, audit_active={}, pierce_blocked={}, J^-(backup)={} nodes, bank dir={} interior/{} surface",
        outage.quenched.contains("bank:backup"),
        outage.quenched.contains("bank:audit"),
        !outage_pierced,
        cone.len(),
        dir.interior_promises.len(),
        dir.surface_promises.len(),
    );
    Ok(())
}
