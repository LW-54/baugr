//! Microgrid power failover, observer-local split blackout, and monoidal valency.
//!
//! Run with: `cargo run --example microgrid`

use baugr::{
    AgentSet, Binding, BodyAlgebra, Cond, Promise, PromiseSystem, ResolutionView, ValencyLaw,
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
    type Overlap = u32;

    fn overlap(&self, o: &PowerOffer, u: &PowerUse) -> Option<u32> {
        if o.voltage != u.voltage {
            return None;
        }
        (u.watts <= o.max_watts).then_some(u.watts)
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
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
    // Backup generator quenches iff mains is NOT kept (stratified negation).
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

    let normal = sys.resolve_optimistic()?;
    println!(
        "Normal:  quenched={:?}, backup_active={}",
        normal.quenched,
        normal.quenched.contains("bat:backup")
    );

    let outage = sys.resolve(|_, p| *p != "grid:mains")?;
    let valency = ValencyLaw {
        offer_id: "bat:backup",
        capacity: 1500_u32,
        weight: |b: &Binding<&str, &str, u32>| b.overlap,
    };
    ResolutionView::new(&sys, &outage).check(&valency)?;
    println!(
        "Outage:  backup active, hospital draws {}W <= 1500W capacity",
        outage
            .bindings
            .iter()
            .find(|b| b.offer_id == "bat:backup")
            .map_or(0, |b| b.overlap)
    );
    Ok(())
}
