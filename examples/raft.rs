//! Opaque Raft consensus superagent with irreducible 2-of-3 quorum emergence
//! and Semantic Spacetime reverse light cone analysis.
//!
//! Run with: `cargo run --example raft`

use baugr::{
    AgentSet, Cond, Promise, PromiseSystem, SstNode, SymmetricMeet, directory_of, project_sst,
};

#[derive(Clone, Debug, PartialEq, Eq)]
enum Cap {
    Vote,
    LinearizableKv,
    AppReady,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let alg = SymmetricMeet::new(|o: &Cap, u: &Cap| (o == u).then(|| o.clone()));
    let mut sys = PromiseSystem::new(alg);

    sys.add_superagent("raft", true);
    for replica in ["n1", "n2", "n3"] {
        sys.contain("raft", replica)?;
        sys.add_promise(Promise::offer(replica, replica, AgentSet::All, Cap::Vote));
    }

    // Irreducible emergent superagent promise: requires >= 2 of 3 interior replicas.
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
    sys.add_promise(Promise::accept(
        "client:use_kv",
        "client",
        AgentSet::single("raft"),
        Cap::LinearizableKv,
    ));
    sys.add_promise(
        Promise::offer("client:app", "client", AgentSet::All, Cap::AppReady)
            .when(Cond::assisted("client:use_kv")),
    );

    let healthy = sys.resolve(|_, p| *p != "n3")?;
    let degraded = sys.resolve(|_, p| *p != "n2" && *p != "n3")?;
    println!(
        "2/3 replicas up -> app ready: {}",
        healthy.is_quenched("client:app")
    );
    println!(
        "1/3 replicas up -> app ready: {}",
        degraded.is_quenched("client:app")
    );

    let dir = directory_of(&sys, &"raft");
    let sst = project_sst(&sys);
    let cone = sst.reverse_causal_cone(&SstNode::Promise("client:app"));
    println!("Superagent directory: {dir:?}");
    println!("Reverse causal cone J⁻(client:app): {cone:?}");
    Ok(())
}
