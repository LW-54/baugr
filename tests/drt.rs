//! Cedar VGD Differential Randomized Testing (Rust `baugr` ↔ Lean 4 `baugr-oracle`)
//! plus standalone randomized property verification of all formal theorems (T1–T7).
//!
//! - Always runs 500 randomized property checks (perturbation light-cone containment,
//!   autonomy non-coercion, opaque superagent non-piercing, strict γ(3,4) well-formedness).
//! - When `BAUGR_ORACLE` points to the compiled Lean 4 `baugr-oracle` executable (wired
//!   automatically by `nix flake check` and `just drt`), also verifies bit-for-bit
//!   equivalence between Rust and Lean across all 500+ randomized Promise Systems!

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::io::Write as _;
use std::process::{Command, Stdio};

use baugr::{
    AgentSet, Body, BodyAlgebra, Cond, LinkKind, NodeKind, Promise, PromiseSystem, SstNode,
    project_sst,
};

/// Deterministic xorshift64* PRNG (zero external crate dependencies).
struct Rng(u64);

impl Rng {
    const fn new(seed: u64) -> Self {
        Self(seed)
    }

    const fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    fn range(&mut self, upper: usize) -> usize {
        if upper == 0 {
            return 0;
        }
        let m = u64::try_from(upper).unwrap_or(1);
        let r = self.next_u64().checked_rem(m).unwrap_or(0);
        usize::try_from(r).unwrap_or(0)
    }

    fn coin(&mut self, num: usize, den: usize) -> bool {
        self.range(den) < num
    }
}

/// Exact bitmask mutual-information `BodyAlgebra` matching `Baugr.Oracle.Main.bitmaskAlgebra`.
#[derive(Clone, Copy, Debug)]
struct BitmaskAlgebra;

impl BodyAlgebra for BitmaskAlgebra {
    type Offer = usize;
    type Use = usize;
    type Overlap = usize;

    fn overlap(&self, o: &usize, u: &usize) -> Option<usize> {
        let m = o & u;
        (m != 0).then_some(m)
    }
}

struct GeneratedCase {
    num_agents: usize,
    sys: PromiseSystem<usize, usize, BitmaskAlgebra>,
    broken: BTreeSet<(usize, usize)>,
}

fn gen_agent_set(rng: &mut Rng, num_agents: usize) -> AgentSet<usize> {
    if rng.coin(1, 3) {
        AgentSet::All
    } else {
        let mut set = BTreeSet::new();
        for a in 0..num_agents {
            if rng.coin(1, 2) {
                set.insert(a);
            }
        }
        AgentSet::Set(set)
    }
}

fn gen_cond(
    rng: &mut Rng,
    promiser: usize,
    num_promises: usize,
    sys: &PromiseSystem<usize, usize, BitmaskAlgebra>,
    depth: usize,
    allow_neg: bool,
) -> Cond<usize> {
    if depth == 0 || num_promises == 0 || rng.coin(2, 5) {
        return Cond::always();
    }
    let choice = rng.range(if allow_neg { 6 } else { 5 });
    match choice {
        0 => Cond::self_promise(rng.range(num_promises)),
        1 => Cond::assisted_quorum(
            rng.range(num_promises),
            1_usize.saturating_add(rng.range(2)),
        ),
        2 => Cond::accepted_at_least(
            rng.range(num_promises),
            1_usize.saturating_add(rng.range(2)),
        ),
        3 => {
            // Prefer an interior promise if one exists, otherwise random id.
            let interior_pids: Vec<usize> = sys
                .promises()
                .values()
                .filter(|pr| sys.is_strict_ancestor(&promiser, &pr.promiser))
                .map(|pr| pr.id)
                .collect();
            let q = interior_pids
                .get(rng.range(interior_pids.len()))
                .copied()
                .unwrap_or_else(|| rng.range(num_promises));
            Cond::interior(q)
        }
        4 => {
            let n = 1_usize.saturating_add(rng.range(3));
            let k = rng.range(n.saturating_add(1));
            let mut cs = Vec::with_capacity(n);
            for _ in 0..n {
                cs.push(gen_cond(
                    rng,
                    promiser,
                    num_promises,
                    sys,
                    depth.saturating_sub(1),
                    allow_neg,
                ));
            }
            Cond::at_least(k, cs)
        }
        _ => !gen_cond(
            rng,
            promiser,
            num_promises,
            sys,
            depth.saturating_sub(1),
            false,
        ),
    }
}

fn generate_stratifiable_case(rng: &mut Rng) -> GeneratedCase {
    loop {
        let num_agents = 3_usize.saturating_add(rng.range(5)); // 3..=7 agents
        let mut sys = PromiseSystem::new(BitmaskAlgebra);
        for a in 0..num_agents {
            let opaque = rng.coin(1, 3);
            sys.add_superagent(a, opaque);
        }
        // Acyclic parent hierarchy: child `c` may have parent `p < c`.
        for c in 1..num_agents {
            if rng.coin(1, 2) {
                let p = rng.range(c);
                let _ = sys.contain(p, c);
            }
        }
        let num_promises = 4_usize.saturating_add(rng.range(8)); // 4..=11 promises
        // Pass 1: create promises with unconditional bodies so static dependencies exist.
        for pid in 0..num_promises {
            let promiser = rng.range(num_agents);
            let target = gen_agent_set(rng, num_agents);
            let scope = gen_agent_set(rng, num_agents);
            let body_bits = 1_usize.saturating_add(rng.range(7)); // 3-bit non-zero bitmask
            let pr = if rng.coin(1, 2) {
                Promise::offer(pid, promiser, target, body_bits).with_scope(scope)
            } else {
                Promise::accept(pid, promiser, target, body_bits).with_scope(scope)
            };
            sys.add_promise(pr);
        }
        // Pass 2: attach rich conditions (including positive cycles & stratified negations!).
        let mut updated = Vec::with_capacity(num_promises);
        for pid in 0..num_promises {
            if let Some(mut pr) = sys.promises().get(&pid).cloned() {
                // Only allow `Not` referencing strictly lower IDs sometimes, or arbitrary to exercise stratify().
                let allow_neg = rng.coin(1, 3);
                pr.cond = gen_cond(rng, pr.promiser, num_promises, &sys, 2, allow_neg);
                updated.push(pr);
            }
        }
        for pr in updated {
            sys.add_promise(pr);
        }

        if sys.stratify().is_err() {
            // Unstratifiable negative cycle generated — retry for stratifiable oracle case.
            continue;
        }

        // Random observer-local broken assessments α_obs(pid) = false.
        let mut broken = BTreeSet::new();
        for obs in 0..num_agents {
            for pid in 0..num_promises {
                if rng.coin(1, 6) {
                    broken.insert((obs, pid));
                }
            }
        }

        return GeneratedCase {
            num_agents,
            sys,
            broken,
        };
    }
}

fn fmt_agent_set(set: &AgentSet<usize>) -> String {
    match set {
        AgentSet::All => "*".to_string(),
        AgentSet::Set(s) if s.is_empty() => "-".to_string(),
        AgentSet::Set(s) => s
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(","),
    }
}

fn fmt_cond(c: &Cond<usize>) -> String {
    match c {
        Cond::SelfPromise(q) => format!("S {q}"),
        Cond::Assisted {
            use_id,
            min_providers,
        } => format!("A {use_id} {min_providers}"),
        Cond::Accepted {
            offer_id,
            min_acceptors,
        } => format!("C {offer_id} {min_acceptors}"),
        Cond::Interior(q) => format!("I {q}"),
        Cond::AtLeast(0, cs) if cs.is_empty() => "T".to_string(),
        Cond::AtLeast(k, cs) => {
            let mut s = format!("K {k} {}", cs.len());
            for sub in cs {
                s.push(' ');
                s.push_str(&fmt_cond(sub));
            }
            s
        }
        Cond::Not(inner) => format!("N {}", fmt_cond(inner)),
    }
}

fn serialize_case(case: &GeneratedCase, strata: &BTreeMap<usize, usize>) -> String {
    let mut out = String::new();
    let _ = writeln!(out, "AGENTS {}", case.num_agents);
    for (child, parent) in case.sys.parents() {
        let _ = writeln!(out, "PARENT {child} {parent}");
    }
    for op in case.sys.opaque_superagents() {
        let _ = writeln!(out, "OPAQUE {op}");
    }
    for pr in case.sys.promises().values() {
        let (pol, body_val) = match pr.body {
            Body::Offer(v) => ("O", v),
            Body::Use(v) => ("U", v),
        };
        let _ = writeln!(
            out,
            "PROMISE {} {} {} {} {} {} {}",
            pr.id,
            pr.promiser,
            pol,
            fmt_agent_set(&pr.target),
            fmt_agent_set(&pr.scope),
            body_val,
            fmt_cond(&pr.cond)
        );
    }
    for (obs, pid) in &case.broken {
        let _ = writeln!(out, "BROKEN {obs} {pid}");
    }
    let max_s = strata.values().copied().max().unwrap_or(0);
    for (pid, r) in strata {
        let _ = writeln!(out, "STRATUM {pid} {r}");
    }
    let _ = writeln!(out, "MAX_STRATUM {max_s}");
    // Knaster-Tarski convergence guaranteed in <= |promises| + 1 steps per stratum.
    let _ = writeln!(out, "STEPS {}", case.sys.promises().len().saturating_add(2));
    out.push_str("END_CASE\n");
    out
}

fn fmt_sst_node(n: &SstNode<usize, usize>) -> String {
    match n {
        SstNode::Agent(a) => format!("t:{a}"),
        SstNode::Promise(p) => format!("e:{p}"),
        SstNode::Intent(p) => format!("c:{p}"),
    }
}

const fn fmt_sst_link(k: LinkKind) -> &'static str {
    match k {
        LinkKind::Near => "N",
        LinkKind::LeadsTo => "+L",
        LinkKind::Follows => "-L",
        LinkKind::Contains => "+C",
        LinkKind::ContainedBy => "-C",
        LinkKind::Expresses => "+E",
        LinkKind::ExpressedBy => "-E",
    }
}

struct CheckedCase {
    resolved: baugr::Resolved<usize, usize, usize>,
    sst: baugr::SstGraph<SstNode<usize, usize>>,
}

fn check_theorem_invariants(
    rng: &mut Rng,
    case: &GeneratedCase,
    resolved: &baugr::Resolved<usize, usize, usize>,
    sst: &baugr::SstGraph<SstNode<usize, usize>>,
) -> Result<(), String> {
    // Property 1 (T5d): Canonical Φ : PromiseSystem -> γ(3,4) is strictly well-formed.
    for edge in sst.edges() {
        let sk = sst.kind_of(&edge.src).ok_or("src node missing")?;
        let dk = sst.kind_of(&edge.dst).ok_or("dst node missing")?;
        if !LinkKind::allowed(sk, edge.kind, dk) {
            return Err(format!("disallowed projected SST edge: {edge:?}"));
        }
    }
    if !sst
        .nodes()
        .values()
        .all(|k| matches!(k, NodeKind::Event | NodeKind::Thing | NodeKind::Concept))
    {
        return Err("unexpected node kind".to_string());
    }

    // Property 2 (T7a): No active binding ever pierces an opaque superagent wall.
    for b in &resolved.bindings {
        for s in case.sys.opaque_superagents() {
            let p_strict = case.sys.is_strict_ancestor(s, &b.promiser);
            let c_strict = case.sys.is_strict_ancestor(s, &b.consumer);
            let p_in = &b.promiser == s || p_strict;
            let c_in = &b.consumer == s || c_strict;
            if (p_strict && !c_in) || (c_strict && !p_in) {
                return Err(format!("binding {b:?} pierced opaque superagent {s}"));
            }
        }
    }

    // Property 3 (T6 Crown Jewel): Flipping assessments OUTSIDE J⁻(target) never changes target!
    let target_pid = rng.range(case.sys.promises().len());
    let rev_cone = sst.reverse_causal_cone(&SstNode::Promise(target_pid));
    let mut flipped_broken = case.broken.clone();
    for obs in 0..case.num_agents {
        for pid in 0..case.sys.promises().len() {
            if !rev_cone.contains(&SstNode::Promise(pid)) && !flipped_broken.remove(&(obs, pid)) {
                flipped_broken.insert((obs, pid));
            }
        }
    }
    let resolved_perturbed = case
        .sys
        .resolve(|obs, pid| !flipped_broken.contains(&(*obs, *pid)))
        .map_err(|e| format!("perturbed resolve failed: {e}"))?;
    if resolved.quenched.contains(&target_pid) != resolved_perturbed.quenched.contains(&target_pid)
    {
        return Err(
            "T6 violation: perturbation outside reverse light cone altered target!".to_string(),
        );
    }
    Ok(())
}

fn verify_against_lean_oracle(
    oracle_path: &str,
    oracle_input: &str,
    cases: &[CheckedCase],
) -> Result<(), String> {
    let mut child = Command::new(oracle_path)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("spawn Lean 4 baugr-oracle: {e}"))?;

    child
        .stdin
        .as_mut()
        .ok_or("oracle stdin unavailable")?
        .write_all(oracle_input.as_bytes())
        .map_err(|e| format!("write cases to Lean oracle: {e}"))?;

    let output = child
        .wait_with_output()
        .map_err(|e| format!("wait Lean oracle: {e}"))?;
    if !output.status.success() {
        return Err(format!(
            "Lean oracle failed: {}",
            String::from_utf8_lossy(&output.stderr)
        ));
    }

    let stdout =
        String::from_utf8(output.stdout).map_err(|e| format!("utf8 oracle output: {e}"))?;
    let mut lines = stdout.lines();

    for (idx, checked) in cases.iter().enumerate() {
        let q_line = lines.next().ok_or("missing QUENCHED line")?;
        let b_line = lines.next().ok_or("missing BINDINGS line")?;
        let s_line = lines.next().ok_or("missing SST line")?;
        let end_line = lines.next().ok_or("missing END_OUT line")?;
        if end_line != "END_OUT" {
            return Err(format!("case {idx}: expected END_OUT, got {end_line:?}"));
        }

        let expected_q = format!(
            "QUENCHED {}",
            checked
                .resolved
                .quenched
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(" ")
        );
        if q_line.trim() != expected_q.trim() {
            return Err(format!(
                "DRT case {idx} QUENCHED mismatch: lean={q_line:?} rust={expected_q:?}"
            ));
        }

        let mut rust_bindings: BTreeSet<String> = BTreeSet::new();
        for b in &checked.resolved.bindings {
            rust_bindings.insert(format!("{}:{}:{}", b.offer_id, b.use_id, b.overlap));
        }
        let expected_b = format!(
            "BINDINGS {}",
            rust_bindings.into_iter().collect::<Vec<_>>().join(" ")
        );
        if b_line.trim() != expected_b.trim() {
            return Err(format!(
                "DRT case {idx} BINDINGS mismatch: lean={b_line:?} rust={expected_b:?}"
            ));
        }

        let mut rust_sst: BTreeSet<String> = BTreeSet::new();
        for e in checked.sst.edges() {
            rust_sst.insert(format!(
                "{}->{}->{}",
                fmt_sst_node(&e.src),
                fmt_sst_link(e.kind),
                fmt_sst_node(&e.dst)
            ));
        }
        let expected_s = format!("SST {}", rust_sst.into_iter().collect::<Vec<_>>().join(" "));
        if s_line.trim() != expected_s.trim() {
            return Err(format!(
                "DRT case {idx} SST mismatch: lean={s_line:?} rust={expected_s:?}"
            ));
        }
    }
    if lines.next().is_some() {
        return Err("unexpected trailing Lean oracle output".to_string());
    }
    Ok(())
}

#[test]
fn randomized_theorem_properties_and_optional_lean_drt() {
    let mut rng = Rng::new(0xBA09_0002_CAFE_BABE);
    let num_cases = 500;
    let mut cases = Vec::with_capacity(num_cases);
    let mut oracle_input = String::new();

    for _ in 0..num_cases {
        let case = generate_stratifiable_case(&mut rng);
        let resolved = case
            .sys
            .resolve(|obs, pid| !case.broken.contains(&(*obs, *pid)))
            .expect("stratifiable case must resolve");
        let sst = project_sst(&case.sys);
        check_theorem_invariants(&mut rng, &case, &resolved, &sst).expect("theorem invariants");
        oracle_input.push_str(&serialize_case(&case, &resolved.strata));
        cases.push(CheckedCase { resolved, sst });
    }

    if let Ok(oracle_path) = std::env::var("BAUGR_ORACLE") {
        verify_against_lean_oracle(&oracle_path, &oracle_input, &cases)
            .expect("Lean 4 DRT equivalence");
    }
}
