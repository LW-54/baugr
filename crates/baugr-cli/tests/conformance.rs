//! Golden Conformance Test Suite for `baugr` CLI (`ERG-L0`, `ERG-L2`, Cedar, SST, JSON Schema).

#![allow(unused_crate_dependencies, clippy::expect_used, clippy::unwrap_used)]

use std::path::PathBuf;
use std::process::Command;

use serde_json::Value;

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crates dir")
        .parent()
        .expect("workspace root")
        .to_path_buf()
}

fn baugr_bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_baugr"))
}

fn run_baugr(root_rel: &str, args: &[&str]) -> std::process::Output {
    let root = workspace_root().join(root_rel);
    Command::new(baugr_bin())
        .arg("--root")
        .arg(root)
        .args(args)
        .output()
        .expect("failed to execute baugr binary")
}

#[test]
fn smart_grid_example_passes_every_command() {
    let chk = run_baugr("examples/smart-grid", &["check", "--json"]);
    assert!(
        chk.status.success(),
        "smart-grid check failed: {}",
        String::from_utf8_lossy(&chk.stderr)
    );
    let report: Value = serde_json::from_slice(&chk.stdout).unwrap();
    assert_eq!(report["schema_errors"].as_array().unwrap().len(), 0);
    assert!(
        report["superagents"]["substation"]["tree_valid"]
            .as_bool()
            .unwrap()
    );
    assert!(
        report["superagents"]["microgrid"]["tree_valid"]
            .as_bool()
            .unwrap()
    );

    // Cedar explain: substation allowed, auditor forbidden
    let allow = run_baugr(
        "examples/smart-grid",
        &[
            "explain",
            "substation",
            "trip-breaker",
            "trip-critical",
            "--json",
        ],
    );
    assert!(allow.status.success());
    let allow_json: Value = serde_json::from_slice(&allow.stdout).unwrap();
    assert_eq!(allow_json["decision"], "allow");

    let deny = run_baugr(
        "examples/smart-grid",
        &[
            "explain",
            "auditor",
            "trip-breaker",
            "trip-critical",
            "--json",
        ],
    );
    assert!(!deny.status.success());
    let deny_json: Value = serde_json::from_slice(&deny.stdout).unwrap();
    assert_eq!(deny_json["decision"], "deny");

    // SST impact cone for battery-bank must include dependent loads and SCADA
    let graph = run_baugr(
        "examples/smart-grid",
        &["graph", "--impact", "battery-bank", "--json"],
    );
    assert!(graph.status.success());
    let graph_json: Value = serde_json::from_slice(&graph.stdout).unwrap();
    let cone: Vec<&str> = graph_json["impactCone"]
        .as_array()
        .unwrap()
        .iter()
        .filter_map(Value::as_str)
        .collect();
    assert!(
        cone.contains(&"hospital-load"),
        "missing hospital-load in {cone:?}"
    );
    assert!(
        cone.contains(&"ev-charger"),
        "missing ev-charger in {cone:?}"
    );
    assert!(
        cone.contains(&"scada-monitor"),
        "missing scada-monitor in {cone:?}"
    );
    assert!(graph_json["schemas"]["promises"]["power:kw"].is_object());

    // Deterministic resolve & desugar
    let resolved = run_baugr("examples/smart-grid", &["resolve", "microgrid"]);
    assert!(resolved.status.success());
    let resolved_json: Value = serde_json::from_slice(&resolved.stdout).unwrap();
    assert_eq!(
        resolved_json["bound_by_instance"]["auditor"]["grid:summary"]["region"],
        "north"
    );
    assert_eq!(
        resolved_json["bound_by_instance"]["substation/hospital-load"]["grid:voltage"]["volts"],
        400
    );

    let desugared = run_baugr(
        "examples/smart-grid",
        &["desugar", "--agent", "hospital-load"],
    );
    assert!(desugared.status.success());
    let des_json: Value = serde_json::from_slice(&desugared.stdout).unwrap();
    assert_eq!(des_json["id"], "hospital-load");
    assert_eq!(des_json["promises"].as_array().unwrap().len(), 3);

    // JSON Schema Draft 2020-12 export for all 4 kinds
    for kind in ["agent", "profile", "policy", "schema"] {
        let out = run_baugr("examples/smart-grid", &["schema-json", "--kind", kind]);
        assert!(out.status.success(), "schema-json {kind} failed");
        let schema: Value = serde_json::from_slice(&out.stdout).unwrap();
        assert_eq!(
            schema["$schema"],
            "https://json-schema.org/draft/2020-12/schema"
        );
        if kind == "agent" {
            assert!(schema["properties"]["offer"]["properties"]["power:kw"].is_object());
        }
    }
}

#[test]
fn valid_golden_fixtures_pass_and_resolve_deterministically() {
    let raw = run_baugr("fixtures/valid/minimal-raw", &["check"]);
    assert!(raw.status.success());

    let multi = run_baugr("fixtures/valid/erg-l2-multi-instance", &["check"]);
    assert!(
        multi.status.success(),
        "erg-l2-multi-instance failed: {}",
        String::from_utf8_lossy(&multi.stderr)
    );

    let resolved = run_baugr("fixtures/valid/erg-l2-multi-instance", &["resolve", "root"]);
    assert!(resolved.status.success());
    let val: Value = serde_json::from_slice(&resolved.stdout).unwrap();
    assert_eq!(val["bound_by_instance"]["w1"]["cfg:slot"]["label"], "alpha");
    assert_eq!(val["bound_by_instance"]["w2"]["cfg:slot"]["label"], "beta");
    assert_eq!(
        val["bound_by_instance"]["collector-a"]["keep-only"]["w1:item"]["channel"],
        "events"
    );
    assert_eq!(
        val["bound_by_instance"]["collector-b"]["sync-only"]["w2:item"]["channel"],
        "events"
    );
}

#[test]
fn all_ten_invalid_golden_fixtures_fail_with_exact_diagnostics() {
    let cases = [
        ("fixtures/invalid/duplicate-exclusive", "DuplicateOffer"),
        (
            "fixtures/invalid/unhandled-broadcast",
            "UnhandledBroadcastOffer",
        ),
        ("fixtures/invalid/budget-exceeded", "BudgetExceeded"),
        (
            "fixtures/invalid/invariant-violation",
            "inv-no-conflict-tags",
        ),
        (
            "fixtures/invalid/superagent-auth-denied",
            "UnauthorizedPromise",
        ),
        ("fixtures/invalid/atomic-auth-denied", "UnauthorizedPromise"),
        (
            "fixtures/invalid/unknown-ptype-strict",
            "UnknownPromiseType",
        ),
        (
            "fixtures/invalid/missing-required-payload",
            "MissingRequiredField",
        ),
        ("fixtures/invalid/bad-payload-type", "InvalidFieldType"),
        ("fixtures/invalid/containment-cycle", "cycle:"),
    ];

    for (fixture, expected_token) in cases {
        let out = run_baugr(fixture, &["check", "--json"]);
        assert!(
            !out.status.success(),
            "expected failure for negative fixture {fixture}"
        );
        let stdout = String::from_utf8_lossy(&out.stdout);
        assert!(
            stdout.contains(expected_token),
            "fixture {fixture} did not report `{expected_token}`; got:
{stdout}"
        );
    }
}
