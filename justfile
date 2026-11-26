# Baugr — thin zero-logic developer shortcuts (all real logic lives in `baugr`, `cargo`, and `lake`)

default:
    @just --list

# Fast Rust format, pedantic clippy, and full unit + golden conformance test suite
test:
    cargo fmt --all -- --check
    cargo clippy --workspace --all-targets -- --deny warnings
    cargo test --workspace

# Build Lean 4 specification + oracle and verify 0 sorryAx across all 54 theorems
lean:
    cd lean && lake build Baugr baugr-oracle && lake env lean Baugr/Audit.lean

# Run Differential Randomized Testing (Rust baugr-core vs Lean 4 baugr-oracle) on smart-grid
drt cases='500':
    cargo run -p baugr-cli -- --root examples/smart-grid drt --oracle lean/.lake/build/bin/baugr-oracle --cases {{cases}}

# Generate mdBook Markdown + Mermaid docs for the smart-grid example
doc out='/tmp/baugr-smart-grid-docs':
    cargo run -p baugr-cli -- --root examples/smart-grid graph --json | cargo run -p baugr-doc -- --out {{out}} --title "Smart Grid Architecture"

# Run full hermetic Nix flake verification suite
check:
    nix flake check -L

# Format Nix and Rust sources
fmt:
    cargo fmt --all
    alejandra flake.nix
