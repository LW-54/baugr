# Baugr — thin zero-logic developer shortcuts (all real logic lives in `cargo`, `lake`, `typst`, and `nix`)

default:
    @just --list

# Rust format, pedantic clippy, rustdoc, unit/domain/property tests, and doctests
test:
    cargo fmt -- --check
    cargo clippy --all-targets -- --deny warnings
    RUSTDOCFLAGS="--deny warnings" cargo doc --no-deps
    cargo test

# Build Lean 4 formal proofs + oracle and verify 0 sorryAx across all 29 audited theorems
lean:
    cd lean && lake build Baugr baugr-oracle && lake env lean Baugr/Audit.lean

# Run 500-case Rust ↔ Lean 4 Differential Randomized Testing (Cedar VGD)
drt: lean
    BAUGR_ORACLE=lean/.lake/build/bin/baugr-oracle cargo test --test drt

# Compile formal Typst specification paper to paper/baugr.pdf
paper:
    typst compile paper/baugr.typ paper/baugr.pdf

# Run full hermetic Nix flake verification suite (7 checks)
check:
    nix flake check -L

# Format Rust and Nix sources
fmt:
    cargo fmt
    alejandra flake.nix
