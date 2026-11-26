//! **Baugr (`baugr-core`)** — Pure, `std::fs`-free (Wasm-ready), 100% usage-agnostic
//! Promise Theory & Semantic Spacetime verification kernel.
//!
//! Mirrors the Lean 4 specification (`lean/Baugr/{Theory,Engine}/*`) module-for-module
//! with zero Nix, Linux, or domain assumptions and stays bit-for-bit locked to `baugr-oracle`
//! via AWS Cedar Verification-Guided Development (DRT).

pub mod agency;
pub mod attr_expr;
pub mod authority;
pub mod binding;
pub mod drt;
pub mod fleet;
pub mod invariants;
pub mod resolve;
pub mod schema;
pub mod spacetime;

#[cfg(test)]
mod purity_tests {
    const SOURCES: [(&str, &str); 10] = [
        ("agency.rs", include_str!("agency.rs")),
        ("attr_expr.rs", include_str!("attr_expr.rs")),
        ("authority.rs", include_str!("authority.rs")),
        ("binding.rs", include_str!("binding.rs")),
        ("drt.rs", include_str!("drt.rs")),
        ("fleet.rs", include_str!("fleet.rs")),
        ("invariants.rs", include_str!("invariants.rs")),
        ("resolve.rs", include_str!("resolve.rs")),
        ("schema.rs", include_str!("schema.rs")),
        ("spacetime.rs", include_str!("spacetime.rs")),
    ];

    #[test]
    fn core_kernel_contains_zero_domain_strings() {
        let forbidden = [
            "vaultwarden",
            "caddy",
            "tailscale",
            "restic",
            "perses",
            "victoria",
            "btrfs",
            "systemd",
            "astrolabe",
            "skidbladnir",
            "ivaldi",
            "verft",
            "nixos",
            "state:persist",
            "http:route",
            "sops",
            "niks3",
            "nats",
            "mdbook",
        ];
        for (name, src) in SOURCES {
            let lower = src.to_lowercase();
            for word in forbidden {
                assert!(
                    !lower.contains(word),
                    "domain leak in usage-agnostic Baugr core kernel: `{word}` found in {name}"
                );
            }
        }
    }

    #[test]
    fn core_kernel_is_wasm_ready_without_os_io() {
        let forbidden_os = [
            "std::fs",
            "std::process",
            "std::env",
            "std::net",
            "std::time::Instant",
        ];
        for (name, src) in SOURCES {
            for line in src.lines() {
                let code = line.trim_start();
                if code.starts_with("//") {
                    continue;
                }
                for item in forbidden_os {
                    assert!(
                        !code.contains(item),
                        "OS-coupled API `{item}` found in pure Wasm-ready baugr-core/{name}"
                    );
                }
            }
        }
    }
}
