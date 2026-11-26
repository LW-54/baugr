{
  description = "Baugr — Universal Promise Theory & Semantic Spacetime γ(3,4) Verification Framework";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    crane.url = "github:ipetkov/crane";
  };

  outputs = {
    nixpkgs,
    crane,
    ...
  }: let
    inherit (nixpkgs) lib;
    systems = ["x86_64-linux" "aarch64-linux"];
    forAllSystems = f:
      lib.genAttrs systems (system:
        f {
          inherit system;
          pkgs = import nixpkgs {inherit system;};
        });

    mkRust = pkgs: let
      craneLib = crane.mkLib pkgs;
      src = lib.fileset.toSource {
        root = ./.;
        fileset = lib.fileset.unions [
          ./Cargo.toml
          ./Cargo.lock
          ./.clippy.toml
          ./deny.toml
          ./crates
          ./examples
          ./fixtures
        ];
      };
      commonArgs = {
        pname = "baugr-workspace";
        version = "0.1.0";
        inherit src;
        strictDeps = true;
      };
      cargoArtifacts = craneLib.buildDepsOnly commonArgs;
    in {
      baugr = craneLib.buildPackage (commonArgs
        // {
          inherit cargoArtifacts;
          pname = "baugr";
          cargoExtraArgs = "-p baugr-cli";
          doCheck = false;
          meta.mainProgram = "baugr";
        });
      baugr-doc = craneLib.buildPackage (commonArgs
        // {
          inherit cargoArtifacts;
          pname = "baugr-doc";
          cargoExtraArgs = "-p baugr-doc";
          doCheck = false;
          meta.mainProgram = "baugr-doc";
        });
      clippy = craneLib.cargoClippy (commonArgs
        // {
          inherit cargoArtifacts;
          cargoClippyExtraArgs = "--workspace --all-targets -- --deny warnings";
        });
      test = craneLib.cargoTest (commonArgs // {inherit cargoArtifacts;});
      fmt = craneLib.cargoFmt {
        pname = "baugr-workspace";
        version = "0.1.0";
        inherit src;
      };
    };

    mkOracle = pkgs:
      pkgs.stdenv.mkDerivation {
        pname = "baugr-oracle";
        version = "0.1.0";
        src = lib.fileset.toSource {
          root = ./lean;
          fileset = lib.fileset.unions [
            ./lean/lakefile.toml
            ./lean/Baugr.lean
            ./lean/Baugr
          ];
        };
        nativeBuildInputs = [pkgs.lean4];
        buildPhase = ''
          export HOME=$TMPDIR
          lake build Baugr baugr-oracle
        '';
        doCheck = true;
        checkPhase = ''
          export HOME=$TMPDIR
          OUT=$(lake env lean Baugr/Audit.lean)
          echo "$OUT"
          if echo "$OUT" | grep -q "sorryAx"; then
            echo "ERROR: sorryAx detected in Baugr.Audit!" >&2
            exit 1
          fi
        '';
        installPhase = ''
          mkdir -p $out/bin
          cp .lake/build/bin/baugr-oracle $out/bin/baugr-oracle
        '';
      };

    smartGridSrc = lib.fileset.toSource {
      root = ./examples/smart-grid;
      fileset = ./examples/smart-grid;
    };
  in {
    packages = forAllSystems ({pkgs, ...}: let
      rust = mkRust pkgs;
    in {
      default = rust.baugr;
      inherit (rust) baugr baugr-doc;
      baugr-oracle = mkOracle pkgs;
    });

    checks = forAllSystems ({pkgs, ...}: let
      rust = mkRust pkgs;
      oracle = mkOracle pkgs;
    in {
      fmt = rust.fmt;
      clippy = rust.clippy;
      test = rust.test;
      lean-audit = oracle;

      smart-grid-drt = pkgs.runCommand "baugr-smart-grid-drt" {} ''
        ${rust.baugr}/bin/baugr --root ${smartGridSrc} check
        ${rust.baugr}/bin/baugr --root ${smartGridSrc} drt --oracle ${oracle}/bin/baugr-oracle --cases 500
        ${rust.baugr}/bin/baugr --root ${smartGridSrc} graph --impact battery-bank
        ${rust.baugr}/bin/baugr --root ${smartGridSrc} project trip-breaker
        echo "BAUGR_SMART_GRID_DRT_OK" > $out
      '';

      doc-pipe = pkgs.runCommand "baugr-doc-pipe" {} ''
        ${rust.baugr}/bin/baugr --root ${smartGridSrc} graph --json           | ${rust.baugr-doc}/bin/baugr-doc --out $out --title "Smart Grid Architecture"
        test -s $out/SUMMARY.md
        test -s $out/index.md
        test -s $out/promises.md
        test -s $out/scopes/substation.md
        test -s $out/scopes/microgrid.md
      '';
    });

    devShells = forAllSystems ({pkgs, ...}: {
      default = pkgs.mkShell {
        packages = [
          pkgs.rustc
          pkgs.cargo
          pkgs.rustfmt
          pkgs.clippy
          pkgs.just
          pkgs.alejandra
        ];
      };
      formal = pkgs.mkShell {
        packages = [
          pkgs.lean4
          pkgs.rustc
          pkgs.cargo
          pkgs.just
        ];
      };
    });

    formatter = forAllSystems ({pkgs, ...}: pkgs.alejandra);
  };
}
