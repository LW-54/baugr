{
  description = "Baugr — Formally Verified Promise Theory & Semantic Spacetime γ(3,4) Library";

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
          ./src
          ./tests
          ./examples
        ];
      };
      commonArgs = {
        pname = "baugr";
        version = "0.3.0";
        inherit src;
        strictDeps = true;
      };
      cargoArtifacts = craneLib.buildDepsOnly commonArgs;
    in {
      clippy = craneLib.cargoClippy (commonArgs
        // {
          inherit cargoArtifacts;
          cargoClippyExtraArgs = "--all-targets -- --deny warnings";
        });
      test = craneLib.cargoTest (commonArgs // {inherit cargoArtifacts;});
      drt = oracle:
        craneLib.cargoTest (commonArgs
          // {
            inherit cargoArtifacts;
            pnameSuffix = "-drt";
            cargoTestExtraArgs = "--test drt";
            BAUGR_ORACLE = "${oracle}/bin/baugr-oracle";
          });
      doc = craneLib.cargoDoc (commonArgs
        // {
          inherit cargoArtifacts;
          RUSTDOCFLAGS = "--deny warnings";
        });
      fmt = craneLib.cargoFmt {
        pname = "baugr";
        version = "0.3.0";
        inherit src;
      };
    };

    mkOracle = pkgs:
      pkgs.stdenv.mkDerivation {
        pname = "baugr-oracle";
        version = "0.3.0";
        src = lib.fileset.toSource {
          root = ./lean;
          fileset = lib.fileset.unions [
            ./lean/lakefile.toml
            ./lean/lake-manifest.json
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

    mkPaper = pkgs:
      pkgs.stdenvNoCC.mkDerivation {
        pname = "baugr-paper";
        version = "0.3.0";
        src = lib.fileset.toSource {
          root = ./paper;
          fileset = lib.fileset.unions [
            ./paper/baugr.typ
            ./paper/refs.bib
          ];
        };
        nativeBuildInputs = [pkgs.typst];
        buildPhase = ''
          typst compile baugr.typ baugr.pdf
        '';
        installPhase = ''
          mkdir -p $out
          cp baugr.pdf $out/baugr.pdf
        '';
      };
  in {
    packages = forAllSystems ({pkgs, ...}: {
      baugr-oracle = mkOracle pkgs;
      paper = mkPaper pkgs;
    });

    checks = forAllSystems ({pkgs, ...}: let
      rust = mkRust pkgs;
      oracle = mkOracle pkgs;
      paper = mkPaper pkgs;
    in {
      fmt = rust.fmt;
      clippy = rust.clippy;
      doc = rust.doc;
      test = rust.test;
      lean-audit = oracle;
      drt = rust.drt oracle;
      inherit paper;
    });

    devShells = forAllSystems ({pkgs, ...}: {
      default = pkgs.mkShell {
        packages = [
          pkgs.rustc
          pkgs.cargo
          pkgs.rustfmt
          pkgs.clippy
          pkgs.typst
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
