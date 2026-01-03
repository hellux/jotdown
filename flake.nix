{
  description = "A parser for the Djot markup language";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, flake-utils, rust-overlay }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        overlays = [ (import rust-overlay) ];
        pkgs = import nixpkgs {
          inherit system overlays;
        };

        rustToolchain = pkgs.rust-bin.stable.latest.default.override {
          extensions = [ "rust-src" "rust-analyzer" ];
        };

        rustNightly = pkgs.rust-bin.nightly.latest.default.override {
          extensions = [ "rust-src" "llvm-tools-preview" ];
        };
      in
      {
        devShells = {
          default = pkgs.mkShell {
            buildInputs = with pkgs; [
              rustToolchain
              cargo
              rustfmt
              clippy
            ];

            shellHook = ''
              echo "jotdown development environment"
              echo "Rust version: $(rustc --version)"
            '';
          };

          fuzz = pkgs.mkShell {
            buildInputs = [
              rustNightly
              pkgs.cargo-fuzz
            ];

            shellHook = ''
              echo "jotdown fuzzing environment"
              echo "Rust version: $(rustc --version)"
              echo "cargo-fuzz installed"
              echo ""
              echo "Run fuzzer with: cd fuzz && cargo fuzz run compare_renderers"
            '';
          };
        };
      }
    );
}
