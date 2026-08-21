{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";

    crane = {
      url = "github:ipetkov/crane";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    flake-utils.url = "github:numtide/flake-utils";

    fenix = {
      url = "github:nix-community/fenix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = {
    nixpkgs,
    crane,
    flake-utils,
    fenix,
    ...
  }:
    flake-utils.lib.eachDefaultSystem (system: let
      pkgs = import nixpkgs {
        inherit system;
      };

      toolchain = with fenix.packages.${system};
        combine [
          default.rustc
          default.cargo
          default.clippy
          default.rustfmt
        ];

      craneLib = (crane.mkLib pkgs).overrideToolchain toolchain;
      buildInputs = with pkgs; [];
    in rec {
      packages.default = craneLib.buildPackage {
        inherit buildInputs;
        src = pkgs.lib.cleanSourceWith {src = craneLib.path ../.;};
      };

      apps.default = flake-utils.lib.mkApp {
        drv = packages.default;
      };
    });
}
