{ pkgs ? (import (builtins.fetchTarball {
  url = "https://github.com/NixOS/nixpkgs/archive/nixos-25.11.tar.gz";
  sha256 = "sha256:06rhb49ksbc07lp31xgf8qdlph29knrql30x58s4x3fflcw8zkg5";
}) { }), use_system_vim ? false, ... }:
pkgs.mkShell {
  buildInputs = [
    pkgs.bmake
    pkgs.cacert # npm install
    pkgs.cargo
    pkgs.clippy
    pkgs.git # submodules
    pkgs.lld # wasm-pack
    pkgs.nodejs # djot.js
    pkgs.python3 # jotdown_wasm http server
    pkgs.rustc
    pkgs.wasm-pack # jotdown_wasm

    # extra dev tools
    pkgs.rust-analyzer
  ];

  MIME_TYPES = "${pkgs.mailcap}/etc/nginx/mime.types";
}
