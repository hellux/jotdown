{ pkgs ? (import (builtins.fetchTarball {
  url = "https://github.com/NixOS/nixpkgs/archive/nixos-26.05.tar.gz";
  sha256 = "0miz2qn3lamkpqyjbfmz93h4icr323ds7l218vvsgq206razvb5v";
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
