{
  pkgs ? import ((import <nixpkgs> { }).fetchFromGitHub {
    owner = "NixOs";
    repo = "nixpkgs";
    rev = "nixos-26.05";
    sha256 = "sha256-J9oC0bKnkXUrMegqRTXVkyDFJ0gn2U/Qpoo9HgGMQmA=";
  }) { },
  use_system_vim ? false,
  ...
}:
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
