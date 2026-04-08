{
  description = "Clift: Lifting C into Lean 4 for formal verification";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.11";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
      in {
        devShells.default = pkgs.mkShell {
          buildInputs = [
            pkgs.elan              # Lean version manager (reads lean-toolchain)
            (pkgs.python3.withPackages (ps: [ ps.pytest ]))  # CImporter + testing
            pkgs.clang_17          # Pinned clang for JSON AST dump
            pkgs.just              # Task runner
            pkgs.jq                # Inspect clang JSON output
          ];
        };
      });
}
