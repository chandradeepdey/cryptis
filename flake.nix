{
  description = "A separation logic for cryptographic protocols";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
    reloc.url = "git+https://gitlab.mpi-sws.org/arthuraa/reloc.git?ref=local-changes";
    reloc.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs = { self, nixpkgs, flake-utils, reloc }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs =
          import nixpkgs {
            inherit system;
            overlays = [ reloc.overlays.default ];
          };
        lib = pkgs.lib;
      in
        {
          devShell = pkgs.mkShell {
            packages = [
              pkgs.coq
              pkgs.coqPackages.mathcomp.ssreflect
              pkgs.coqPackages.deriving
              pkgs.coqPackages.iris
              pkgs.coqPackages.reloc
            ];
          };
        }
    ) //
    {
      overlays.default = final: prev: {
        coqPackages = prev.coqPackages.overrideScope (final: prev: {});
      };
    };
}
