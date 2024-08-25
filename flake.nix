{
  description = "Call Agda2hs";

  inputs.agda2hs.url = "github:Agda/agda2hs";
  inputs.nixpkgs.follows = "agda2hs/nixpkgs";
  inputs.flake-utils.follows = "agda2hs/flake-utils";

  outputs = { self, agda2hs, flake-utils, nixpkgs }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };

        agda-libs = [ pkgs.agdaPackages.standard-library agda2hs.outputs.packages.${system}.agda2hs-lib ];
        agda2hs-mine = agda2hs.outputs.lib.${system}.withPackages agda-libs;
        agda-mine = pkgs.agda.withPackages agda-libs;
      in
      {
        packages = {
          inherit agda2hs-mine agda-mine;
          default = agda2hs-mine;
        };
      });
}
