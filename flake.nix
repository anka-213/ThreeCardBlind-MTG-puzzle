{
  description = "Call Agda2hs";

  inputs.agda2hs.url = "github:Agda/agda2hs";
  inputs.nixpkgs.follows = "agda2hs/nixpkgs";
  inputs.flake-utils.follows = "agda2hs/flake-utils";

  outputs = { self, agda2hs, flake-utils, nixpkgs }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };

        agda2hs-mine = agda2hs.outputs.lib.${system}.withPackages [ pkgs.agdaPackages.standard-library ];
        agda-mine = pkgs.agda.withPackages [ pkgs.agdaPackages.standard-library ];
      in
      {
        packages = {
          inherit agda2hs-mine agda-mine;
          default = agda2hs-mine;
        };
      });
}
