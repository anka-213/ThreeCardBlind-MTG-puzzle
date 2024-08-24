{
  description = "Call Agda2hs";

  inputs.agda2hs.url = "github:Agda/agda2hs";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs";
  inputs.nixpkgs.follows = "agda2hs";
  inputs.flake-utils.url = "github:numtide/flake-utils";
  inputs.flake-utils.follows = "agda2hs";

  outputs = { self, agda2hs, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };

        agda2hs-mine = agda2hs.outputs.lib.withPackages [ pkgs.agdaPackages.standard-library ];
      in
      {
        packages = {
          # inherit agda2hs-lib;
          # inherit (agda2hs) agda2hs;
          inherit agda2hs-mine;
          default = agda2hs-mine;
        };
        # lib = {
        #   inherit (agda2hs) withPackages;
        #   inherit agda2hs-pkg agda2hs-hs agda2hs-expr;
        # };
        # devShells.default = pkgs.haskellPackages.shellFor {
        #   packages = p: [ agda2hs-hs ];
        #   buildInputs = with pkgs.haskellPackages; [
        #     cabal-install
        #     cabal2nix
        #     haskell-language-server
        #     pkgs.agda
        #   ];
        # };
      });
}
