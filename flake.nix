{
  inputs = {
    nixpkgs.url = "github:olynch/nixpkgs/add-binutils-to-ocaml";
    opam-repository = {
      url = "github:ocaml/opam-repository";
      flake = false;
    };
    opam-nix = {
      url = "github:tweag/opam-nix";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.opam-repository.follows = "opam-repository";
    };
    flake-utils.url = "github:numtide/flake-utils";
  };
  outputs = { self, flake-utils, opam-nix, nixpkgs, ... }@inputs:
    let package = "narya";
    in flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        pkgsStatic = pkgs.pkgsStatic;
        on = opam-nix.lib.${system};
        devPackagesQuery = {
          ocaml-lsp-server = "*";
          ocamlformat = "*";
        };
        query = devPackagesQuery // {
          ocaml-system = "*";
        };
        optional = nixpkgs.lib.optional;
        mkScopes = pkgs: rec {
          isStatic = pkgs.stdenv.hostPlatform.isStatic;
          scope = on.buildDuneProject { inherit pkgs; } package ./. query;
          overlay = final: prev: {
            # You can add overrides here
            ${package} = prev.${package}.overrideAttrs (_: {
              doNixSupport = false;
              buildInputs = [ pkgs.pkgsStatic.gmp ];
            } // (if pkgs.stdenv.hostPlatform.isStatic then {
              DUNE_PROFILE = "static";
            } else {}));
            conf-gmp = prev.conf-gmp.overrideAttrs (_: {
              depsBuildBuild = [ pkgs.buildPackages.stdenv.cc ] ++ prev.conf-gmp.depsBuildBuild;
            });
          };
          scope' = scope.overrideScope' overlay;
          main = scope'.${package};
        };
        scopes = mkScopes pkgs;
        scopesStatic = mkScopes pkgsStatic;
        # Packages from devPackagesQuery
        devPackages = builtins.attrValues
          (pkgs.lib.getAttrs (builtins.attrNames devPackagesQuery) scopes.scope');
      in {
        packages.default = scopesStatic.main;

        devShells.default = pkgs.mkShell {
          inputsFrom = [ scopes.main ];
          buildInputs = devPackages;
        };
      });
  nixConfig = {
    extra-substituters = "https://cache.nixos.org https://narya.cachix.org";
    extra-trusted-public-keys = "cache.nixos.org-1:6NCHdD59X431o0gWypbMrAURkbJ16ZPMQFGspcDShjY= narya.cachix.org-1:ZvDdkNFh5xvWcNy7D+gailHuwHTupstYSE/o77RR4A4=";
  };
}
