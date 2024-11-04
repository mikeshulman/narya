{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
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
    # Don't forget to put the package name instead of `throw':
    let package = "narya";
    in flake-utils.lib.eachDefaultSystem (system:
      let
        pkgsDynamic = import nixpkgs {
          inherit system;
        };
        pkgsStatic = import nixpkgs {
          inherit system;
          overlays = [(final: prev: rec {
            ocaml = prev.ocaml.overrideAttrs (_: {
              depsBuildBuild = [ prev.binutils ] ++ prev.ocaml.depsBuildBuild;
            });
            ocaml-ng = prev.ocaml-ng // {
              ocamlPackages_5_2 = prev.ocaml-ng.ocamlPackages_5_2 // {
                ocaml = ocaml;
              };
            };
          })];
          crossSystem = { config = "x86_64-unknown-linux-musl"; };
        };
        on = opam-nix.lib.${system};
        devPackagesQuery = {
          # You can add "development" packages here. They will get added to the devShell automatically.
          ocaml-lsp-server = "*";
          ocamlformat = "*";
        };
        query = devPackagesQuery // {
          ## You can force versions of certain packages here, e.g:
          ## - force the ocaml compiler to be taken from opam-repository:
          ocaml-system = "*";
          ## - or force the compiler to be taken from nixpkgs and be a certain version:
          # ocaml-system = "4.14.0";
          ## - or force ocamlfind to be a certain version:
          # ocamlfind = "1.9.2";
        };
        optional = nixpkgs.lib.optional;
        mkScopes = pkgs: rec {
          isStatic = pkgs.stdenv.hostPlatform.isStatic;
          src = nixpkgs.lib.cleanSourceWith {
            filter = name: type: let baseName = baseNameOf (toString name); in !(
              (baseName == "flake.nix") ||
              (baseName == "flake.lock") ||
              (baseName == "static.patch")
            );
            src = ./.;
          };
          patched = pkgs.stdenv.mkDerivation {
            name = package;
            inherit src;
            buildPhase = ''
              patch -p1 < ${./static.patch}
              cp -r . $out
            '';
          };
          scope = on.buildDuneProject { inherit pkgs; } package patched query;
          overlay = final: prev: {
            # You can add overrides here
            ${package} = prev.${package}.overrideAttrs (_: {
              # Prevent the ocaml dependencies from leaking into dependent environments
              doNixSupport = false;
              buildInputs = [ pkgs.pkgsStatic.gmp ] ++ prev.${package}.buildInputs;
            });
            conf-gmp = prev.conf-gmp.overrideAttrs (_: {
              depsBuildBuild = [ pkgs.buildPackages.stdenv.cc ] ++ prev.conf-gmp.depsBuildBuild;
            });
          };
          scope' = scope.overrideScope' overlay;
          # The main package containing the executable
          main = scope'.${package};
        };
        scopesDynamic = mkScopes pkgsDynamic;
        scopesStatic = mkScopes pkgsStatic;
        # Packages from devPackagesQuery
        devPackages = builtins.attrValues
          (pkgsDynamic.lib.getAttrs (builtins.attrNames devPackagesQuery) scopesDynamic.scope');
      in {
        packages.default = scopesStatic.main;

        devShells.default = pkgsDynamic.mkShell {
          inputsFrom = [ scopesDynamic.main ];
          buildInputs = devPackages ++ [
            # You can add packages from nixpkgs here
          ];
        };
      });
}
