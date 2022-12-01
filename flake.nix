{
  description = "Hacl*";

  inputs = {
    fstar-src = {
      url = "github:fstarlang/fstar";
      flake = false;
    };
    karamel-src = {
      url = "github:fstarlang/karamel";
      flake = false;
    };
    hacl-nix = {
      url = "github:hacl-star/hacl-nix";
      inputs.fstar-src.follows = "fstar-src";
      inputs.karamel-src.follows = "karamel-src";
    };
    nixpkgs.follows = "hacl-nix/nixpkgs";
    flake-utils.follows = "hacl-nix/flake-utils";
  };

  outputs = { hacl-nix, nixpkgs, flake-utils, ... }:
    flake-utils.lib.eachSystem [ "x86_64-linux" ] (system:
      let
        pkgs = import nixpkgs { inherit system; };
        ocamlPackages = pkgs.ocaml-ng.ocamlPackages_4_12;
        hacl = pkgs.callPackage ./. {
          inherit (hacl-nix.packages.${system}) z3 fstar karamel vale;
          inherit ocamlPackages;
        };
      in {
        packages = {
          inherit hacl;
          default = hacl;
        };
        hydraJobs = {
          inherit hacl;
          hacl-build-products = hacl.passthru.build-products;
          hacl-stats = hacl.passthru.stats;
          hacl-dist-compare = hacl.passthru.dist-compare;
          hacl-dist-list = hacl.passthru.dist-list;
        };
      });
}
