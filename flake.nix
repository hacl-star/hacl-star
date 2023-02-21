{
  description = "Hacl*";

  inputs = {
    fstar.url = "github:fstarlang/fstar";
    flake-utils.follows = "fstar/flake-utils";
    nixpkgs.follows = "fstar/nixpkgs";
    karamel-src = {
      url = "github:fstarlang/karamel";
      flake = false;
    };
  };

  outputs = { self, fstar, flake-utils, nixpkgs, karamel-src }:
    flake-utils.lib.eachSystem [ "x86_64-linux" ] (system:
      let
        pkgs = import nixpkgs { inherit system; };
        fstarPackages = fstar.packages.${system};
        karamel = pkgs.callPackage ./.nix/karamel.nix {
          inherit (fstarPackages) ocamlPackages z3 fstar;
          src = karamel-src;
        };
        vale = pkgs.callPackage ./.nix/vale.nix { };
        hacl = pkgs.callPackage ./.nix/hacl.nix {
          inherit (fstarPackages) ocamlPackages z3 fstar;
          inherit karamel vale;
        };
      in {
        packages = {
          inherit (fstarPackages) ocamlPackages z3 fstar;
          inherit karamel vale hacl;
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
