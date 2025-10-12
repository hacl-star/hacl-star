{
  description = "HACL*";

  inputs = {
    fstar = {
      url = "github:fstarlang/fstar?ref=v2025.10.06";
    };
    flake-utils.follows = "fstar/flake-utils";
    nixpkgs.follows = "fstar/nixpkgs";
    karamel = {
      url = "github:fstarlang/karamel?ref=254e099bd586b17461845f6b0cab44c3ef5080e9";
      inputs.fstar.follows = "fstar";
      inputs.flake-utils.follows = "flake-utils";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = {
    self,
    fstar,
    flake-utils,
    nixpkgs,
    karamel,
  }:
    flake-utils.lib.eachSystem ["x86_64-linux"] (system: let
      pkgs = import nixpkgs {inherit system;};
      fstarPackages = fstar.packages.${system};
      karamel-home = karamel.packages.${system}.karamel.home;
      vale = pkgs.callPackage ./.nix/vale.nix {};
      hacl = pkgs.callPackage ./.nix/hacl.nix {
        inherit (fstarPackages) ocamlPackages z3 fstar;
        inherit vale;
        karamel = karamel-home;
        fstar-scripts = "${fstar}/.scripts";
      };
    in {
      packages = {
        inherit hacl vale;
        default = hacl;
      };
    });
}
