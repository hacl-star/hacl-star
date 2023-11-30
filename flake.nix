{
  description = "HACL*";

  inputs = {
    fstar.url = "github:fstarlang/fstar";
    flake-utils.follows = "fstar/flake-utils";
    nixpkgs.follows = "fstar/nixpkgs";
    karamel = {
      url = "github:fstarlang/karamel";
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
        inherit hacl;
        default = hacl;
      };
    });
}
