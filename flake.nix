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
      fstarPackage = fstarPackages.fstar;
      karamelPackage = karamel.packages.${system}.karamel.override {
        fstar = fstarPackage;
      };
      vale = pkgs.callPackage ./.nix/vale.nix {};
      hacl = pkgs.callPackage ./.nix/hacl.nix {
        inherit (fstarPackages) ocamlPackages z3;
        fstar = fstarPackage;
        inherit vale;
        karamel = karamelPackage;
        fstar-scripts = "${fstar}/.scripts";
      };
      # Keep admission explicit, including when bootstrapping the toolchain.
      fstarAdmit = fstarPackage.overrideAttrs (_: {ADMIT = "1";});
      karamelAdmit = (karamelPackage.override {fstar = fstarAdmit;}).overrideAttrs (_: {
        OTHERFLAGS = "--admit_smt_queries true";
      });
      haclAdmit = hacl.override {
        admit = true;
        fstar = fstarAdmit;
        karamel = karamelAdmit;
      };
      mkDevShell = package: pkgs.mkShell {
        inputsFrom = [package];
        VALE_HOME = vale;
        shellHook = ''
          export KRML_LIB="$(krml -locate-krmllib)"
          export KRML_INCLUDE="$(krml -locate-include)"
        '';
      };
    in {
      packages = {
        inherit hacl vale;
        default = hacl;
        hacl-admit = haclAdmit;
      };
      devShells = {
        default = mkDevShell hacl;
        admit = mkDevShell haclAdmit;
      };
    });
}
