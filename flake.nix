{
  inputs = {
    fstar-src.url     = github:W95Psp/FStar?ref=data-constructors-attributes;
    fstar-src.flake   = false;
    karamel-src.url   = github:fstarlang/karamel?ref=master;
    karamel-src.flake = false;
    
    everest = {
      url = github:project-everest/everest-nix?dir=projects;
      inputs.fstar-src.follows    = "fstar-src";
      inputs.karamel-src.follows  = "karamel-src";
      # `/` means `self` (see NixOS/nix#4931)
      inputs.hacl-src.follows     = "/";
    };

    flake-utils.url = "flake-utils";
    nixpkgs.url = "nixpkgs";
  };

  outputs = {everest, ...}: everest;
}
