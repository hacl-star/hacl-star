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
      # `/` means `self` (see NixOS/nix#4931)
      inputs.hacl-src.follows = "/";
    };
  };

  outputs = { hacl-nix, ... }: hacl-nix;
}
