module Hacl.Meta.HPKE

friend Hacl.Impl.HPKE

%splice[
  hpke_setupBaseS_higher;
  hpke_setupBaseR_higher;
  hpke_sealBase_higher;
  hpke_openBase_higher
] (Meta.Interface.specialize (`Spec.Agile.HPKE.ciphersuite) [
    `Hacl.Impl.HPKE.setupBaseS;
    `Hacl.Impl.HPKE.setupBaseR;
    `Hacl.Impl.HPKE.sealBase;
    `Hacl.Impl.HPKE.openBase
])
