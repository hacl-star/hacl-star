module Hacl.HPKE.Curve51_CP32_SHA256

open Hacl.Meta.HPKE

module IDH = Hacl.Impl.Generic.DH

friend Hacl.Meta.HPKE

let setupBaseI = hpke_setupBaseI_higher #cs IDH.secret_to_public_c51 IDH.scalarmult_c51
