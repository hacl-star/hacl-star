module Hacl.PKCS11.External

open FStar.Seq
open FStar.UInt8

type uint8 = UInt8.t


(* CKM_EC_KEY_PAIR_GEN *)
assume val keyGenerationTemplateP256: unit -> Tot (seq uint8)

assume val keyGenerationTemplateCurve25519: unit -> Tot (seq uint8)
