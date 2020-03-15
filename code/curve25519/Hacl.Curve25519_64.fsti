module Hacl.Curve25519_64

open Hacl.Impl.Curve25519.Generic
open Hacl.Impl.Curve25519.Fields

inline_for_extraction noextract
let p = Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled)

val scalarmult: scalarmult_st M64 p
val secret_to_public: secret_to_public_st M64 p
val ecdh: ecdh_st M64 p
