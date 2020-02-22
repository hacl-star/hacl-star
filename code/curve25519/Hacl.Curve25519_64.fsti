module Hacl.Curve25519_64

open Hacl.Impl.Curve25519.Generic
open Hacl.Impl.Curve25519.Fields

val scalarmult: scalarmult_st (M64, Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled))
val secret_to_public: secret_to_public_st (M64, Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled))
val ecdh: ecdh_st (M64, Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled))
