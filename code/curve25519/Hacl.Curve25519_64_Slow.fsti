module Hacl.Curve25519_64_Slow

open Hacl.Impl.Curve25519.Generic
open Hacl.Impl.Curve25519.Fields

val scalarmult: scalarmult_st M64 True
val secret_to_public: secret_to_public_st M64 True
val ecdh: ecdh_st M64 True
