module Hacl.Curve25519_51

open Hacl.Impl.Curve25519.Generic
open Hacl.Impl.Curve25519.Fields

val scalarmult: scalarmult_st M51 True
val secret_to_public: secret_to_public_st M51 True
val ecdh: ecdh_st M51 True
