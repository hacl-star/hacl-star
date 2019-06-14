module Tezos

open FStar.HyperStack
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Curve25519.Fields
open Hacl.Impl.Curve25519.Generic


let curve25519_64_ecdh shared my_priv their_pub =
  Hacl.Curve25519_64.ecdh shared my_priv their_pub
