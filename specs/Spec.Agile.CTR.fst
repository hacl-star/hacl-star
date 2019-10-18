module Spec.Agile.CTR

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Spec.Agile.Cipher

#reset-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 1"

// So that clients don't need to open both modules
include Spec.Agile.Cipher

val counter_mode:
  a:cipher_alg ->
  k:key a ->
  n:nonce a ->
  plain:bytes { length plain <= max_size_t } ->
  Tot (cipher:bytes { length cipher = length plain })
let counter_mode a k n plain =
  let stream = ctr_stream a k n (length plain) in
  map2 ( ^. ) (plain <: lbytes (length plain)) (stream <: lbytes (length plain))
