module Spec.Agile.HMAC

open Spec.Hash.Definitions
open Lib.IntTypes

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 50"

let wrap
  (a: fixed_len_alg)
  (key: bytes{Seq.length key `less_than_max_input_length` a})
  : lbytes (block_length a)
=
  let key0 = if Seq.length key <= block_length a then key else Spec.Agile.Hash.hash a key in
  let paddingLength = block_length a - Seq.length key0 in
  Seq.append key0 (Seq.create paddingLength (u8 0))

#push-options "--max_fuel 1"

let rec xor_lemma (x: uint8) (v: bytes) : Lemma
  (ensures xor x v == Spec.Loops.seq_map2 logxor (Seq.create (Seq.length v) x) v)
  (decreases (Seq.length v))
=
  let l = Seq.length v in
  if l > 0 then (
    let xs  = Seq.create l x in
    let xs' = Seq.create (l-1) x in
    Seq.lemma_eq_intro (Seq.slice xs 1 l) xs';
    xor_lemma x (Seq.slice v 1 l))

#pop-options

let hmac a key data =
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 32 < pow2 125);
  let k = wrap a key in
  let h1 = Spec.Agile.Hash.hash a (Seq.append (xor (u8 0x36) k) data) in
  let h2 = Spec.Agile.Hash.hash a (Seq.append (xor (u8 0x5c) k) h1) in
  h2
