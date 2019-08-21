module Spec.HMAC

module S = Lib.Sequence

open Spec.Hash.Definitions
open FStar.Integers
open Lib.IntTypes

let wrap (a:hash_alg) (key: bytes{S.length key < max_input_length a}): Tot (lbytes (block_length a))
=
  let key0 = if S.length key <= block_length a then key else Spec.Hash.hash a key in
  let paddingLength = block_length a - S.length key0 in
  S.concat #uint8 #(S.length key0) #paddingLength key0 (S.create paddingLength (u8 0))

let xor (x: uint8) (v: bytes): Tot (lbytes (S.length v)) =
  Spec.Loops.seq_map (logxor x) v

#push-options "--max_fuel 1"

let rec xor_lemma (x: uint8) (v: bytes) : Lemma
  (ensures (xor x v == Spec.Loops.seq_map2 logxor (Seq.create (Seq.length v) x) v))
  (decreases (Seq.length v)) =
  let l = Seq.length v in
  if l = 0 then () else (
    let xs  = Seq.create l x in
    let xs' = Seq.create (l-1) x in
    Seq.lemma_eq_intro (Seq.slice xs 1 l) xs';
    xor_lemma x (Seq.slice v 1 l))

#pop-options
#push-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 70"

let hmac a key data =
  let k = wrap a key in
  let h1 = Spec.Hash.hash a (Seq.append (xor (u8 0x36) k) data) in
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 32 < pow2 125);
  let h2 = Spec.Hash.hash a (Seq.append (xor (u8 0x5c) k) h1) in
  h2
