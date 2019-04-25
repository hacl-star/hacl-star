module Spec.HMAC

module S = FStar.Seq

open Spec.Hash.Definitions
open FStar.Integers

let wrap (a:hash_alg) (key: bytes{S.length key < max_input_length a}): Tot (lbytes (block_length a))
=
  let key0 = if S.length key <= block_length a then key else Spec.Hash.hash a key in
  let paddingLength = block_length a - S.length key0 in
  S.append key0 (S.create paddingLength 0uy)

let xor (x: UInt8.t) (v: bytes): Tot (lbytes (S.length v)) =
  Spec.Loops.seq_map (FStar.UInt8.logxor x) v

#push-options "--max_fuel 1"
let rec xor_lemma (x: UInt8.t) (v: bytes) : Lemma (requires True)
  (ensures (xor x v == Spec.Loops.seq_map2 FStar.UInt8.logxor (S.create (S.length v) x) v))
  (decreases (S.length v))
  [ SMTPat (xor x v) ]
=
  let l = S.length v in
  if l = 0 then () else (
    let xs  = S.create l x in
    let xs' = S.create (l-1) x in
    S.lemma_eq_intro (S.tail xs) xs';
    xor_lemma x (S.tail v))
#pop-options

#push-options "--max_fuel 0 --max_ifuel 0"
let hmac a key data =
  let k = wrap a key in
  let h1 = EverCrypt.Hash.spec a S.(xor 0x36uy k @| data) in
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 32 < pow2 125);
  let h2 = EverCrypt.Hash.spec a S.(xor 0x5cuy k @| h1) in
  h2


