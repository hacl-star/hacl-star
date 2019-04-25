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

let wrap_lemma (a:hash_alg) (key: bytes{S.length key < max_input_length a}): Lemma
  (requires S.length key > block_length a)
  (ensures wrap a key == (
    let key0 = Spec.Hash.hash a key in
    let paddingLength = block_length a - S.length key0 in
    S.concat #uint8 #(S.length key0) #paddingLength key0 (S.create paddingLength (u8 0)))) = ()

let xor (x: uint8) (v: bytes): Tot (lbytes (S.length v)) =
  Spec.Loops.seq_map (logxor x) v


#push-options "--max_fuel 1"

let rec xor_lemma (x: uint8) (v: bytes{S.length v <= max_size_t}) : Lemma
  (ensures (xor x v == Spec.Loops.seq_map2 logxor (S.create (S.length v) x) v))
  (decreases (S.length v)) =
  let l = S.length v in
  if l = 0 then () else (
    let xs  = S.create #uint8 l x in
    let xs' = S.create (l-1) x in
    S.eq_intro (S.sub xs 1 (l - 1)) xs';
    xor_lemma x (S.sub #uint8 #l v 1 (l - 1)))

#pop-options
#push-options "--max_fuel 0 --max_ifuel 0"

let hmac a key data =
  let k = wrap a key in
  assert_norm(max_size_t + block_length a < pow2 61);
  assert_norm(max_size_t + block_length a < pow2 125);
  let h1 =
    Spec.Hash.hash a (S.concat #uint8 #(S.length k) #(S.length data) (xor (u8 0x36) k) data)
  in
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 32 < pow2 125);
  let h2 = Spec.Hash.hash a (S.concat #uint8 #(S.length k) #(S.length h1) (xor (u8 0x5c) k) h1) in
  h2
