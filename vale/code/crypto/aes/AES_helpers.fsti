module AES_helpers

open Opaque_s
open Words_s
open Types_s
open FStar.Seq
open AES_s
open FStar.Mul

// syntax for seq accesses, s.[index] and s.[index] <- value
unfold
let op_String_Access (#a:Type) (s:seq a) (i:nat{ i < length s}) : Tot a = index s i

unfold
let op_String_Assignment = Seq.upd

unfold let ( *^ ) = nat32_xor
unfold let ( *^^ ) = quad32_xor

let quad32_shl32 (q:quad32) : quad32 =
  let Mkfour v0 v1 v2 v3 = q in
  Mkfour 0 v0 v1 v2


// Redefine key expansion in terms of quad32 values rather than nat32 values,
// then prove both definitions are equivalent.

let round_key_128_rcon (prev:quad32) (rcon:nat32) : quad32 =
  let Mkfour v0 v1 v2 v3 = prev in
  let w0 = v0 *^ (sub_word (rot_word_LE v3) *^ rcon) in
  let w1 = v1 *^ w0 in
  let w2 = v2 *^ w1 in
  let w3 = v3 *^ w2 in
  Mkfour w0 w1 w2 w3

let round_key_128 (prev:quad32) (round:nat) : quad32 =
  round_key_128_rcon prev (aes_rcon (round - 1))

let rec expand_key_128_def (key:seq nat32) (round:nat) : Pure quad32
  (requires is_aes_key_LE AES_128 key)
  (ensures fun _ -> True)
  =
  if round = 0 then Mkfour key.[0] key.[1] key.[2] key.[3]
  else round_key_128 (expand_key_128_def key (round - 1)) round

let expand_key_128 = make_opaque expand_key_128_def

val lemma_expand_key_128_0 (key:aes_key_LE AES_128) : Lemma
  (equal key (expand_key AES_128 key 4))

val lemma_expand_key_128_i (key:aes_key_LE AES_128) (i:nat) : Lemma
  (requires
    0 < i /\ i < 11
  )
  (ensures (
    let m = 4 * (i - 1) in
    let n = 4 * i in
    let v = expand_key AES_128 key n in
    let w = expand_key AES_128 key (n + 4) in
    let prev =              Mkfour v.[m + 0] v.[m + 1] v.[m + 2] v.[m + 3] in
    round_key_128 prev i == Mkfour w.[n + 0] w.[n + 1] w.[n + 2] w.[n + 3]
  ))

// expand_key for large 'size' argument agrees with expand_key for smaller 'size' argument
val lemma_expand_append (key:aes_key_LE AES_128) (size1:nat) (size2:nat) : Lemma
  (requires size1 <= size2 /\ size2 <= 44)
  (ensures equal (expand_key AES_128 key size1) (slice (expand_key AES_128 key size2) 0 size1))
  (decreases size2)

// quad32 key expansion is equivalent to nat32 key expansion
val lemma_expand_key_128 (key:seq nat32) (size:nat) : Lemma
  (requires size <= 11 /\ is_aes_key_LE AES_128 key)
  (ensures (
    let s = key_schedule_to_round_keys size (expand_key AES_128 key 44) in
    (forall (i:nat).{:pattern (expand_key_128 key i) \/ (expand_key_128_def key i)}
      i < size ==> expand_key_128 key i == s.[i])
  ))

// Refine round_key_128 to a SIMD computation
let simd_round_key_128 (prev:quad32) (rcon:nat32) : quad32 =
  let r = rot_word_LE (sub_word prev.hi3) *^ rcon in
  let q = prev in
  let q = q *^^ quad32_shl32 q in
  let q = q *^^ quad32_shl32 q in
  let q = q *^^ quad32_shl32 q in
  q *^^ Mkfour r r r r

// SIMD version of round_key_128 is equivalent to scalar round_key_128
val lemma_simd_round_key (prev:quad32) (rcon:nat32) : Lemma
  (simd_round_key_128 prev rcon == round_key_128_rcon prev rcon)

val commute_sub_bytes_shift_rows_forall (_:unit) :
  Lemma
    (forall q.{:pattern sub_bytes (shift_rows_LE q) \/ shift_rows_LE (sub_bytes q)}
      sub_bytes (shift_rows_LE q) == shift_rows_LE (sub_bytes q))

let rounds_opaque = make_opaque rounds
let cipher_opaque = make_opaque cipher

val init_rounds_opaque (init:quad32) (round_keys:seq quad32) :
  Lemma (length round_keys > 0 ==> rounds_opaque init round_keys 0 == init)

val finish_cipher (alg:algorithm) (input:quad32) (round_keys:seq quad32) :
  Lemma
    (length round_keys == (nr alg) + 1 ==>
        length round_keys > 0 /\ nr alg > 1 /\   // REVIEW: Why are these needed?
           (let state = quad32_xor input (index round_keys 0) in
            let state = rounds_opaque state round_keys (nr alg - 1) in
            let state = shift_rows_LE state in
            let state = sub_bytes state in
            let state = quad32_xor state (index round_keys (nr alg)) in
            state == cipher_opaque alg input round_keys))

val finish_cipher_opt (alg:algorithm) (input plain t0 t1 out:quad32) (round_keys:seq quad32) : Lemma
  (requires length round_keys == (nr alg) + 1 /\
            length round_keys > 0 /\ nr alg > 1 /\   // REVIEW: Why are these needed?
            t0 = quad32_xor input (index round_keys 0) /\
            t1 = rounds_opaque t0 round_keys (nr alg - 1) /\
            out = quad32_xor (sub_bytes (shift_rows_LE t1)) (quad32_xor plain (index round_keys (nr alg))))
  (ensures out == quad32_xor plain (cipher_opaque alg input round_keys))


val lemma_incr_msb (orig ctr ctr':quad32) (increment:nat) : Lemma
  (requires increment < 256 /\
            ctr == reverse_bytes_quad32 orig /\
            ctr' == Arch.Types.add_wrap_quad32 ctr (Mkfour 0 0 0 (increment * 0x1000000)))
  (ensures  (orig.lo0 % 256) + increment < 256 ==> ctr' == reverse_bytes_quad32 (GCTR_s.inc32 orig increment))

val lemma_msb_in_bounds (ctr_BE inout5 t1':quad32) (counter:nat) : Lemma
  (requires inout5 == reverse_bytes_quad32 (GCTR_s.inc32 ctr_BE 5) /\
            counter == ctr_BE.lo0 % 256 /\
            counter + 6 < 256 /\
            t1' == Arch.Types.add_wrap_quad32 inout5 (Mkfour 0 0 0 0x1000000))
  (ensures  t1' == reverse_bytes_quad32 (GCTR_s.inc32 ctr_BE 6))
