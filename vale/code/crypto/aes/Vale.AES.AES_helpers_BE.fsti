module Vale.AES.AES_helpers_BE

open Vale.Def.Opaque_s
open Vale.Def.Words_s
open Vale.Def.Types_s
open FStar.Seq
open Vale.AES.AES_BE_s
open FStar.Mul
open Vale.Arch.Types
open Vale.Def.Words.Seq_s

// syntax for seq accesses, s.[index] and s.[index] <- value
unfold let (.[]) (#a:Type) (s:seq a) (i:nat{ i < length s}) : Tot a = index s i
unfold let (.[]<-) = Seq.upd

unfold let ( *^ ) = nat32_xor
unfold let ( *^^ ) = quad32_xor

unfold let be_quad32_to_seq (q:quad32) : seq nat32 = four_to_seq_BE q

let quad32_shr32 (q:quad32) : quad32 =
  let Mkfour v0 v1 v2 v3 = q in
  Mkfour v1 v2 v3 0


// Redefine key expansion in terms of quad32 values rather than nat32 values,
// then prove both definitions are equivalent.

let round_key_128_rcon (prev:quad32) (rcon:nat32) : quad32 =
  let Mkfour v0 v1 v2 v3 = prev in
  let w3 = v3 *^ (sub_word (rot_word v0) *^ rcon) in
  let w2 = v2 *^ w3 in
  let w1 = v1 *^ w2 in
  let w0 = v0 *^ w1 in
  Mkfour w0 w1 w2 w3

let round_key_128 (prev:quad32) (round:nat) : quad32 =
  round_key_128_rcon prev (aes_rcon (round - 1))

let rec expand_key_128_def (key:seq nat32) (round:nat) : Pure quad32
  (requires is_aes_key_word AES_128 key)
  (ensures fun _ -> True)
  =
  if round = 0 then Mkfour key.[3] key.[2] key.[1] key.[0]
  else round_key_128 (expand_key_128_def key (round - 1)) round
[@"opaque_to_smt"] let expand_key_128 = opaque_make expand_key_128_def
irreducible let expand_key_128_reveal = opaque_revealer (`%expand_key_128) expand_key_128 expand_key_128_def

val lemma_expand_key_128_0 (key:aes_key_word AES_128) : Lemma
  (equal key (expand_key AES_128 key 4))

val lemma_expand_key_128_i (key:aes_key_word AES_128) (i:nat) : Lemma
  (requires
    0 < i /\ i < 11
  )
  (ensures (
    let m = 4 * (i - 1) in
    let n = 4 * i in
    let v = expand_key AES_128 key n in
    let w = expand_key AES_128 key (n + 4) in
    let prev =              Mkfour v.[m + 3] v.[m + 2] v.[m + 1] v.[m + 0] in
    round_key_128 prev i == Mkfour w.[n + 3] w.[n + 2] w.[n + 1] w.[n + 0]
  ))

// expand_key for large 'size' argument agrees with expand_key for smaller 'size' argument
val lemma_expand_append (key:aes_key_word AES_128) (size1:nat) (size2:nat) : Lemma
  (requires size1 <= size2 /\ size2 <= 44)
  (ensures equal (expand_key AES_128 key size1) (slice (expand_key AES_128 key size2) 0 size1))
  (decreases size2)

// quad32 key expansion is equivalent to nat32 key expansion
val lemma_expand_key_128 (key:seq nat32) (size:nat) : Lemma
  (requires size <= 11 /\ is_aes_key_word AES_128 key)
  (ensures (
    let s = key_schedule_to_round_keys size (expand_key AES_128 key 44) in
    (forall (i:nat).{:pattern (expand_key_128 key i) \/ (expand_key_128_def key i)}
      i < size ==> expand_key_128 key i == s.[i])
  ))

// Refine round_key_128 to a SIMD computation
let simd_round_key_128 (prev:quad32) (rcon:nat32) : quad32 =
  let r = rot_word (sub_word prev.lo0 *^ ishl32 rcon 16) in
  let q = prev in
  let q = q *^^ quad32_shr32 q in
  let q = q *^^ quad32_shr32 q in
  let q = q *^^ quad32_shr32 q in
  q *^^ Mkfour r r r r

// SIMD version of round_key_128 is equivalent to scalar round_key_128
val lemma_simd_round_key (prev:quad32) (rcon:nat32) : Lemma
  (simd_round_key_128 prev rcon == round_key_128_rcon prev rcon)

val init_rounds_opaque (init:quad32) (round_keys:seq quad32) :
  Lemma (length round_keys > 0 ==> eval_rounds init round_keys 0 == init)

val finish_cipher (alg:algorithm) (input:quad32) (round_keys:seq quad32) :
  Lemma
    (length round_keys == (nr alg) + 1 ==>
        length round_keys > 0 /\ nr alg > 1 /\   // REVIEW: Why are these needed?
           (let state = quad32_xor input (index round_keys 0) in
            let state = eval_rounds state round_keys (nr alg - 1) in
            let state = sub_bytes state in
            let state = shift_rows state in
            let state = quad32_xor state (index round_keys (nr alg)) in
            state == eval_cipher alg input round_keys))

val finish_cipher_opt (alg:algorithm) (input plain t0 t1 out:quad32) (round_keys:seq quad32) : Lemma
  (requires length round_keys == (nr alg) + 1 /\
            length round_keys > 0 /\ nr alg > 1 /\   // REVIEW: Why are these needed?
            t0 = quad32_xor input (index round_keys 0) /\
            t1 = eval_rounds t0 round_keys (nr alg - 1) /\
            out = quad32_xor (shift_rows (sub_bytes t1)) (quad32_xor plain (index round_keys (nr alg))))
  (ensures out == quad32_xor plain (eval_cipher alg input round_keys))
