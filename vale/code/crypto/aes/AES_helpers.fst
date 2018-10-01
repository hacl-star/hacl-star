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

let rec expand_key_128_def (key:aes_key_LE AES_128) (round:nat) : quad32 =
  if round = 0 then Mkfour key.[0] key.[1] key.[2] key.[3]
  else round_key_128 (expand_key_128_def key (round - 1)) round

let expand_key_128 = make_opaque expand_key_128_def

#reset-options "--initial_fuel 4 --max_fuel 4 --max_ifuel 0"
let lemma_expand_key_128_0 (key:aes_key_LE AES_128) : Lemma
  (equal key (expand_key AES_128 key 4))
  =
  reveal_opaque expand_key_def

#reset-options "--initial_fuel 1 --max_fuel 1 --max_ifuel 0 --z3rlimit 10"
let lemma_expand_key_128_i (key:aes_key_LE AES_128) (i:nat) : Lemma
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
  =
  reveal_opaque expand_key_def;
  let n = 4 * i in
  // unfold expand_key 4 times (could use fuel, but that unfolds everything):
  let _ = expand_key AES_128 key (n + 1) in
  let _ = expand_key AES_128 key (n + 2) in
  let _ = expand_key AES_128 key (n + 3) in
  ()
#reset-options

// expand_key for large 'size' argument agrees with expand_key for smaller 'size' argument
let rec lemma_expand_append (key:aes_key_LE AES_128) (size1:nat) (size2:nat) : Lemma
  (requires size1 <= size2 /\ size2 <= 44)
  (ensures equal (expand_key AES_128 key size1) (slice (expand_key AES_128 key size2) 0 size1))
  (decreases size2)
  =
  reveal_opaque expand_key_def;
  if size1 < size2 then lemma_expand_append key size1 (size2 - 1)

#reset-options "--z3rlimit 10"
// quad32 key expansion is equivalent to nat32 key expansion
let rec lemma_expand_key_128 (key:aes_key_LE AES_128) (size:nat) : Lemma
  (requires size <= 11)
  (ensures (
    let s = key_schedule_to_round_keys size (expand_key AES_128 key 44) in
    (forall (i:nat).{:pattern (expand_key_128 key i) \/ (expand_key_128_def key i)}
      i < size ==> expand_key_128 key i == s.[i])
  ))
  =
  reveal_opaque expand_key_128_def;
  lemma_expand_append key (4 * size) 44;
  if size = 0 then ()
  else
  (
    let i = size - 1 in
    lemma_expand_append key (4 * i) 44;
    lemma_expand_key_128 key i;
    if i = 0 then lemma_expand_key_128_0 key
    else lemma_expand_key_128_i key i
  )
#reset-options

// Refine round_key_128 to a SIMD computation
let simd_round_key_128 (prev:quad32) (rcon:nat32) : quad32 =
  let r = rot_word_LE (sub_word prev.hi3) *^ rcon in
  let q = prev in
  let q = q *^^ quad32_shl32 q in
  let q = q *^^ quad32_shl32 q in
  let q = q *^^ quad32_shl32 q in
  q *^^ Mkfour r r r r

// SIMD version of round_key_128 is equivalent to scalar round_key_128
#push-options "--max_fuel 3 --initial_fuel 3 --max_ifuel 3 --initial_ifuel 3"  // REVIEW: Why do we need this?
let lemma_simd_round_key (prev:quad32) (rcon:nat32) : Lemma
  (simd_round_key_128 prev rcon == round_key_128_rcon prev rcon)
  =
  reveal_opaque quad32_xor_def;
  reveal_opaque reverse_bytes_nat32_def;  
  commute_rot_word_sub_word prev.hi3;
  Arch.Types.xor_lemmas ()
#pop-options

let commute_sub_bytes_shift_rows_forall () :
  Lemma (forall q . {:pattern sub_bytes (shift_rows_LE q) \/ shift_rows_LE (sub_bytes q) }
         sub_bytes (shift_rows_LE q) == shift_rows_LE (sub_bytes q))
  =
  FStar.Classical.forall_intro commute_sub_bytes_shift_rows
