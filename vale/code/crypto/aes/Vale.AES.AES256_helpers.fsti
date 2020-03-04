module Vale.AES.AES256_helpers

open FStar.Mul
open Vale.Def.Opaque_s
open Vale.Def.Words_s
open Vale.Arch.Types
open Vale.Def.Types_s
open FStar.Seq
open Vale.AES.AES_s

// syntax for seq accesses, s.[index] and s.[index] <- value
unfold let (.[]) (#a:Type) (s:seq a) (i:nat{ i < length s}) : Tot a = index s i
unfold let (.[]<-) = Seq.upd

unfold let ( *^ ) = nat32_xor
unfold let ( *^^ ) = quad32_xor

let quad32_shl32 (q:quad32) : quad32 =
  let Mkfour v0 v1 v2 v3 = q in
  Mkfour 0 v0 v1 v2

let make_AES256_key (k0 k1:quad32) : Pure (seq nat32)
  (requires True)
  (ensures fun key -> is_aes_key_LE AES_256 key)
  =
  append (quad32_to_seq k0) (quad32_to_seq k1)

// Redefine key expansion in terms of quad32 values rather than nat32 values,
// then prove both definitions are equivalent.

let round_key_256_rcon (prev0 prev1:quad32) (rcon:nat32) (round:int) : quad32 =
  let Mkfour v0 v1 v2 v3 = prev0 in
  let Mkfour _  _  _  v7 = prev1 in
  let c1 = if round % 2 = 0 then sub_word (rot_word_LE v7) *^ rcon else sub_word v7 in
  let w0 = v0 *^ c1 in
  let w1 = v1 *^ w0 in
  let w2 = v2 *^ w1 in
  let w3 = v3 *^ w2 in
  Mkfour w0 w1 w2 w3

let round_key_256 (prev0 prev1:quad32) (round:nat) : quad32 =
  round_key_256_rcon prev0 prev1 (aes_rcon (round / 2 - 1)) round

let rec expand_key_256_def (key:seq nat32) (round:nat) : Pure quad32
  (requires is_aes_key_LE AES_256 key)
  (ensures fun _ -> True)
  =
  if round = 0 then Mkfour key.[0] key.[1] key.[2] key.[3]
  else if round = 1 then Mkfour key.[4] key.[5] key.[6] key.[7]
  else round_key_256 (expand_key_256_def key (round - 2)) (expand_key_256_def key (round - 1)) round
[@"opaque_to_smt"] let expand_key_256 = opaque_make expand_key_256_def
irreducible let expand_key_256_reveal = opaque_revealer (`%expand_key_256) expand_key_256 expand_key_256_def

// quad32 key expansion is equivalent to nat32 key expansion
val lemma_expand_key_256 (key:seq nat32) (size:nat) : Lemma
  (requires size <= 15 /\ is_aes_key_LE AES_256 key)
  (ensures (
    let s = key_schedule_to_round_keys size (expand_key AES_256 key 60) in
    (forall (i:nat).{:pattern (expand_key_256 key i)} i < size ==> expand_key_256 key i == s.[i])
  ))

// Refine round_key_256 to a SIMD computation
let simd_round_key_256 (prev0 prev1:quad32) (rcon:nat32) (round:int) : quad32 =
  let r = if round % 2 = 0 then rot_word_LE (sub_word prev1.hi3) *^ rcon else sub_word prev1.hi3 in
  let q = prev0 in
  let q = q *^^ quad32_shl32 q in
  let q = q *^^ quad32_shl32 q in
  let q = q *^^ quad32_shl32 q in
  q *^^ Mkfour r r r r

// SIMD version of round_key_256 is equivalent to scalar round_key_256
val lemma_simd_round_key (prev0 prev1:quad32) (rcon:nat32) (round:int) : Lemma
  (simd_round_key_256 prev0 prev1 rcon round == round_key_256_rcon prev0 prev1 rcon round)

val lemma_round_key_256_rcon_odd (prev0 prev1:quad32) (rcon:nat32) (round:int) : Lemma
  (requires ~(round % 2 == 0))
  (ensures round_key_256_rcon prev0 prev1 rcon round == round_key_256_rcon prev0 prev1 0 round)
