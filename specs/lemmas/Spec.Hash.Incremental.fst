module Spec.Hash.Incremental

module S = FStar.Seq

open Spec.Agile.Hash
open Spec.Hash.Definitions
open Spec.Hash.PadFinish
open FStar.Mul
open Lib.IntTypes

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 300"

let update_last_blake (a:hash_alg{is_blake a})
  (hash:words_state a)
  (prevlen:nat{prevlen % block_length a = 0})
  (input:bytes{S.length input + prevlen <= max_input_length a}):
  Tot (words_state a)
  = let (nb, rem) = Spec.Blake2.split (to_blake_alg a) (S.length input) in
    let blocks = Seq.slice input 0 (nb * block_length a) in
    let (h', totlen) = update_multi a hash blocks in
    let last_block = Spec.Blake2.get_last_padded_block (to_blake_alg a) input rem in
    (Spec.Blake2.blake2_update_block (to_blake_alg a) true (v (totlen +. u64 rem)) last_block h', u64 0)

(* An incremental specification better suited to a stateful API, allowing the
   client to perform the padding at the last minute upon hitting the last chunk of
   data. *)
let update_last (a:hash_alg)
  (hash:words_state a)
  (prevlen:nat{prevlen % block_length a = 0})
  (input:bytes{S.length input + prevlen <= max_input_length a}):
  Tot (words_state a)
=
  if is_blake a then
    update_last_blake a hash prevlen input
  else
  let total_len = prevlen + S.length input in
  let padding = pad a total_len in
  update_multi a hash S.(input @| padding)

let hash_incremental (a:hash_alg) (input:bytes{S.length input <= (max_input_length a)}):
  Tot (hash:bytes{S.length hash = (hash_length a)})
=
  let open FStar.Mul in
  let n = S.length input / (block_length a) in
  // Ensuring that we always handle one block in update_last
  let n = if S.length input % block_length a = 0 && n > 0 then n-1 else n in
  let bs, l = S.split input (n * (block_length a)) in
  let hash = update_multi a (init a) bs in
  let hash = update_last a hash (n * (block_length a)) l in
  finish a hash

let padded_block_modulo (a:hash_alg{is_blake a}) (s1 s2:bytes) (rem:nat{rem <= block_length a}) (n:nat)
  : Lemma (requires S.length s2 == n * block_length a /\ rem <= S.length s1)
          (ensures Spec.Blake2.get_last_padded_block (to_blake_alg a) s1 rem `S.equal`
                   Spec.Blake2.get_last_padded_block (to_blake_alg a) (s2 `S.append` s1) rem)
  = let last1 = Seq.slice s1 (S.length s1 - rem) (S.length s1) in
    let s' = s2 `S.append` s1 in
    let last2 = Seq.slice s' (S.length s' - rem) (S.length s') in
    assert (Seq.equal last1 last2)

let small_update_last_blake
  (a:hash_alg{is_blake a}) (h:words_state a)
  (prevlen:nat{prevlen % block_length a = 0}) (s:bytes)
  : Lemma
    (requires S.length s + prevlen <= max_input_length a /\ S.length s <= block_length a)
    (ensures
      (let last_block = Spec.Blake2.get_last_padded_block (to_blake_alg a) s (S.length s) in
      update_last_blake a h prevlen s ==
      (Spec.Blake2.blake2_update_block (to_blake_alg a) true (v (snd h +. u64 (S.length s))) last_block (fst h), u64 0)))
   = let (nb, rem) = Spec.Blake2.split (to_blake_alg a) (S.length s) in
     let blocks = Seq.slice s 0 (nb * block_length a) in
     let h' = update_multi a h blocks in
//   TODO: Reorganize modules to avoid circular dependencies
//     Spec.Hash.Lemmas.update_multi_zero a h
     assume (h == h')

let blake_split_same_modulo (a:hash_alg{is_blake a}) (len1 len2:nat) (n:nat)
  : Lemma (requires len1 + n * block_length a = len2 /\ len1 > 0)
          (ensures snd (Spec.Blake2.split (to_blake_alg a) len1) ==
                   snd (Spec.Blake2.split (to_blake_alg a) len2))
  = ()

// TODO: Reorganize modules to avoid circular dependencies
let update_multi_associative (a: hash_alg)
  (h: words_state a)
  (input1: bytes_blocks a)
  (input2: bytes_blocks a):
  Lemma (ensures (
    let input = S.append input1 input2 in
    (update_multi a (update_multi a h input1) input2) ==
      (update_multi a h input)))
  = admit()

#push-options "--z3rlimit 2500"

let concatenated_hash_incremental_blake (a:hash_alg{is_blake a}) (inp1:bytes_blocks a) (inp2:bytes)
  : Lemma
    (requires Seq.length (inp1 `S.append` inp2) <= max_input_length a /\ Seq.length inp2 > 0)
    (ensures finish a (update_last_blake a (update_multi a (init a) inp1) (S.length inp1) inp2)
      `S.equal` hash_incremental a (inp1 `S.append` inp2))
  = let open FStar.Mul in
    let h = init a in

    let h1 = update_multi a h inp1 in
    let h2 = update_last_blake a h1 (S.length inp1) inp2 in
    let n = S.length inp2 / (block_length a) in
    let n:nat = if S.length inp2 % block_length a = 0 && n > 0 then n-1 else n in
    let nb, rem = Spec.Blake2.split (to_blake_alg a) (S.length inp2) in

    let bs2, l2 = S.split inp2 (n * block_length a) in

    assert (S.length l2 == S.length inp2 - (n * block_length a));
    let h3 = update_multi a h1 bs2 in

    let input = inp1 `S.append` inp2 in
    let n' = S.length input / (block_length a) in
    let n':nat = if S.length input % block_length a = 0 && n' > 0 then n'-1 else n' in
    blake_split_same_modulo a (S.length inp2) (S.length input) (S.length inp1 / (block_length a));
    let bs, l = S.split input (n' * (block_length a)) in

    assert (l `S.equal` l2);
    assert (bs `S.equal` (inp1 `S.append` bs2));

    update_multi_associative a h inp1 bs2;
    assert (h3 == update_multi a h bs);

    assert (nb == n);

    let h4 = update_last_blake a h3 (S.length inp1 + S.length bs2) l2 in

    let last_block = Spec.Blake2.get_last_padded_block (to_blake_alg a) l2 (S.length l2) in
    padded_block_modulo a l2 bs2 rem n;

    small_update_last_blake a h3 (S.length inp1 + S.length bs2) l2
