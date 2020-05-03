module Spec.Blake2.Lemmas

open Lib.IntTypes

open Spec.Hash.Lemmas
open Lib.UpdateMulti
open FStar.Mul

friend Spec.Agile.Hash

// AF: These proofs were extremely brittle when trying to do them directly on add_extra_i
// The workaround here is overly verbose, but seems to add stability

#push-options "--fuel 0 --ifuel 0"

noextract inline_for_extraction
let add_extra_i (a:hash_alg{is_blake a}) (ev:extra_state a) (i:U32.t) : extra_state a =
    [@inline_let] let s = to_u64 i *. u64 (size_block a) in
    ev +. s

let add_extra_s (a:hash_alg{is_blake a}) (ev:nat) (i:nat) : nat =
  (ev + (i * size_block a)) % pow2 64

let add_s_i (a:hash_alg{is_blake a}) (ev:extra_state a) (i:U32.t) : Lemma
  (v #U64 #SEC (add_extra_i a ev i) == add_extra_s a (v #U64 #SEC ev) (v i))
  = calc (==) {
      v #U64 #SEC (add_extra_i a ev i);
      (==) { }
      v (ev +. (to_u64 i *. u64 (size_block a)));
      (==) { }
      (v #U64 #SEC ev + (v i * size_block a) % pow2 64) % pow2 64;
      (==) { FStar.Math.Lemmas.lemma_mod_add_distr (v #U64 #SEC ev) (v i * size_block a) (pow2 64) }
      (v #U64 #SEC ev + v i * size_block a) % pow2 64;
    }

let add_extra_s_zero (#a:hash_alg{is_blake a}) (ev:extra_state a) : Lemma (add_extra_s a (v #U64 #SEC ev) 0 == v #U64 #SEC ev)
  = ()

let add_extra_i_zero a ev =
    add_s_i a ev 0ul;
    add_extra_s_zero ev

let add_extra_s_assoc (a:hash_alg{is_blake a}) (ev:nat) (i j:nat) : Lemma
  (add_extra_s a (add_extra_s a ev j) i == add_extra_s a ev (i + j))
  = calc (==) {
      add_extra_s a (add_extra_s a ev j) i;
      (==) { }
      ((add_extra_s a ev j) + (i * size_block a)) % pow2 64;
      (==) { }
      ((ev + (j * size_block a)) % pow2 64 + (i * size_block a)) % pow2 64;
      (==) { FStar.Math.Lemmas.lemma_mod_add_distr (i * size_block a)
        (ev + (j * size_block a)) (pow2 64) }
      (ev + i * size_block a + j * size_block a) % pow2 64;
      (==) { FStar.Math.Lemmas.distributivity_add_left i j (size_block a) }
      add_extra_s a ev (i+j);
   }


val lemma_update_s (a:hash_alg{is_blake a}) (h:words_state a) (i:nat) (input: bytes_blocks a) :
  Lemma (requires i + 1 < pow2 32 /\ Seq.length input == i * block_length a)
        (ensures (
          let h' = update_multi a h input in
          v #U64 #SEC (snd h') == add_extra_s a (v #U64 #SEC (snd h)) i))
        (decreases i)


val update1_add (a:hash_alg{is_blake a}) (h:words_state a) (l:bytes{Seq.length l == block_length a})
  : Lemma
  (let h' = update a h l in
   let _, ev = h in
   let _, ev' = h' in
   ev' == add_extra_i a ev 1ul)
let update1_add a h l =
  mul_mod_lemma (to_u64 1ul) (u64 (size_block a))

#restart-solver
#push-options "--fuel 1 --z3rlimit 20"

let rec lemma_update_s a h i input =
  let ev = snd h in
  let h' = update_multi a h input in
  let ev' = snd h' in
  if i = 0 then add_extra_s_zero ev
  else
    let block, rem = split_block (block_length a) input 1 in
    let h_mid = update a h block in
    let h_f = update_multi a h_mid rem in

    let ev_mid = snd h_mid in
    let ev_f = snd h_f in

    calc (==) {
      v #U64 #SEC ev';
      (==) { }
      v #U64 #SEC ev_f;
      (==) { lemma_update_s a h_mid (i-1) rem }
      add_extra_s a (v #U64 #SEC ev_mid) (i-1);
      (==) { update1_add a h block }
      add_extra_s a (v #U64 #SEC (add_extra_i a ev 1ul)) (i-1);
      (==) { calc (==) {
        v #U64 #SEC (add_extra_i a ev 1ul);
        (==) { add_s_i a ev 1ul }
        add_extra_s a (v #U64 #SEC ev) 1;
          }
        }
      add_extra_s a (add_extra_s a (v #U64 #SEC ev) 1) (i-1);
      (==) { add_extra_s_assoc a (v #U64 #SEC ev) (i-1) 1 }
      add_extra_s a (v #U64 #SEC ev) i;
    }

#pop-options


let rec update_multi_add_extra a h i input =
  let ev = snd h in
  let h' = update_multi a h input in
  let ev' = snd h' in
  add_s_i a ev (U32.uint_to_t i);
  lemma_update_s a h i input
#pop-options
