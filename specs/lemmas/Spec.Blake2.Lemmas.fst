module Spec.Blake2.Lemmas

open Lib.IntTypes

open Spec.Hash.Lemmas
open Lib.UpdateMulti
open FStar.Mul

friend Spec.Agile.Hash


#push-options "--fuel 0 --ifuel 0"

noextract inline_for_extraction
let add_extra_i (a:hash_alg{is_blake a}) (ev:extra_state a) (i:U32.t) : extra_state a =
  match a with
  | Blake2S ->
    [@inline_let] let s = to_u64 i *. u64 (size_block a) in
    ev +. s
  | Blake2B -> admit()
    // [@inline_let] let s = to_u128 i *. u128 (size_block a) in
    // ev +. s

let add_extra_s (a:hash_alg{is_blake a}) (ev:nat) (i:nat) : nat =
  match a with
  | Blake2S -> (ev + (i * size_block a)) % pow2 64
  | Blake2B -> admit()

let add_s_i_2s (ev:extra_state Blake2S) (i:U32.t) : Lemma
  (v (add_extra_i Blake2S ev i) == add_extra_s Blake2S (v ev) (v i))
  = calc (==) {
      v (add_extra_i Blake2S ev i);
      (==) { }
      v (ev +. (to_u64 i *. u64 (size_block Blake2S)));
      (==) { }
      (v ev + (v i * size_block Blake2S) % pow2 64) % pow2 64;
      (==) { FStar.Math.Lemmas.lemma_mod_add_distr (v ev) (v i * size_block Blake2S) (pow2 64) }
      (v ev + v i * size_block Blake2S) % pow2 64;
    }

let add_extra_s_zero_2s (ev:extra_state Blake2S) : Lemma (add_extra_s Blake2S (v ev) 0 == v ev)
  = ()

let add_extra_i_zero a ev = match a with
  | Blake2S ->
    add_s_i_2s ev 0ul;
    add_extra_s_zero_2s ev

  | Blake2B -> admit()

let add_extra_s_assoc_2s (ev:nat) (i j:nat) : Lemma
  (add_extra_s Blake2S (add_extra_s Blake2S ev j) i == add_extra_s Blake2S ev (i + j))
  = calc (==) {
      add_extra_s Blake2S (add_extra_s Blake2S ev j) i;
      (==) { }
      ((add_extra_s Blake2S ev j) + (i * size_block Blake2S)) % pow2 64;
      (==) { }
      ((ev + (j * size_block Blake2S)) % pow2 64 + (i * size_block Blake2S)) % pow2 64;
      (==) { FStar.Math.Lemmas.lemma_mod_add_distr (i * size_block Blake2S)
        (ev + (j * size_block Blake2S)) (pow2 64) }
      (ev + i * size_block Blake2S + j * size_block Blake2S) % pow2 64;
      (==) { FStar.Math.Lemmas.distributivity_add_left i j (size_block Blake2S) }
      add_extra_s Blake2S ev (i+j);
   }


val aux_2s (h:words_state Blake2S) (i:nat) (input: bytes_blocks Blake2S) :
  Lemma (requires i + 1 < pow2 32 /\ Seq.length input == i * block_length Blake2S)
        (ensures (
          let h' = update_multi Blake2S h input in
          v (snd h') == add_extra_s Blake2S (v (snd h)) i))
        (decreases i)


val update1_add (h:words_state Blake2S) (l:bytes{Seq.length l == block_length Blake2S})
  : Lemma
  (let h' = update Blake2S h l in
   let _, ev = h in
   let _, ev' = h' in
   ev' == add_extra_i Blake2S ev 1ul)
let update1_add h l =
  mul_mod_lemma (to_u64 1ul) (u64 (size_block Blake2S))

#restart-solver
#push-options "--fuel 1 --z3rlimit 20"

let rec aux_2s h i input =
  let ev = snd h in
  let h' = update_multi Blake2S h input in
  let ev' = snd h' in
  if i = 0 then add_extra_s_zero_2s ev
  else
    let block, rem = split_block (block_length Blake2S) input 1 in
    let h_mid = update Blake2S h block in
    let h_f = update_multi Blake2S h_mid rem in

    let ev_mid = snd h_mid in
    let ev_f = snd h_f in

    calc (==) {
      v ev';
      (==) { }
      v ev_f;
      (==) { aux_2s h_mid (i-1) rem }
      add_extra_s Blake2S (v ev_mid) (i-1);
      (==) { update1_add h block }
      add_extra_s Blake2S (v (add_extra_i Blake2S ev 1ul)) (i-1);
      (==) { calc (==) {
        v (add_extra_i Blake2S ev 1ul);
        (==) { add_s_i_2s ev 1ul }
        add_extra_s Blake2S (v ev) 1;
          }
        }
      add_extra_s Blake2S (add_extra_s Blake2S (v ev) 1) (i-1);
      (==) { add_extra_s_assoc_2s (v ev) (i-1) 1 }
      add_extra_s Blake2S (v ev) i;
    }

#pop-options


let rec update_multi_add_extra a h i input =
  let ev = snd h in
  let h' = update_multi a h input in
  let ev' = snd h' in
  match a with
  | Blake2S ->
    add_s_i_2s ev (U32.uint_to_t i);
    aux_2s h i input

  | Blake2B -> admit()

#pop-options
