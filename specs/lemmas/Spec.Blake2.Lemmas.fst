module Spec.Blake2.Lemmas

open Lib.IntTypes

open Spec.Hash.Lemmas
open FStar.Mul

friend Spec.Agile.Hash

#push-options "--fuel 0 --ifuel 0"

module B2 = Spec.Blake2

/// Proving spec equivalence

#push-options "--z3rlimit 10"
(*
let lemma_update_multi_core
  (a:hash_alg{is_blake a})
  (blocks:bytes{Seq.length blocks <= max_input_length a})
  (nb:nat)
  (h:words_state a)
  : Lemma
    (requires snd h == u64 0 /\ Seq.length blocks == nb * block_length a)
    (ensures fst (Spec.Agile.Hash.update_multi a h blocks) ==
             Lib.LoopCombinators.repeati nb (B2.blake2_update1 (to_blake_alg a) 0 blocks) (fst h))
  = admit()


let lemma_blake2_split
  (a:hash_alg{is_blake a})
  (d:bytes{Seq.length d <= max_input_length a})
  (h:words_state a)
  : Lemma
    (let (nb, rem) = B2.split (to_blake_alg a) (Seq.length d) in
     let blocks = Seq.slice d 0 (nb * block_length a) in
     Lib.LoopCombinators.repeati nb (B2.blake2_update1 (to_blake_alg a) 0 d) (fst h) ==
     Lib.LoopCombinators.repeati nb (B2.blake2_update1 (to_blake_alg a) 0 blocks) (fst h))
  = admit()

let lemma_update_multi
  (a:hash_alg{is_blake a})
  (d:bytes{Seq.length d <= max_input_length a})
  (h:words_state a)
  : Lemma
    (requires (snd h) == u64 0)
    (ensures (
      let padding = Spec.Hash.PadFinish.pad a (Seq.length d) in
      fst (Spec.Agile.Hash.update_multi a h (d `Seq.append` padding)) ==
      B2.blake2_update_blocks (to_blake_alg a) 0 d (fst h)))
  = let padding = Spec.Hash.PadFinish.pad a (Seq.length d) in
    let (nb, rem) = B2.split (to_blake_alg a) (Seq.length d) in
    assert (nb * block_length a + rem == Seq.length d);
    let blocks = Seq.slice d 0 (nb * block_length a) in
    let rest = Seq.slice d (nb * block_length a) (Seq.length d) in
    let h_ag1 = Spec.Agile.Hash.update_multi a h blocks in
    let h_ag_f = Spec.Agile.Hash.update_multi a h (d `Seq.append` padding) in
    let h_b1 = Lib.LoopCombinators.repeati nb (B2.blake2_update1 (to_blake_alg a) 0 d) (fst h) in

    let padded_rest = rest `Seq.append` padding in
    assume (Seq.length padded_rest == block_length a);
//    assume (nb * block_length a == Seq.length d - rem);
//    admit()

    let aux1 () : Lemma (h_ag_f == Spec.Agile.Hash.update_multi a h_ag1 padded_rest)
      =
        assert (d `Seq.equal` (blocks `Seq.append` rest));
        Seq.append_assoc blocks rest padding;
        Spec.Hash.Lemmas.update_multi_associative a h blocks padded_rest
        // AF: Using calc as follows here seems to send F* off the rails. Maybe it struggles type-checking at each step?
        //   calc (==) {
        //   h_ag_f <: words_state a;
        //   (==) { }
        //   Spec.Agile.Hash.update_multi a h (d `Seq.append` padding);
        //   (==) { assert (d `Seq.equal` (blocks `Seq.append` rest)) }
        //   Spec.Agile.Hash.update_multi a h ((blocks `Seq.append` rest) `Seq.append` padding);
        //   (==) { Seq.append_assoc blocks rest padding }
        //   Spec.Agile.Hash.update_multi a h (blocks `Seq.append` (rest `Seq.append` padding));
        //   (==) { Spec.Hash.Lemmas.update_multi_associative a h blocks padded_rest }
        //   Spec.Agile.Hash.update_multi a (Spec.Agile.Hash.update_multi a h blocks) padded_rest;
        //   (==) { assert (Spec.Agile.Hash.update_multi a h blocks == h_ag1) }
        //   Spec.Agile.Hash.update_multi a h_ag1 padded_rest;
        // }

    in aux1 ();

    lemma_blake2_split a d h;
    lemma_update_multi_core a blocks nb h;
    assert (B2.blake2_update_blocks (to_blake_alg a) 0 d (fst h) ==
      B2.blake2_update_last (to_blake_alg a) 0 rem d h_b1);

    Spec.Hash.Lemmas.update_multi_update a h_ag1 padded_rest;
    assume (Seq.equal padded_rest (B2.get_last_padded_block (to_blake_alg a) d rem));

    assert (Spec.Agile.Hash.update_multi a h_ag1 padded_rest ==
      Spec.Agile.Hash.update a h_ag1 padded_rest);

    assert (B2.blake2_update_last (to_blake_alg a) 0 rem d (fst h_ag1) ==
    // This is not equal to update. Update is defined as update_block false (Seq.length blocks) padded_rest here...
            B2.blake2_update_block (to_blake_alg a) true (Seq.length d) padded_rest (fst h_ag1));

    admit()

    // assert (B2.blake2_update_last (to_blake_alg a) 0 rem d (fst h_ag1) ==
    //  fst (Spec.Agile.Hash.update_multi a h_ag1 padded_rest))


*)
let lemma_blake2_hash_equivalence
  (a:hash_alg{is_blake a}) (d:bytes{Seq.length d <= max_input_length a})
  : Lemma
    (B2.blake2 (to_blake_alg a) d 0 Seq.empty (B2.max_output (to_blake_alg a)) ==
     Spec.Agile.Hash.hash a d)
  = ()

#pop-options

// AF: These proofs were extremely brittle when trying to do them directly on add_extra_i
// The workaround here is overly verbose, but seems to add stability

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
    let block, rem = Lib.UpdateMulti.split_block (block_length a) input 1 in
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
