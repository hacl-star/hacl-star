module Spec.Hash.Incremental

module S = FStar.Seq

open Spec.Hash.Definitions
open Spec.Hash.PadFinish
open Spec.Hash.Lemmas

friend Spec.Agile.Hash

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 50"

open FStar.Tactics
open FStar.Mul
open Spec.Blake2
module Loops = Lib.LoopCombinators

/// TODO: I don't find this lemma in Lib, and the below proofs don't work if
/// I don't prove this step separately.
let add_v_eq (a b : nat) :
  Lemma
  (requires (a + b <= pow2 64 - 1))
  (ensures (v (u64 a +. u64 b) == a + b)) = ()

/// The [repeati_blake2_update1_as_update_multi_eq] lemma is not fundamentally difficult, but
/// the proof time/success rate can be very random, probably because of modular
/// arithmetic. For this reason, we cut it into small pieces.
let update_multi_one_block_eq
  (a:hash_alg{is_blake a})
  (block : bytes_block a)
  (hash : words_state' a) 
  (totlen : nat{(totlen + block_length a) <= pow2 64 - 1}) :
  Lemma
  (ensures (
    let totlen' = totlen + block_length a in
    update_multi a (hash, u64 totlen) block ==
    (blake2_update_block (to_blake_alg a) false totlen'
                         block hash,
     u64 totlen'))) =
  let s = (hash, u64 totlen) in
  let totlen' = u64 (totlen + block_length a) in
  add_v_eq totlen (block_length a);
  assert(totlen' == u64 totlen +. u64 (block_length a));
  let block1, block2 = Lib.UpdateMulti.split_block (block_length a) block 1 in
  assert(block2 `S.equal` S.empty);
  assert(block1 `S.equal` block);
  calc (==) {
    update_multi a s block;
  (==) {}
    update_multi a (Spec.Agile.Hash.update a s block1) block2;
  (==) { update_multi_zero a (Spec.Agile.Hash.update a s block1) }
    Spec.Agile.Hash.update a s block;
  };
  (* TODO: doesn't succeed if I merge this assert with the calc above *)
  assert(
    Spec.Agile.Hash.update a s block ==
    ((blake2_update_block (to_blake_alg a) false (v #U64 #SEC totlen')
                          block hash,
     totlen')))

let repeati_blake2_update1_eq 
  (a:hash_alg{is_blake a})
  (nb prev : nat)
  (d : bytes)
  (hash : words_state' a) :
  Lemma
  (requires (
    nb > 0 /\
    nb * block_length a <= Seq.length d /\
    prev + nb * block_length a <= max_limb (to_blake_alg a) /\
    nb <= Seq.length d / size_block (to_blake_alg a) /\
    prev + Seq.length d <= max_limb (to_blake_alg a) /\
    prev + nb * block_length a <= pow2 64 - 1
  ))
  (ensures (
    let update1 = blake2_update1 (to_blake_alg a) prev d in
    let block = S.slice d ((nb-1) * block_length a) (nb * block_length a) in
    Loops.repeati nb update1 hash ==
    blake2_update_block (to_blake_alg a) false (prev + nb * block_length a)
                        block (Loops.repeati (nb-1) update1 hash)
  )) =
  let update1 = blake2_update1 (to_blake_alg a) prev d in
  let block = S.slice d ((nb-1) * block_length a) (nb * block_length a) in
  Loops.unfold_repeati nb update1 hash (nb - 1)

/// TODO: the time spent on this proof is super random.
#push-options "--z3rlimit 500 --fuel 1"
let rec repeati_blake2_update1_as_update_multi_eq
  (a:hash_alg{is_blake a}) (nb prev : nat)
  (d : bytes)
  (hash : words_state' a) :
  Lemma
  (requires (
    nb * block_length a <= Seq.length d /\
    prev + nb * block_length a <= max_limb (to_blake_alg a) /\
    nb <= Seq.length d / size_block (to_blake_alg a) /\
    prev + Seq.length d <= max_limb (to_blake_alg a) /\
    prev + nb * block_length a <= pow2 64 - 1
  ))
  (ensures (
    let blocks, _ = Seq.split d (nb * block_length a) in
    (Loops.repeati nb (blake2_update1 (to_blake_alg a) prev d) hash,
     u64 (prev + nb * block_length a)) ==
    update_multi a (hash, u64 prev) blocks)) =
  let update1 = blake2_update1 (to_blake_alg a) prev d in
  let blocks, _ = Seq.split d (nb * block_length a) in
  assert(Seq.length blocks == nb * block_length a);
  Math.Lemmas.multiple_modulo_lemma nb (block_length a);
  if nb = 0 then
    Loops.eq_repeati0 nb update1 hash
  else
    begin
    repeati_blake2_update1_eq a nb prev d hash;
    (**)
    let blocks1, blocks2 = Seq.split blocks ((nb-1) * block_length a) in
    assert(blocks `S.equal` S.append blocks1 blocks2);
    assert(Seq.length blocks1 == (nb - 1) * block_length a);
    Math.Lemmas.multiple_modulo_lemma (nb-1) (block_length a);
    assert(Seq.length blocks2 == 1 * block_length a);
    Math.Lemmas.multiple_modulo_lemma 1 (block_length a);
    update_multi_associative a (hash, u64 prev) blocks1 blocks2;
    let s2 = update_multi a (hash, u64 prev) blocks1 in
    assert(
      update_multi a (hash, u64 prev) blocks ==
      update_multi a s2 blocks2);
    repeati_blake2_update1_as_update_multi_eq a (nb - 1) prev d hash;
    assert(blocks1 `S.equal` Seq.slice d 0 ((nb-1) * block_length a));
    assert(
      s2 == (Loops.repeati (nb-1) update1 hash, u64 (prev + (nb-1) * block_length a)));
    update_multi_one_block_eq a blocks2 (fst s2) (v #U64 #SEC (snd s2))
    end
#pop-options

/// Once again, proof times are random...
(* let blake2_no_finish_no_last
  (a:hash_alg{is_blake a}) (input:bytes{Seq.length input <= max_input_length a}) =
  let nn = Spec.Blake2.max_output (to_blake_alg a) in
  let prev0 = compute_prev0 (to_blake_alg a) 0 in
  let s1 = blake2_init (to_blake_alg a) 0 Seq.empty nn in
  let (nb,rem) = split (to_blake_alg a) (S.length input) in
  let s2 = Loops.repeati nb (blake2_update1 (to_blake_alg a) prev0 input) s1 in
  s2

let blake2_ihash_no_finish_no_last
  (a:hash_alg{is_blake a}) (input:bytes{Seq.length input <= max_input_length a}) =
  let bs, l = split_blocks a input in
  let is1 = init a in
  let is2 = update_multi a is1 bs in
  is2 *)

let blake2_no_finish
  (a:hash_alg{is_blake a}) (input:bytes{Seq.length input <= max_input_length a}) =
  let nn = Spec.Blake2.max_output (to_blake_alg a) in
  let prev0 = compute_prev0 (to_blake_alg a) 0 in
  let s1 = blake2_init (to_blake_alg a) 0 Seq.empty nn in
  let (nb,rem) = split (to_blake_alg a) (S.length input) in
  let s2 = Loops.repeati nb (blake2_update1 (to_blake_alg a) prev0 input) s1 in
  let s3 = blake2_update_last (to_blake_alg a) prev0 rem input s2 in
  s3

let blake2_ihash_no_finish
  (a:hash_alg{is_blake a}) (input:bytes{Seq.length input <= max_input_length a}) =
  let bs, l = split_blocks a input in
  let is1 = init a in
  let is2 = update_multi a is1 bs in
  let is3 = update_last a is2 (S.length bs) l in
  is3


(* TODO HERE *)
/// Sanity check
#push-options "--z3rlimit 500 --fuel 0 --ifuel 0"
let blake2_is_hash_incremental_aux
  (a:hash_alg{is_blake a}) (input:bytes{Seq.length input <= max_input_length a})
  : Lemma
    (blake2_no_finish a input == fst (blake2_ihash_no_finish a input))
  =
  (* Let's prove the equality step by step *)
  (**)
  let nn = Spec.Blake2.max_output (to_blake_alg a) in
  let prev0 = compute_prev0 (to_blake_alg a) 0 in
  let s1 = blake2_init (to_blake_alg a) 0 Seq.empty nn in
  let (nb,rem) = split (to_blake_alg a) (S.length input) in
  let s2 = Loops.repeati nb (blake2_update1 (to_blake_alg a) prev0 input) s1 in
  let s3 = blake2_update_last (to_blake_alg a) prev0 rem input s2 in
  (**)
  let bs, l = split_blocks a input in
  let is1 = init a in
  let is2 = update_multi a is1 bs in
  let is3 = update_last a is2 (S.length bs) l in
  (* [s1 == fst is1] *)
  assert(s1 == fst is1);
  (* [s2 == fst is2] *)
  assert(S.length bs == nb * block_length a);
  assert(
    nb * block_length a <= Seq.length input /\
    prev0 + nb * block_length a <= max_limb (to_blake_alg a) /\
    nb <= Seq.length input / size_block (to_blake_alg a) /\
    prev0 + Seq.length input <= max_limb (to_blake_alg a) /\
    prev0 + nb * block_length a <= pow2 64 - 1);
  repeati_blake2_update1_as_update_multi_eq a nb prev0 input s1;  
  assert(s2 == fst is2);
  (* [s3 == fst is3] *)
  (* First, work on [s3] *)
  assert(rem == S.length input - S.length bs);
  assert(l `S.equal` S.slice input (S.length input - rem) (S.length input));
  let pblock1 = get_last_padded_block (to_blake_alg a) input rem in
//  assert(
//    forall (i:nat{i < S.length l}). S.index pblock1 i == S.index l i);
//  assert(
//    forall (i:nat{S.length l <= i /\ i < block_length a}).
//      S.index pblock1 i == S.index (S.create (block_length a) (u8 0)) i);
  assume(
    get_last_padded_block (to_blake_alg a) input rem `S.equal`
      Seq.append l (S.create (block_length a - S.length l) (u8 0)));
  assert(
    s3 == blake2_update_block (to_blake_alg a) true (S.length input) pblock1 s2);
  (* Then, work on [is3] *)
  assert(
    is3 == update_last_blake a is2 (S.length bs) l);
  let blocks, last_block, rem' = last_split_blake a l in
  assert(
    blocks == S.empty /\
    last_block == Spec.Blake2.get_last_padded_block (to_blake_alg a) l rem /\
    rem' = S.length l);
//  assert(
//    last_split_blake a l ==
//    (S.empty, Spec.Blake2.get_last_padded_block (to_blake_alg a) l rem, S.length l));
  let h' = update_multi a is2 S.empty in
  update_multi_zero a is2;
  assert(h' == is2);
  assert(snd h' == u64 (S.length bs));
  assume(v (snd h' +. u64 rem) == S.length input);
  assert(
    is3 ==
    (Spec.Blake2.blake2_update_block (to_blake_alg a) true (v (snd h' +. u64 rem))
                                     last_block (fst h'),
     u64 0));
  (* Prove the final equality *)
  assert(s3 == fst is3)

(*
let split (a:alg) (len:nat)
  : nb_rem:(nat & nat){let (nb,rem) = nb_rem in
		   nb * size_block a + rem == len} =
  let nb = len / size_block a in
  let rem = len % size_block a in
  let nb' = if rem = 0 && nb > 0 then nb - 1 else nb in
  let rem' = if rem = 0 && nb > 0 then size_block a else rem in
  (nb',rem')

let last_split_blake (a:hash_alg{is_blake a}) (input:bytes)
  : Pure (bytes & bytes & nat)
    (requires True)
    (ensures fun (b, l, rem) ->
      S.length b % block_length a == 0 /\
      S.length l == block_length a /\
      rem <= block_length a /\
      rem <= S.length input)
  = let (nb, rem) = Spec.Blake2.split (to_blake_alg a) (S.length input) in
    let blocks = Seq.slice input 0 (nb * block_length a) in
    let last_block = Spec.Blake2.get_last_padded_block (to_blake_alg a) input rem in
    blocks, last_block, rem

let update_last_blake (a:hash_alg{is_blake a})
  (hash:words_state a)
  (prevlen:nat{prevlen % block_length a = 0})
  (input:bytes{S.length input + prevlen <= max_input_length a}):
  Tot (words_state a)
  = let blocks, last_block, rem = last_split_blake a input in
    let h' = update_multi a hash blocks in
    (Spec.Blake2.blake2_update_block (to_blake_alg a) true (v (snd h' +. u64 rem)) last_block (fst h'), u64 0)


  assert(
    is3 == update_last_blake a is2 (S.length bs) l);
  assert(
    last_split_blake a l ==
      bs, 
  admit()

  assert(
    let last_pblock = Spec.Blake2.get_last_padded_block (to_blake_alg a) input rem in
    last_split_blake a is2 (S.length bs) l == bs, last_pblock, rem

let blake2_update_last a prev rem m s =
  let inlen = length m in
  let totlen = prev + inlen in
  let last_block = get_last_padded_block a m rem in
  blake2_update_block a true totlen last_block s (**)

let get_last_padded_block (a:alg) (m:bytes)
    (rem:nat{rem <= length m /\ rem <= size_block a}) : block_s a =
  let last = Seq.slice m (length m - rem) (length m) in
  let last_block = create (size_block a) (u8 0) in
  let last_block = update_sub last_block 0 rem last in
  last_block

(**)

let update_last (a:hash_alg)
  (hash:words_state a)
  (prevlen:nat{prevlen % block_length a = 0})
  (input:bytes{S.length input + prevlen <= max_input_length a}):
  Tot (words_state a)
=
    update_last_blake a hash prevlen input


let last_pblock = Spec.Blake2.get_last_padded_block (to_blake_alg a) input rem in
update_last_blake == bs, last_pblock, rem
                     

  assert(s3 == is3)
#pop-options


/// Sanity check
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let blake2_init_eq
  (a:hash_alg{is_blake a}) (input:bytes{Seq.length input <= max_input_length a})
  : Lemma (
      (**)
      let nn = Spec.Blake2.max_output (to_blake_alg a) in
      let prev0 = compute_prev0 (to_blake_alg a) 0 in
      let s1 = blake2_init (to_blake_alg a) 0 Seq.empty nn in
      (**)
      let bs, l = split_blocks a input in
      let is1 = init a in
      (**)
      s1 == fst is1)
  = ()
#pop-options

/// Sanity check
#push-options "--z3rlimit 500 --fuel 0 --ifuel 0"
let blake2_is_hash_incremental_aux
  (a:hash_alg{is_blake a}) (input:bytes{Seq.length input <= max_input_length a})
  : Lemma
    (requires (blake2_no_finish a input == fst (blake2_ihash_no_finish a input)))
    (ensures (
      Spec.Blake2.blake2 (to_blake_alg a) input 0 Seq.empty
                        (Spec.Blake2.max_output (to_blake_alg a)) ==
      hash_incremental a input))
  = ()
#pop-options

/// It is enough to prove the requirement of the above lemma
let blake2_no_finish_eq
  (a:hash_alg{is_blake a}) (input:bytes{Seq.length input <= max_input_length a}) :
  Lemma(blake2_no_finish a input == fst (blake2_ihash_no_finish a input)) =
  (**)
  let nn = Spec.Blake2.max_output (to_blake_alg a) in
  let prev0 = compute_prev0 (to_blake_alg a) 0 in
  let s1 = blake2_init (to_blake_alg a) 0 Seq.empty nn in
  let (nb,rem) = split (to_blake_alg a) (S.length input) in
  let s2 = Loops.repeati nb (blake2_update1 (to_blake_alg a) prev0 input) s1 in
  (**)
  let bs, l = split_blocks a input in
  let is1 = init a in
  let is2 = update_multi a is1 bs in
  let is3 = update_last a is2 (S.length bs) l in
  (**)
  
  

let blake2_no_finish
  (a:hash_alg{is_blake a}) (input:bytes{Seq.length input <= max_input_length a}) =
  let nn = Spec.Blake2.max_output (to_blake_alg a) in
  let prev0 = compute_prev0 (to_blake_alg a) 0 in
  let s1 = blake2_init (to_blake_alg a) 0 Seq.empty nn in
  let (nb,rem) = split (to_blake_alg a) (S.length input) in
  let s2 = Loops.repeati nb (blake2_update1 (to_blake_alg a) prev0 input) s1 in
  let s3 = blake2_update_last (to_blake_alg a) prev0 rem input s2 in
  s3

let blake2_ihash_no_finish
  (a:hash_alg{is_blake a}) (input:bytes{Seq.length input <= max_input_length a}) =
  let bs, l = split_blocks a input in
  let is1 = init a in
  let is2 = update_multi a is1 bs in
  let is3 = update_last a is2 (S.length bs) l in
  is3


#push-options "--z3rlimit 500 --fuel 0 --ifuel 0"
let blake2_is_hash_incremental
  (a:hash_alg{is_blake a}) (input:bytes{Seq.length input <= max_input_length a})
  : Lemma
    (Spec.Blake2.blake2 (to_blake_alg a) input 0 Seq.empty
                        (Spec.Blake2.max_output (to_blake_alg a)) ==
     hash_incremental a input)
  =
  (* Different steps for original blake spec *)
  let nn = Spec.Blake2.max_output (to_blake_alg a) in
  let prev0 = compute_prev0 (to_blake_alg a) 0 in
  let s1 = blake2_init (to_blake_alg a) 0 Seq.empty nn in
//  let s2 = blake2_update_blocks (to_blake_alg a) prev0 input s1 in
  let (nb,rem) = split (to_blake_alg a) (S.length input) in
  let s2 = Loops.repeati nb (blake2_update1 (to_blake_alg a) prev0 input) s1 in
  let s3 = blake2_update_last (to_blake_alg a) prev0 rem input s2 in
  let s3' = blake2_update_blocks (to_blake_alg a) prev0 input s1 in
  assume(s3' == s3);
  let s4 = blake2_finish (to_blake_alg a) s3 nn in
  let s4' = Spec.Blake2.blake2 (to_blake_alg a) input 0 Seq.empty
                               (Spec.Blake2.max_output (to_blake_alg a)) in
  assume(s4 == s4');
  (* Different steps for blake incremental *)
  let bs, l = split_blocks a input in
  let is1 = init a in
  assume(S.length bs % block_length a == 0);
  let is2 = update_multi a is1 bs in
//  assume(S.length bs % block_length a == 0);
  let is3 = update_last a is2 (S.length bs) l in (**)
  let is4 = finish a is3 in
  let is4' = hash_incremental a input in
  assume(is4' == is4);
  (* Let's show that is2 == s3 (suffices to prove the goal) *)
  assume(fst is3 == s3)
#pop-options

#push-options "--z3rlimit 1000"
let blake2_is_hash_incremental
  (a:hash_alg{is_blake a}) (input:bytes{Seq.length input <= max_input_length a})
  : Lemma
    (Spec.Blake2.blake2 (to_blake_alg a) input 0 Seq.empty
                        (Spec.Blake2.max_output (to_blake_alg a)) ==
     hash_incremental a input)
  =
  (* Different steps for original blake spec *)
  let nn = Spec.Blake2.max_output (to_blake_alg a) in
  let prev0 = compute_prev0 (to_blake_alg a) 0 in
  let s1 = blake2_init (to_blake_alg a) 0 Seq.empty nn in
  let s2 = blake2_update_blocks (to_blake_alg a) prev0 input s1 in
//  let (nb,rem) = split (to_blake_alg a) (S.length input) in
//  let s2 = Loops.repeati nb (blake2_update1 (to_blake_alg a) prev0 input) s1 in
//  let s3 = blake2_update_last (to_blake_alg a) prev0 rem input s2 in
//  let s3' = blake2_update_blocks (to_blake_alg a) prev0 input s1 in
//  assert(s3' == s3);
  let s4 = blake2_finish (to_blake_alg a) s2 nn in
  let s4' = Spec.Blake2.blake2 (to_blake_alg a) input 0 Seq.empty
                               (Spec.Blake2.max_output (to_blake_alg a)) in
  assert(s4 == s4');
  (* Different steps for blake incremental *)
  let bs, l = split_blocks a input in
  let is1 = update_multi a (init a) bs in
  let is2 = update_last a is1 (S.length bs) l in
  let is3 = finish a is2 in
  let is3' = hash_incremental a input in
  assert(is3' == is3);
  (* Let's show that is2 == s3 (suffices to prove the goal) *)
  assume(fst is2 == s2)
#pop-options


let hash_incremental (a:hash_alg) (input:bytes{S.length input <= (max_input_length a)}):
  Tot (hash:bytes{S.length hash = (hash_length a)})
=
  let bs, l = split_blocks a input in
  let hash = update_multi a (init a) bs in
  let hash = update_last a hash (S.length bs) l in
  finish a hash
  


  let open FStar.Mul in
  let n = S.length input / block_length a in
  let n = if S.length input % block_length a = 0 && n > 0 then n-1 else n in
  let padding = pad a (S.length input) in
  let padded_d = input `S.append` padding in
  let blocks, rest = Lib.UpdateMulti.split_block (block_length a) padded_d n in
  let blocks', rest' = S.split input (n * block_length a) in
  S.lemma_eq_intro blocks blocks';
  S.lemma_eq_intro (rest' `S.append` padding) rest;
  Math.Lemmas.multiple_modulo_lemma n (block_length a);
  S.lemma_eq_intro padded_d (blocks `S.append` rest);
  update_multi_associative a (init a) blocks rest;
  S.lemma_eq_intro (fst (update_multi a (init a) padded_d)) (fst (update_multi a (update_multi a (init a) blocks) rest));
  assert(
      let kk = 0 in
      let k = Seq.empty in
      let d = input in
      let nn = Spec.Blake2.max_output (to_blake_alg a) in
      let prev0 = Spec.Blake2.compute_prev0 (to_blake_alg a) kk in
      let s = Spec.Blake2.blake2_init (to_blake_alg a) kk k nn in
      (**)
      s == fst (init a));
  assert(
    let bs, l = split_blocks a input in
    let hash0 = update_multi a (init a) bs in
    update_last a hash0 (S.length bs) l ==
      update_last_blake a hash0 (S.length bs) l);
  let (nb,rem) = split (to_blake_alg a) (Seq.length input) in
  let s0 = init a in
  let hash : words_state' a = fst s0 in
  let prev = v #U64 #SEC (snd s0) in
//  let s = repeati nb (blake2_update1 a prev m) s in
  assume(
    nb * block_length a <= Seq.length input /\
    prev + nb * block_length a <= max_limb (to_blake_alg a) /\
    nb < Seq.length input / size_block (to_blake_alg a) /\
    prev + Seq.length input <= max_limb (to_blake_alg a) /\
    prev + nb * block_length a <= pow2 64 - 1);
  repeati_blake2_update1_as_update_multi_eq a nb prev input hash


#push-options "--z3rlimit 1000"
let blake2_is_hash_incremental
  (a:hash_alg{is_blake a}) (input:bytes{Seq.length input <= max_input_length a})
  : Lemma
    (Spec.Blake2.blake2 (to_blake_alg a) input 0 Seq.empty
                        (Spec.Blake2.max_output (to_blake_alg a)) ==
     hash_incremental a input)
  =
  let open FStar.Mul in
  let n = S.length input / block_length a in
  let n = if S.length input % block_length a = 0 && n > 0 then n-1 else n in
  let padding = pad a (S.length input) in
  let padded_d = input `S.append` padding in
  let blocks, rest = Lib.UpdateMulti.split_block (block_length a) padded_d n in
  let blocks', rest' = S.split input (n * block_length a) in
  S.lemma_eq_intro blocks blocks';
  S.lemma_eq_intro (rest' `S.append` padding) rest;
  Math.Lemmas.multiple_modulo_lemma n (block_length a);
  S.lemma_eq_intro padded_d (blocks `S.append` rest);
  update_multi_associative a (init a) blocks rest;
  S.lemma_eq_intro (fst (update_multi a (init a) padded_d)) (fst (update_multi a (update_multi a (init a) blocks) rest));
  assert(
      let kk = 0 in
      let k = Seq.empty in
      let d = input in
      let nn = Spec.Blake2.max_output (to_blake_alg a) in
      let prev0 = Spec.Blake2.compute_prev0 (to_blake_alg a) kk in
      let s = Spec.Blake2.blake2_init (to_blake_alg a) kk k nn in
      (**)
      s == fst (init a));
  assert(
    let bs, l = split_blocks a input in
    let hash0 = update_multi a (init a) bs in
    update_last a hash0 (S.length bs) l ==
      update_last_blake a hash0 (S.length bs) l);
  let (nb,rem) = split (to_blake_alg a) (Seq.length input) in
  let s0 = init a in
  let hash : words_state' a = fst s0 in
  let prev = v #U64 #SEC (snd s0) in
//  let s = repeati nb (blake2_update1 a prev m) s in
  assume(
    nb * block_length a <= Seq.length input /\
    prev + nb * block_length a <= max_limb (to_blake_alg a) /\
    nb < Seq.length input / size_block (to_blake_alg a) /\
    prev + Seq.length input <= max_limb (to_blake_alg a) /\
    prev + nb * block_length a <= pow2 64 - 1);
  repeati_blake2_update1_as_update_multi_eq a nb prev input hash

repeati_blake2_update1_as_update_multi_eq
  (a:hash_alg{is_blake a}) (nb prev : nat)
  (d : bytes)
  (hash : words_state' a) :
  Lemma
  (requires (
    nb * block_length a <= Seq.length d /\
    prev + nb * block_length a <= max_limb (to_blake_alg a) /\
    nb < Seq.length d / size_block (to_blake_alg a) /\
    prev + Seq.length d <= max_limb (to_blake_alg a) /\
    prev + nb * block_length a <= pow2 64 - 1
  ))
  (ensures (
    let blocks, _ = Seq.split d (nb * block_length a) in
    (Loops.repeati nb (blake2_update1 (to_blake_alg a) prev d) hash,
     u64 (prev + nb * block_length a)) ==
    update_multi a (hash, u64 prev) blocks)) =

  
let blake2_update_blocks a prev m s =
  let (nb,rem) = split a (length m) in
  let s = repeati nb (blake2_update1 a prev m) s in
  blake2_update_last a prev rem m s
  


  assume(
      let kk = 0 in
      let k = Seq.empty in
      let d = input in
      let nn = Spec.Blake2.max_output (to_blake_alg a) in
      let prev0 = Spec.Blake2.compute_prev0 (to_blake_alg a) kk in
      let s = Spec.Blake2.blake2_init (to_blake_alg a) kk k nn in
      let s = Spec.Blake2.blake2_update_blocks (to_blake_alg a) prev0 d s in
      (**)
      let bs, l = split_blocks a input in
      let hash = update_multi a (init a) bs in
      let hash = update_last a hash (S.length bs) l in
      s == fst hash);
  admit()

      let s = Spec.Blake2.blake2_init (to_blake_alg a) kk k nn in
      let s = Spec.Blake2.blake2_update_blocks (to_blake_alg a) prev0 d s in

let blake2_update_blocks a prev m s =
  let (nb,rem) = split a (length m) in
  let s = repeati nb (blake2_update1 a prev m) s in
  blake2_update_last a prev rem m s





    let hash = hash0 in
    let prevlen = S.length bs in
    let input = l in
    let blocks, last_block, rem = last_split_blake a input in
    let h' = update_multi a hash blocks in
    hash1 == (Spec.Blake2.blake2_update_block (to_blake_alg a) true (v (snd h' +. u64 rem)) last_block (fst h'), u64 0));
  admit()
  finish a hash

let update_last_blake (a:hash_alg{is_blake a})
  (hash:words_state a)
  (prevlen:nat{prevlen % block_length a = 0})
  (input:bytes{S.length input + prevlen <= max_input_length a}):
  Tot (words_state a)
  = let blocks, last_block, rem = last_split_blake a input in
    let h' = update_multi a hash blocks in
    (Spec.Blake2.blake2_update_block (to_blake_alg a) true (v (snd h' +. u64 rem)) last_block (fst h'), u64 0)


  assume(
      let kk = 0 in
      let k = Seq.empty in
      let d = input in
      let nn = Spec.Blake2.max_output (to_blake_alg a) in
      let prev0 = Spec.Blake2.compute_prev0 (to_blake_alg a) kk in
      let s = Spec.Blake2.blake2_init (to_blake_alg a) kk k nn in
      let s = Spec.Blake2.blake2_update_blocks (to_blake_alg a) prev0 d s in
      (**)
      let bs, l = split_blocks a input in
      let hash = update_multi a (init a) bs in
      let hash = update_last a hash (S.length bs) l in
      s == fst hash)


let blake2 a d kk k nn =
  let prev0 = compute_prev0 a kk in
  let s = blake2_init a kk k nn in
  let s = blake2_update_blocks a prev0 d s in
  blake2_finish a s nn


let hash_incremental (a:hash_alg) (input:bytes{S.length input <= (max_input_length a)}):
  Tot (hash:bytes{S.length hash = (hash_length a)})
=
  let bs, l = split_blocks a input in
  let hash = update_multi a (init a) bs in
  let hash = update_last a hash (S.length bs) l in
  finish a hash

let split_blocks (a:hash_alg) (input:bytes)
  : Pure (bytes & bytes)
    (requires S.length input <= max_input_length a)
    (ensures fun (l, r) ->
      S.length l % block_length a == 0 /\
      S.length r <= block_length a /\
      S.append l r == input)
  = let open FStar.Mul in
    let n = S.length input / block_length a in
    // Ensuring that we always handle one block in update_last
    let n = if S.length input % block_length a = 0 && n > 0 then n-1 else n in
    let bs, l = S.split input (n * block_length a) in
    S.lemma_split input (n * block_length a);
    bs, l

let update_multi
  (a:hash_alg)
  (hash:words_state a)
  (blocks:bytes_blocks a)
=
  Lib.UpdateMulti.mk_update_multi (block_length a) (update a) hash blocks

let rec mk_update_multi #a (block_length: pos)
  (update: update_t a block_length)
  (acc: a)
  (blocks: S.seq uint8): Pure a
  (requires
    S.length blocks % block_length = 0)
  (ensures fun _ ->
    True)
  (decreases (S.length blocks))
=
  if S.length blocks = 0 then
    acc
  else
    let block, rem = split_block block_length blocks 1 in
    let acc = update acc block in
    mk_update_multi block_length update acc rem



let hash_is_hash_incremental (a: hash_alg) (input: bytes { S.length input <= max_input_length a }):
  Lemma (ensures (S.equal (hash a input) (hash_incremental a input)))
=
  if is_blake a then (blake2_is_hash_incremental a input)
  else
  let open FStar.Mul in
  let n = S.length input / block_length a in
  let n = if S.length input % block_length a = 0 && n > 0 then n-1 else n in
  let padding = pad a (S.length input) in
  let padded_input = input `S.append` padding in
  let blocks, rest = Lib.UpdateMulti.split_block (block_length a) padded_input n in
  let blocks', rest' = S.split input (n * block_length a) in
  S.lemma_eq_intro blocks blocks';
  S.lemma_eq_intro (rest' `S.append` padding) rest;
  Math.Lemmas.multiple_modulo_lemma n (block_length a);
  S.lemma_eq_intro padded_input (blocks `S.append` rest);
  update_multi_associative a (init a) blocks rest;
  S.lemma_eq_intro (fst (update_multi a (init a) padded_input)) (fst (update_multi a (update_multi a (init a) blocks) rest))
