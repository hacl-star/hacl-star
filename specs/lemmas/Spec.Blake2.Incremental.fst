module Spec.Blake2.Incremental

module S = FStar.Seq
module Blake2 = Spec.Blake2

open Spec.Agile.Hash
open Spec.Hash.Definitions
open Spec.Hash.Incremental.Definitions
open Spec.Hash.PadFinish
open Spec.Hash.Lemmas

friend Spec.Agile.Hash

open FStar.Mul
module Loops = Lib.LoopCombinators

#set-options "--fuel 0 --ifuel 0 --z3rlimit 50"

/// Below we prove once and for all properties about the values returned by
/// some utility functions. Note that some of those functions have post-conditions,
/// so don't be surprise not to see obvious properties which are already given by
/// those postconditions (we don't duplicate them).
/// We introduce those lemmas below because they are easy to prove independantly,
/// and allow us to make proofs while disabling non-linear artihmetic in Z3 later,
/// so as to ensure proofs stability.
let blake2_size_block_props (a : hash_alg{is_blake a}) :
  Lemma(
    Spec.Blake2.size_block (to_blake_alg a) > 0 /\
    Spec.Blake2.size_block (to_blake_alg a) == block_length a) = ()

let blake2_split_props (a:Blake2.alg) (len:nat) :
  Lemma(
    let nb, rem = Blake2.split a len in
    rem <= len /\
    rem <= Blake2.size_block a) = ()

#push-options "--z3rlimit 100"
let split_blocks_props (a:hash_alg{is_blake a}) (input:bytes) :
  Lemma
  (requires (S.length input `less_than_max_input_length` a))
  (ensures (
    let nb, rem = Blake2.split (to_blake_alg a) (S.length input) in
    let bs, l = split_blocks a input in
    Seq.length bs = nb * block_length a /\
    Seq.length l = rem /\
    rem <= block_length a /\
    Seq.length input = Seq.length bs + rem /\
    rem = Seq.length input - Seq.length bs /\
    l `S.equal` S.slice input (S.length input - rem) (S.length input) /\
    (Seq.length input <= block_length a ==>
     (nb = 0 /\ rem = Seq.length input))))
  =
  let nb, rem = Blake2.split (to_blake_alg a) (S.length input) in
  blake2_split_props (to_blake_alg a) (S.length input);
  let bs, l = split_blocks a input in
  ()
#pop-options

let last_split_blake_props (a:hash_alg{is_blake a}) (input : bytes) :
  Lemma
  (requires (Seq.length input <= block_length a))
  (ensures (
    let blocks, last_block, rem = last_split_blake a input in
    blocks `Seq.equal` Seq.empty /\
    rem = Seq.length input /\
    last_block `Seq.equal` Blake2.get_last_padded_block (to_blake_alg a) input rem)) =
  ()

let last_split_blake_get_last_padded_block_eq (a:hash_alg{is_blake a}) (input : bytes) :
  Lemma
  (requires S.length input `less_than_max_input_length` a)
  (ensures (
    let nb, rem = Blake2.split (to_blake_alg a) (S.length input) in
    let bs, l = split_blocks a input in
    let last_block1 = Blake2.get_last_padded_block (to_blake_alg a) input rem in
    let blocks, last_block2, rem = last_split_blake a l in
    last_block2 `Seq.equal` last_block1)) =
  let nb, rem = Blake2.split (to_blake_alg a) (S.length input) in
  let bs, l = split_blocks a input in
  let last_block1 = Blake2.get_last_padded_block (to_blake_alg a) input rem in
  let blocks, last_block2, rem = last_split_blake a l in
  assert(input `Seq.equal` Seq.append bs l);
  blake2_split_props (to_blake_alg a) (S.length input);
  split_blocks_props a input;
  last_split_blake_props a l;
  ()

/// Below are various lemmas used to prove ``repeati_blake2_update1_is_update_multi``.
let blake2_update_multi_one_block_eq
  (a:hash_alg{is_blake a})
  (block : bytes_block a)
  (hash : words_state' a)
  (totlen : nat{(totlen + block_length a) <= max_extra_state a}) :
  Lemma
  (ensures (
    let totlen' = totlen + block_length a in
    update_multi a (hash, nat_to_extra_state a totlen) block ==
    (Blake2.blake2_update_block (to_blake_alg a) false totlen'
                                block hash,
     nat_to_extra_state a totlen'))) =
  let s = (hash, nat_to_extra_state a totlen) in
  let totlen' = nat_to_extra_state a (totlen + block_length a) in
  extra_state_add_nat_bound_lem1 #a (nat_to_extra_state a totlen) (block_length a);
  assert(totlen' == extra_state_add_nat #a (nat_to_extra_state a totlen) (block_length a));
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
    ((Blake2.blake2_update_block (to_blake_alg a) false (extra_state_v #a totlen')
                                 block hash,
     totlen')))

/// Auxiliary lemma to help type postconditions
let nb_blocks_props (a:hash_alg{is_blake a}) (nb prev data_length : nat) :
  Lemma
  (requires (
    nb * block_length a <= data_length /\
    prev + data_length <= Blake2.max_limb (to_blake_alg a) /\
    prev + nb * block_length a <= max_extra_state a))
  (ensures (
    nb * block_length a >= 0 /\
    nb <= data_length / Spec.Blake2.size_block (to_blake_alg a) /\
    nb * block_length a % block_length a = 0)) =
  Math.Lemmas.nat_times_nat_is_nat nb (block_length a);
  assert(nb * block_length a >= 0);
  assert_norm(Spec.Blake2.size_block (to_blake_alg a) > 0);
  assert_norm(block_length a == Blake2.size_block (to_blake_alg a));
  calc (<=) {
    (nb <: int);
    (==) { Math.Lemmas.cancel_mul_div nb (block_length a) }
    (nb * block_length a) / block_length a;
    (<=) { Math.Lemmas.lemma_div_le (nb * block_length a) data_length (block_length a) }
    data_length / block_length a;
    (==) {}
    data_length / Spec.Blake2.size_block (to_blake_alg a);
  };
  assert_norm(block_length a > 0);
  Math.Lemmas.multiple_modulo_lemma nb (block_length a)

/// Auxiliary lemma to help type postconditions
let nb_nonzero_blocks_props (a:hash_alg{is_blake a}) (nb prev data_length : nat) :
  Lemma
  (requires (
    nb > 0 /\
    nb * block_length a <= data_length /\
    prev + data_length <= Blake2.max_limb (to_blake_alg a) /\
    prev + nb * block_length a <= max_extra_state a))
  (ensures (
    nb * block_length a >= 0 /\
    nb <= data_length / Spec.Blake2.size_block (to_blake_alg a) /\
    nb * block_length a % block_length a = 0 /\
    (nb - 1) * block_length a >= 0 /\
    (nb - 1) * block_length a < nb * block_length a /\
    (nb * block_length a) - ((nb-1) * block_length a) = block_length a /\
    Blake2.size_block (to_blake_alg a) == block_length a)) =
  nb_blocks_props a nb prev data_length;
  blake2_size_block_props a;
  Math.Lemmas.lemma_mult_le_right (block_length a) (nb-1) nb;
  Math.Lemmas.nat_times_nat_is_nat (nb-1) (block_length a);
  Math.Lemmas.lemma_div_le (nb * block_length a) data_length (block_length a);
  Math.Lemmas.cancel_mul_div nb (block_length a);
  Math.Lemmas.distributivity_sub_left nb (nb-1) (block_length a);
  Math.Lemmas.mul_one_left_is_same (block_length a)

#push-options "--z3cliopt smt.arith.nl=false"
let repeati_blake2_update1_eq
  (a:hash_alg{is_blake a})
  (nb prev : nat)
  (d : bytes)
  (hash : words_state' a) :
  Lemma
  (requires (
    nb > 0 /\
    nb * block_length a <= Seq.length d /\
    prev + Seq.length d <= Blake2.max_limb (to_blake_alg a) /\
    prev + nb * block_length a <= max_extra_state a))
  (ensures (
    (**) nb_nonzero_blocks_props a nb prev (Seq.length d);
    let update1 = Blake2.blake2_update1 (to_blake_alg a) prev d in
    let block = S.slice d ((nb-1) * block_length a) (nb * block_length a) in
    Loops.repeati nb update1 hash ==
    Blake2.blake2_update_block (to_blake_alg a) false (prev + nb * block_length a)
                               block (Loops.repeati (nb-1) update1 hash)
  )) =
  nb_nonzero_blocks_props a nb prev (Seq.length d);
  let update1 = Blake2.blake2_update1 (to_blake_alg a) prev d in
  let block = S.slice d ((nb-1) * block_length a) (nb * block_length a) in
  Loops.unfold_repeati nb update1 hash (nb - 1)
#pop-options

let blake2_update_multi_associate_eq1
  (a:hash_alg{is_blake a}) (nb prev : nat)
  (blocks : bytes{S.length blocks == nb * block_length a})
  (hash : words_state' a) :
  Lemma
  (requires (
    nb > 0 /\
    prev + nb * block_length a <= Blake2.max_limb (to_blake_alg a) /\
    prev + nb * block_length a <= max_extra_state a
  ))
  (ensures (
    let blocks1, blocks2 = Seq.split blocks ((nb-1) * block_length a) in
    update_multi a (hash, nat_to_extra_state a prev) blocks ==
    update_multi a (update_multi a (hash, nat_to_extra_state a prev) blocks1) blocks2)) =
  let blocks1, blocks2 = Seq.split blocks ((nb-1) * block_length a) in
  assert(blocks `S.equal` S.append blocks1 blocks2);
  assert(Seq.length blocks1 == (nb - 1) * block_length a);
  Math.Lemmas.multiple_modulo_lemma (nb-1) (block_length a);
  assert(Seq.length blocks2 == 1 * block_length a);
  Math.Lemmas.multiple_modulo_lemma 1 (block_length a);
  update_multi_associative a (hash, nat_to_extra_state a prev) blocks1 blocks2

#push-options "--z3cliopt smt.arith.nl=false"
val repeati_blake2_update1_is_update_multi_aux
  (a:hash_alg{is_blake a}) (nb prev : nat)
  (d : bytes)
  (hash : words_state' a) :
  Lemma
  (requires (
    nb * block_length a <= Seq.length d /\
    prev + Seq.length d <= Blake2.max_limb (to_blake_alg a) /\
    prev + nb * block_length a <= max_extra_state a
  ))
  (ensures (
    (**) nb_blocks_props a nb prev (Seq.length d);
    let blocks, _ = Seq.split d (nb * block_length a) in
    (Loops.repeati #(words_state' a) nb (Blake2.blake2_update1 (to_blake_alg a) prev d) hash,
     nat_to_extra_state a (prev + nb * block_length a)) ==
       update_multi a (hash, nat_to_extra_state a prev) blocks))
#pop-options

#push-options "--fuel 1 --z3cliopt smt.arith.nl=false"
let rec repeati_blake2_update1_is_update_multi_aux a nb prev d hash =
  nb_blocks_props a nb prev (Seq.length d);
  blake2_size_block_props a;
  let update1 = Blake2.blake2_update1 (to_blake_alg a) prev d in
  let blocks, _ = Seq.split d (nb * block_length a) in
  if nb = 0 then
    begin
    Loops.eq_repeati0 #(words_state' a) nb update1 hash;
    assert(Loops.repeati #(words_state' a) nb (Blake2.blake2_update1 (to_blake_alg a) prev d) hash == hash);
    Math.Lemmas.mul_zero_left_is_zero (block_length a);
    assert(Seq.length blocks = 0);
    Spec.Hash.Lemmas.update_multi_zero a (hash, nat_to_extra_state a prev);
    assert(update_multi a (hash, nat_to_extra_state a prev) blocks == (hash, nat_to_extra_state a prev));
    calc (==) {
      prev + nb * block_length a;
      (==) { Math.Lemmas.mul_zero_left_is_zero (block_length a) }
      prev + 0;
      (==) { Math.Lemmas.add_zero_right_is_same prev }
      prev;
    }
    end
  else
    begin
    repeati_blake2_update1_eq a nb prev d hash;
    Math.Lemmas.nat_times_nat_is_nat (nb-1) (block_length a);
    Math.Lemmas.lemma_mult_le_right (block_length a) (nb - 1) nb;
    assert((nb - 1) * block_length a <= nb * block_length a);
    let blocks1, blocks2 = Seq.split blocks ((nb-1) * block_length a) in
    assert(Seq.append blocks1 blocks2 `Seq.equal` blocks);
    blake2_update_multi_associate_eq1 a nb prev blocks hash;
    calc (==) {
      Seq.length blocks1 % block_length a;
      (==) {}
      ((nb - 1) * block_length a) % block_length a;
      (==) { Math.Lemmas.cancel_mul_mod (nb-1) (block_length a) }
      0;
    };
    calc (==) {
      Seq.length blocks2;
      (==) {}
      (nb * block_length a) - ((nb-1) * block_length a);
      (==) { Math.Lemmas.distributivity_sub_left nb (nb-1) (block_length a) }
      1 * block_length a;
      (==) { Math.Lemmas.mul_one_left_is_same (block_length a) }
      block_length a;
    };
    calc (==) {
      Seq.length blocks2 % block_length a;
      (==) {}
      1 * block_length a % block_length a;
      (==) { Math.Lemmas.cancel_mul_mod 1 (block_length a) }
      0;
    };
    let s0 = (hash, nat_to_extra_state a prev) in
    let s1 = update_multi a s0 blocks1 in
    let s2 = update_multi a s1 blocks2 in
    let s2' = update_multi a s0 blocks in
    assert(s2 == s2');
    assert((nb - 1) * block_length a <= Seq.length d);
    assert(prev + Seq.length d <= Blake2.max_limb (to_blake_alg a));
    assert(prev + (nb-1) * block_length a <= max_extra_state a);
    repeati_blake2_update1_is_update_multi_aux a (nb - 1) prev d hash;
    assert(blocks1 `S.equal` Seq.slice d 0 ((nb-1) * block_length a));
    assert(
      s1 == (Loops.repeati #(words_state' a) (nb-1) update1 hash,
             nat_to_extra_state a (prev + (nb-1) * block_length a)));
    blake2_update_multi_one_block_eq a blocks2 (fst s1) (extra_state_v (snd s1));
    Loops.unfold_repeati #(words_state' a) nb update1 hash (nb-1)
    end
#pop-options

let repeati_blake2_update1_is_update_multi a nb prev d hash =
  repeati_blake2_update1_is_update_multi_aux a nb prev d hash

let extra_state_v_nat_to_extra_state_is_id (a : hash_alg{is_blake a})
                                           (n : nat{n <= max_extra_state a}) :
  Lemma(extra_state_v (nat_to_extra_state a n) = n) = ()

/// In order to prove that incremental blake is equal to blake, we prove
/// that the intermediary states computed at each step of the two algorithms are
/// equal, with one auxiliary lemma per step.

/// We begin by providing properly unfolded versions of the blake functions below,
/// which will be used as references to match the different steps. We prove that
/// those functions are equal to the original ones for sanity check.

open Lib.ByteSequence

/// The alternative blake2 function
let blake2'
  (a:hash_alg{is_blake a})
  (input : bytes {S.length input `less_than_max_input_length` a}) :
  r:lbytes (Spec.Blake2.max_output (to_blake_alg a)) {
    r == Blake2.blake2 (to_blake_alg a) input 0 Seq.empty (Spec.Blake2.max_output (to_blake_alg a))}
  =
  let nn = Blake2.max_output (to_blake_alg a) in
  let kk = 0 in
  let prev0 = 0 in
  let s1 = Blake2.blake2_init_hash (to_blake_alg a) kk nn in
  let nb, rem = Blake2.split (to_blake_alg a) (S.length input) in
  let s2 = Loops.repeati #(Blake2.state (to_blake_alg a)) nb
                         (Blake2.blake2_update1 (to_blake_alg a) prev0 input) s1 in
  let s3 = Blake2.blake2_update_last (to_blake_alg a) prev0 rem input s2 in
  let s4 = Blake2.blake2_finish (to_blake_alg a) s3 (Spec.Blake2.max_output (to_blake_alg a)) in
  s4

/// The alternative incremental blake2 function
let blake2_hash_incremental'
  (a:hash_alg{is_blake a})
  (input : bytes {S.length input `less_than_max_input_length` a}) :
  r:lbytes (hash_length a) {
    r == hash_incremental a input } =
  let bs, l = split_blocks a input in
  let is1 = init a in
  let is2 = update_multi a is1 bs in
  let is3 = update_last a is2 (S.length bs) l in
  let is4 = finish a is3 in
  is4

/// Below, we prove all the intermediary lemmas which relate the states from the
/// two functions above

val blake2_is_hash_incremental_aux1
  (a:hash_alg{is_blake a})
  (input : bytes {S.length input `less_than_max_input_length` a}) :
  Lemma(
    (**)
    let nn = Spec.Blake2.max_output (to_blake_alg a) in
    let kk = 0 in
    let prev0 = 0 in
    let s1 = Blake2.blake2_init_hash (to_blake_alg a) kk nn in
    (**)
    let bs, l = split_blocks a input in
    let is1 = init a in
    ((s1 <: words_state' a), nat_to_extra_state a prev0) == is1)

let blake2_is_hash_incremental_aux1 a input = ()

val blake2_is_hash_incremental_aux2
  (a:hash_alg{is_blake a})
  (input : bytes {S.length input `less_than_max_input_length` a})
  (s1 : Blake2.state (to_blake_alg a)) :
  Lemma(
//    let prev0 = Blake2.compute_prev0 (to_blake_alg a) kk in
    let prev0 = 0 in
    let nb, rem = Blake2.split (to_blake_alg a) (S.length input) in
    let s2 = Loops.repeati #(Blake2.state (to_blake_alg a)) nb
                           (Blake2.blake2_update1 (to_blake_alg a) prev0 input) s1 in
    let bs, l = split_blocks a input in
    let is2 : words_state a = update_multi a (s1, nat_to_extra_state a prev0) bs in
    is2 == ((s2 <: words_state' a), nat_to_extra_state a (prev0 + nb * block_length a)))

#push-options "--z3cliopt smt.arith.nl=false"
let blake2_is_hash_incremental_aux2 a input s1 =
  (* Preliminaries: variables introduction *)
  blake2_size_block_props a;
  let prev0 = 0 in
  let nb, rem = Blake2.split (to_blake_alg a) (S.length input) in
  blake2_split_props (to_blake_alg a) (S.length input);
  assert(Spec.Blake2.size_block (to_blake_alg a) > 0);
  assert(nb <= Seq.length input / Spec.Blake2.size_block (to_blake_alg a));
  assert(prev0 <= block_length a);
  assert(prev0 + Seq.length input <= Spec.Blake2.max_limb (to_blake_alg a));
  let s2 = Loops.repeati #(Blake2.state (to_blake_alg a)) nb
                         (Blake2.blake2_update1 (to_blake_alg a) prev0 input) s1 in
  let bs, l = split_blocks a input in
  split_blocks_props a input;
  let is2 : words_state a = update_multi a (s1, nat_to_extra_state a prev0) bs in
  (* The proof *)
  assert(S.length bs == nb * block_length a);
  assert(
    nb * block_length a <= Seq.length input /\
    prev0 + Seq.length input <= Blake2.max_limb (to_blake_alg a) /\
    prev0 + nb * block_length a <= max_extra_state a);
  repeati_blake2_update1_is_update_multi a nb prev0 input s1;
  assert(
    (Loops.repeati #(words_state' a) nb (Blake2.blake2_update1 (to_blake_alg a) prev0 input) s1,
     nat_to_extra_state a (prev0 + nb * block_length a)) ==
       update_multi a (s1, nat_to_extra_state a prev0) bs);
  assert(is2 == ((s2 <: words_state' a), nat_to_extra_state a (prev0 + nb * block_length a)))
#pop-options

val blake2_is_hash_incremental_aux3
  (a:hash_alg{is_blake a})
  (input : bytes {S.length input `less_than_max_input_length` a})
  (s2 : Blake2.state (to_blake_alg a)) :
  Lemma(
    let prev0 = 0 in
    let nb, rem = Blake2.split (to_blake_alg a) (S.length input) in
    let bs, l = split_blocks a input in
    let is2 : words_state a =
      ((s2 <: words_state' a), nat_to_extra_state a (prev0 + nb * block_length a)) in
    let s3 = Blake2.blake2_update_last (to_blake_alg a) prev0 rem input s2 in
    let is3 : words_state a = update_last a is2 (S.length bs) l in
    is3 == ((s3 <: words_state' a), nat_to_extra_state a 0))

#push-options "--z3cliopt smt.arith.nl=false"
let blake2_is_hash_incremental_aux3 a input s2 =
  (* Preliminaries: variables introduction *)
  blake2_size_block_props a;
  let prev0 = 0 in
  let nb, rem = Blake2.split (to_blake_alg a) (S.length input) in
  blake2_split_props (to_blake_alg a) (S.length input);
  let bs, l = split_blocks a input in
  split_blocks_props a input;
  let is2 : words_state a =
    ((s2 <: words_state' a), nat_to_extra_state a (prev0 + nb * block_length a)) in
  let s3 = Blake2.blake2_update_last (to_blake_alg a) prev0 rem input s2 in
  let is3 : words_state a = update_last a is2 (S.length bs) l in
  (* The proof *)
  (* First, work on [s3] *)
  assert(rem == S.length input - S.length bs);
  assert(l `S.equal` S.slice input (S.length input - rem) (S.length input));
  let pblock = Blake2.get_last_padded_block (to_blake_alg a) input rem in
  assert(
    s3 == Blake2.blake2_update_block (to_blake_alg a) true (prev0 + S.length input) pblock s2);
  (* Then, work on [is3] *)
  assert(is3 == update_last_blake a is2 (S.length bs) l);
  let blocks, last_block, rem' = last_split_blake a l in
  last_split_blake_props a l;
  last_split_blake_get_last_padded_block_eq a input;
  assert(rem = rem');
  assert(
    blocks == S.empty /\
    last_block == pblock /\
    rem' = S.length l);
  let h' : words_state a = update_multi a is2 S.empty in
  update_multi_zero a is2;
  assert(h' == is2);
  assert_norm(Some?.v (max_input_length a) == max_extra_state a);
  assert(snd h' == nat_to_extra_state a (prev0 + S.length bs));
  calc(==) {
    extra_state_v (snd h');
  (==) {}
    extra_state_v (nat_to_extra_state a (prev0 + S.length bs));
  (==) { extra_state_v_nat_to_extra_state_is_id a (prev0 + S.length bs) }
    prev0 + S.length bs;
  };
  calc(==) {
    extra_state_v (snd h') + rem;
  (==) {}
    (prev0 + S.length bs) + rem;
  (==) { Math.Lemmas.paren_add_left prev0 (S.length bs) rem }
    prev0 + S.length bs + rem;
  (==) { Math.Lemmas.paren_add_right prev0 (S.length bs) rem }
    prev0 + (S.length bs + rem);
  (==) {}
    prev0 + S.length input;
  };
  assert(extra_state_v (snd h') + rem <= max_extra_state a);
  assert(rem <= max_extra_state a);
  calc (==) {
    extra_state_v (extra_state_add_nat (snd h') rem);
  (==) { extra_state_add_nat_bound_lem2 #a (snd h') rem }
    extra_state_v (nat_to_extra_state a ((extra_state_v (snd h')) + rem));
  (==) {}
    extra_state_v (nat_to_extra_state a (prev0 + S.length input));
  (==) { extra_state_v_nat_to_extra_state_is_id a (prev0 + S.length input) }
    prev0 + S.length input;
  };
  assert(
    is3 ==
    (Spec.Blake2.blake2_update_block (to_blake_alg a) true
                                     (extra_state_v (extra_state_add_nat (snd h') rem))
                                     last_block (fst h'),
     nat_to_extra_state a 0));
  (* Prove the final equality *)
  assert(s3 == fst is3)
#pop-options

val blake2_is_hash_incremental_aux4
  (a:hash_alg{is_blake a})
  (input : bytes {S.length input `less_than_max_input_length` a})
  (s3 : Blake2.state (to_blake_alg a)) :
  Lemma(
    let s4 = Blake2.blake2_finish (to_blake_alg a) s3 (Spec.Blake2.max_output (to_blake_alg a)) in
    let is4 = finish a ((s3 <: words_state' a), nat_to_extra_state a 0) in
    s4 == is4)

let blake2_is_hash_incremental_aux4 a input s3 = ()

/// The final theorem about blake2
let blake2_is_hash_incremental
  (a : hash_alg{is_blake a})
  (input : bytes {S.length input `less_than_max_input_length` a}) :
  Lemma (
    S.equal (Blake2.blake2 (to_blake_alg a) input 0 Seq.empty (Spec.Blake2.max_output (to_blake_alg a)))
            (hash_incremental a input))
  =
  blake2_is_hash_incremental_aux1 a input;
  let nn = Spec.Blake2.max_output (to_blake_alg a) in
  let kk = 0 in
  let s1 = Blake2.blake2_init_hash (to_blake_alg a) kk nn in
  blake2_is_hash_incremental_aux2 a input s1;
  let prev0 = 0 in
  let nb, rem = Blake2.split (to_blake_alg a) (S.length input) in
  blake2_split_props (to_blake_alg a) (S.length input);
  let s2 = Loops.repeati #(Blake2.state (to_blake_alg a)) nb
                         (Blake2.blake2_update1 (to_blake_alg a) prev0 input) s1 in
  blake2_is_hash_incremental_aux3 a input s2;
  let s3 = Blake2.blake2_update_last (to_blake_alg a) prev0 rem input s2 in
  blake2_is_hash_incremental_aux4 a input s3
