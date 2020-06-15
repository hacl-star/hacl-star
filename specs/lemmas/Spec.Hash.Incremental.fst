module Spec.Hash.Incremental

module S = FStar.Seq

open Spec.Hash.Definitions
open Spec.Hash.PadFinish
open Spec.Hash.Lemmas

module Blake2 = Spec.Blake2

friend Spec.Agile.Hash

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 50"

open FStar.Mul
module Loops = Lib.LoopCombinators

/// A lemma I could not find in FStar.Math.Lemmas - note: duplicated in Hash.Streaming.Spec.fst
let mul_zero_left_is_zero (n : nat) : Lemma(0 * n = 0) = ()

/// A lemma I could not find in FStar.Math.Lemmas
let add_zero_right_is_same (n : nat) : Lemma(n + 0 = n) = ()

/// TODO: I don't find this lemma in Lib, and the below proofs don't work if
/// I don't prove this step separately.
let add_v_eq (a b : nat) :
  Lemma
  (requires (a + b <= pow2 64 - 1))
  (ensures (v (u64 a +. u64 b) == a + b)) = ()

/// The [repeati_blake2_update1_is_update_multi] lemma is not fundamentally difficult, but
/// the proof time/success rate can be very random, probably because of modular
/// arithmetic. For this reason, we cut it into small pieces.
let update_multi_one_block_eq
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
  extra_state_add_nat_bound_lem #a (nat_to_extra_state a totlen) (block_length a);
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
    prev + nb * block_length a <= max_extra_state a
  ))
  (ensures (
    let update1 = Blake2.blake2_update1 (to_blake_alg a) prev d in
    let block = S.slice d ((nb-1) * block_length a) (nb * block_length a) in
    Loops.repeati nb update1 hash ==
    Blake2.blake2_update_block (to_blake_alg a) false (prev + nb * block_length a)
                               block (Loops.repeati (nb-1) update1 hash)
  )) =
  let update1 = Blake2.blake2_update1 (to_blake_alg a) prev d in
  let block = S.slice d ((nb-1) * block_length a) (nb * block_length a) in
  Loops.unfold_repeati nb update1 hash (nb - 1)

let update_multi_associate_eq1
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

#push-options "--fuel 1 --z3cliopt smt.arith.nl=false"
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
    (**) Math.Lemmas.nat_times_nat_is_nat nb (block_length a);
    (**) assert(nb * block_length a >= 0);
    (**) assert_norm(Spec.Blake2.size_block (to_blake_alg a) > 0);
    (**) assert_norm(block_length a == Blake2.size_block (to_blake_alg a));
    (**) calc (<=) {
    (**)   (nb <: int);
    (**)   (==) { Math.Lemmas.cancel_mul_div nb (block_length a) }
    (**)   (nb * block_length a) / block_length a;
    (**)   (<=) { Math.Lemmas.lemma_div_le (nb * block_length a) (Seq.length d) (block_length a) }
    (**)   Seq.length d / block_length a;
    (**)   (==) {}
    (**)   Seq.length d / Spec.Blake2.size_block (to_blake_alg a);
    (**) };
    (**) assert(forall (i : nat). i < nb ==> (i < Seq.length d / Spec.Blake2.size_block (to_blake_alg a)));
    (**) assert_norm(block_length a > 0);
    let blocks, _ = Seq.split d (nb * block_length a) in
    (**) Math.Lemmas.multiple_modulo_lemma nb (block_length a);
    (**) assert(Seq.length blocks % block_length a = 0);
    (Loops.repeati #(words_state' a) nb (Blake2.blake2_update1 (to_blake_alg a) prev d) hash,
     nat_to_extra_state a (prev + nb * block_length a)) ==
       update_multi a (hash, nat_to_extra_state a prev) blocks))

let rec repeati_blake2_update1_is_update_multi_aux a nb prev d hash =
  assert_norm(block_length a > 0);
  assert_norm(block_length a == Blake2.size_block (to_blake_alg a));
  calc (<=) {
    (nb <: int);
    (==) { Math.Lemmas.cancel_mul_div nb (block_length a) }
    (nb * block_length a) / block_length a;
    (<=) { Math.Lemmas.lemma_div_le (nb * block_length a) (Seq.length d) (block_length a) }
    Seq.length d / block_length a;
  };
  assert(Seq.length d % block_length a >= 0);
  assert(nb <= Seq.length d / Blake2.size_block (to_blake_alg a));
  assert(prev + nb * block_length a <= Blake2.max_limb (to_blake_alg a));
  let update1 = Blake2.blake2_update1 (to_blake_alg a) prev d in
  Math.Lemmas.nat_times_nat_is_nat nb (block_length a);
  let blocks, _ = Seq.split d (nb * block_length a) in
  assert(Seq.length blocks == nb * block_length a);
  Math.Lemmas.multiple_modulo_lemma nb (block_length a);
  if nb = 0 then
    begin
    Loops.eq_repeati0 #(words_state' a) nb update1 hash;
    assert(Loops.repeati #(words_state' a) nb (Blake2.blake2_update1 (to_blake_alg a) prev d) hash == hash);
    mul_zero_left_is_zero (block_length a);
    assert(Seq.length blocks = 0);
    Spec.Hash.Lemmas.update_multi_zero a (hash, nat_to_extra_state a prev);
    assert(update_multi a (hash, nat_to_extra_state a prev) blocks == (hash, nat_to_extra_state a prev));
    calc (==) {
      prev + nb * block_length a;
      (==) { mul_zero_left_is_zero (block_length a) }
      prev + 0;
      (==) { add_zero_right_is_same prev }
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
    update_multi_associate_eq1 a nb prev blocks hash;
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
    update_multi_one_block_eq a blocks2 (fst s1) (extra_state_v (snd s1));
    Loops.unfold_repeati #(words_state' a) nb update1 hash (nb-1)
    end
#pop-options

let repeati_blake2_update1_is_update_multi a nb prev d hash =
  repeati_blake2_update1_is_update_multi_aux a nb prev d hash

/// It is enough to prove the equality between the spec and the incremental hash
/// without the finish step. Moreover, for some reason, introducing those two
/// functions below helps reducing the proof time, which ceases becoming super
/// random (I don't know why).
let blake2_no_finish
  (a:hash_alg{is_blake a})
  (kk : size_nat{kk <= Blake2.max_key (to_blake_alg a)})
  (k : lbytes kk)
  (input : bytes {if kk = 0 then S.length input <= max_input_length a
                  else S.length input + block_length a <= max_input_length a}) =
//  (input:bytes{Seq.length input <= max_input_length a}) =
  let nn = Blake2.max_output (to_blake_alg a) in
//  let prev0 = Blake2.compute_prev0 (to_blake_alg a) 0 in
  let prev0 = Blake2.compute_prev0 (to_blake_alg a) kk in
//  let s1 = Blake2.blake2_init (to_blake_alg a) 0 S.empty nn in
  let s1 = Blake2.blake2_init (to_blake_alg a) kk k nn in
  let (nb,rem) = Blake2.split (to_blake_alg a) (S.length input) in
  let s2 = Loops.repeati nb (Blake2.blake2_update1 (to_blake_alg a) prev0 input) s1 in
  let s3 = Blake2.blake2_update_last (to_blake_alg a) prev0 rem input s2 in
  s3

let blake2_hash_incremental_no_finish
  (a:hash_alg{is_blake a})
  (kk : size_nat{kk <= Blake2.max_key (to_blake_alg a)})
  (k : lbytes kk)
  (input : bytes {if kk = 0 then S.length input <= max_input_length a
                  else S.length input + block_length a <= max_input_length a}) =
//  (input:bytes{Seq.length input <= max_input_length a}) =
  let bs, l = split_blocks a input in
//  let is1 = init a in
  let is1 = blake2_init a kk k in
  let is2 = update_multi a is1 bs in
  let is3 = update_last a is2 (S.length bs) l in
  is3

/// TODO: for some reason, if I don't put a very big rlimit, the proof almost
/// immediately fails. However, with a big rlimit it succeeds quickly.
/// TODO: another weird thing: when I convert some asserts to asserts, the proof
/// loops...
/// TODO: the proof time is random
#push-options "--z3rlimit 1000 --fuel 0 --ifuel 0"
let blake2_is_hash_incremental_aux
  (a:hash_alg{is_blake a})
  (kk : size_nat{kk <= Blake2.max_key (to_blake_alg a)})
  (k : lbytes kk)
  (input : bytes {if kk = 0 then S.length input <= max_input_length a
                  else S.length input + block_length a <= max_input_length a})
//  (input:bytes{Seq.length input <= max_input_length a})
  : Lemma
    (blake2_no_finish a kk k input == fst (blake2_hash_incremental_no_finish a kk k input))
  =
  (* Let's prove the equality step by step *)
  (**)
  let nn = Spec.Blake2.max_output (to_blake_alg a) in
//  let prev0 = Blake2.compute_prev0 (to_blake_alg a) 0 in
  let prev0 = Blake2.compute_prev0 (to_blake_alg a) kk in
//  let s1 = blake2_init (to_blake_alg a) 0 Seq.empty nn in
  let s1 = Blake2.blake2_init (to_blake_alg a) kk k nn in
  let (nb,rem) = Blake2.split (to_blake_alg a) (S.length input) in
  let s2 = Loops.repeati nb (Blake2.blake2_update1 (to_blake_alg a) prev0 input) s1 in
  let s3 = Blake2.blake2_update_last (to_blake_alg a) prev0 rem input s2 in
  (**)
  let bs, l = split_blocks a input in
//  let is1 = init a in
  let is1 = blake2_init a kk k in
  let is2 = update_multi a is1 bs in
  let is3 = update_last a is2 (S.length bs) l in
  (* [s1 == fst is1] *)
  assert(s1 == fst is1);
  (* [s2 == fst is2] *)
  assert(S.length bs == nb * block_length a);
  assert(
    nb * block_length a <= Seq.length input /\
    prev0 + Seq.length input <= Blake2.max_limb (to_blake_alg a) /\
    prev0 + nb * block_length a <= max_extra_state a);
  repeati_blake2_update1_is_update_multi a nb prev0 input s1;  
  assert(s2 == fst is2);
  (* [s3 == fst is3] *)
  (* First, work on [s3] *)
  assert(rem == S.length input - S.length bs);
  assert(l `S.equal` S.slice input (S.length input - rem) (S.length input));
  let pblock = Blake2.get_last_padded_block (to_blake_alg a) input rem in
//  assert(
//    s3 == Blake2.blake2_update_block (to_blake_alg a) true (S.length input) pblock s2);
  assert(
    s3 == Blake2.blake2_update_block (to_blake_alg a) true (prev0 + S.length input) pblock s2);
  (* Then, work on [is3] *)
  assert(
    is3 == update_last_blake a is2 (S.length bs) l);
  let blocks, last_block, rem' = last_split_blake a l in
  assert(
    blocks == S.empty /\
    last_block == pblock /\
    rem' = S.length l);
  let h' = update_multi a is2 S.empty in
  update_multi_zero a is2;
  assert(h' == is2);
  assert(max_input_length a == max_extra_state a);
  assert(snd h' == nat_to_extra_state a (prev0 + S.length bs));
  assert(extra_state_v (snd h') + rem == prev0 + S.length input);
  extra_state_add_nat_bound_lem #a (snd h') rem;
  (* TODO: above OK, fix below (proof seems to loop) *)
  assert(extra_state_v (extra_state_add_nat (snd h') rem) == prev0 + S.length input);
  assert(
    is3 ==
    (Spec.Blake2.blake2_update_block (to_blake_alg a) true
                                     (extra_state_v (extra_state_add_nat (snd h') rem))
                                     last_block (fst h'),
     nat_to_extra_state a 0));
  (* Prove the final equality *)
  assert(s3 == fst is3)
#pop-options

let blake2_is_hash_incremental
  (a : hash_alg{is_blake a})
  (kk : size_nat{kk <= Blake2.max_key (to_blake_alg a)})
  (k : lbytes kk)
  (input : bytes {if kk = 0 then S.length input <= max_input_length a
                  else S.length input + block_length a <= max_input_length a}) :
  Lemma (
    S.equal (Blake2.blake2 (to_blake_alg a) input kk k (Spec.Blake2.max_output (to_blake_alg a)))
            (blake2_hash_incremental a kk k input))
  =
  blake2_is_hash_incremental_aux a kk k input

let md_is_hash_incremental
  (a:hash_alg{not (is_blake a)})
  (input: bytes { S.length input <= max_input_length a })
  (s:words_state a)
  : Lemma (
      let blocks, rest = split_blocks a input in
      update_multi a s (input `S.append` (pad a (S.length input))) ==
      update_last a (update_multi a s blocks) (S.length blocks) rest)
   = let blocks, rest = split_blocks a input in
     assert (S.length input == S.length blocks + S.length rest);
     let padding = pad a (S.length input) in
     calc (==) {
       update_last a (update_multi a s blocks) (S.length blocks) rest;
       (==) { }
       update_multi a (update_multi a s blocks) S.(rest @| padding);
       (==) { update_multi_associative a s blocks S.(rest @| padding) }
       update_multi a s S.(blocks @| (rest @| padding));
       (==) { S.append_assoc blocks rest padding }
       update_multi a s S.((blocks @| rest) @| padding);
       (==) { }
       update_multi a s S.(input @| padding);
     }

let blake2_hash_incremental_no_key_eq
  (a: hash_alg{is_blake a}) (input: bytes { S.length input <= max_input_length a }) :
  Lemma(Seq.equal (blake2_hash_incremental a 0 Seq.empty input)
                  (hash_incremental a input)) = ()

let hash_is_hash_incremental (a: hash_alg) (input: bytes { S.length input <= max_input_length a }):
  Lemma (S.equal (hash a input) (hash_incremental a input))
  =
  if is_blake a then
    begin
    blake2_is_hash_incremental a 0 Seq.empty input;
    blake2_hash_incremental_no_key_eq a input
    end
  else md_is_hash_incremental a input (init a)
