module Spec.Hash.Incremental

module S = FStar.Seq

open Spec.Hash.Definitions
open Spec.Hash.PadFinish
open Spec.Hash.Lemmas

module B2 = Spec.Blake2

friend Spec.Agile.Hash

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 50"

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

let update_multi_associate_eq1
  (a:hash_alg{is_blake a}) (nb prev : nat)
  (blocks : bytes{S.length blocks == nb * block_length a})
  (hash : words_state' a) :
  Lemma
  (requires (
    nb > 0 /\
    prev + nb * block_length a <= max_limb (to_blake_alg a) /\
    prev + nb * block_length a <= pow2 64 - 1
  ))
  (ensures (
    let blocks1, blocks2 = Seq.split blocks ((nb-1) * block_length a) in
    update_multi a (hash, u64 prev) blocks ==
    update_multi a (update_multi a (hash, u64 prev) blocks1) blocks2)) =
  let blocks1, blocks2 = Seq.split blocks ((nb-1) * block_length a) in
  assert(blocks `S.equal` S.append blocks1 blocks2);
  assert(Seq.length blocks1 == (nb - 1) * block_length a);
  Math.Lemmas.multiple_modulo_lemma (nb-1) (block_length a);
  assert(Seq.length blocks2 == 1 * block_length a);
  Math.Lemmas.multiple_modulo_lemma 1 (block_length a);
  update_multi_associative a (hash, u64 prev) blocks1 blocks2

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
    update_multi_associate_eq1 a nb prev blocks hash;
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

/// It is enough to prove the equality between the spec and the incremental hash
/// without the finish step. Moreover, for some reason, introducing those two
/// functions below helps reducing the proof time, which ceases becoming super
/// random (I don't know why).
let blake2_no_finish
  (a:hash_alg{is_blake a}) (input:bytes{Seq.length input <= max_input_length a}) =
  let nn = Spec.Blake2.max_output (to_blake_alg a) in
  let prev0 = compute_prev0 (to_blake_alg a) 0 in
  let s1 = blake2_init (to_blake_alg a) 0 Seq.empty nn in
  let (nb,rem) = split (to_blake_alg a) (S.length input) in
  let s2 = Loops.repeati nb (blake2_update1 (to_blake_alg a) prev0 input) s1 in
  let s3 = blake2_update_last (to_blake_alg a) prev0 rem input s2 in
  s3

let blake2_hash_incremental_no_finish
  (a:hash_alg{is_blake a}) (input:bytes{Seq.length input <= max_input_length a}) =
  let bs, l = split_blocks a input in
  let is1 = init a in
  let is2 = update_multi a is1 bs in
  let is3 = update_last a is2 (S.length bs) l in
  is3

/// TODO: for some reason, if I don't put a very big rlimit, the proof almost
/// immediately fails. However, with a big rlimit it succeeds quickly.
#push-options "--z3rlimit 500 --fuel 0 --ifuel 0"
let blake2_is_hash_incremental_aux
  (a:hash_alg{is_blake a}) (input:bytes{Seq.length input <= max_input_length a})
  : Lemma
    (blake2_no_finish a input == fst (blake2_hash_incremental_no_finish a input))
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
  let pblock = get_last_padded_block (to_blake_alg a) input rem in
  assert(
    s3 == blake2_update_block (to_blake_alg a) true (S.length input) pblock s2);
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
  assert(max_input_length a == pow2 64 -1);
  assert(snd h' == u64 (S.length bs));
  assert(v #U64 #SEC (snd h') + rem == S.length input);
  add_v_eq (v #U64 #SEC (snd h')) rem;
  assert(v (snd h' +. u64 rem) == S.length input);
  assert(
    is3 ==
    (Spec.Blake2.blake2_update_block (to_blake_alg a) true (v (snd h' +. u64 rem))
                                     last_block (fst h'),
     u64 0));
  (* Prove the final equality *)
  assert(s3 == fst is3)
#pop-options

let blake2_is_hash_incremental
  (a:hash_alg{is_blake a}) (input:bytes{Seq.length input <= max_input_length a})
  : Lemma
    (Spec.Blake2.blake2 (to_blake_alg a) input 0 Seq.empty
                        (Spec.Blake2.max_output (to_blake_alg a)) ==
     hash_incremental a input)
  =
  blake2_is_hash_incremental_aux a input

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

let hash_is_hash_incremental (a: hash_alg) (input: bytes { S.length input <= max_input_length a }):
  Lemma (ensures (S.equal (hash a input) (hash_incremental a input)))
  =
  if is_blake a then (blake2_is_hash_incremental a input)
  else md_is_hash_incremental a input (init a)
