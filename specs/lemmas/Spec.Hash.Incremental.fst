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

/// The [blake2_is_hash_incremental] lemma is not fundamentally difficult, but
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
    nb < Seq.length d / size_block (to_blake_alg a) /\
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

#push-options "--z3rlimit 500 --ifuel 1 --fuel 1"
let rec repeati_blake2_update1_as_update_multi_eq
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

let rec update_multi_associative #a (block_length: pos)
  (update: update_t a block_length)
  (acc: a)
  (input1 input2: S.seq uint8):
  Lemma
    (requires
      S.length input1 % block_length == 0 /\
      S.length input2 % block_length == 0)
    (ensures (
      let input = S.append input1 input2 in
      S.length input % block_length == 0 /\
      mk_update_multi block_length update (mk_update_multi block_length update acc input1) input2 ==
        mk_update_multi block_length update acc input))
    (decreases (
      S.length input1 + S.length input2))

(*
#push-options "--z3rlimit 500 --ifuel 1"
let blake2_is_hash_incremental
  (a:hash_alg{is_blake a}) (input:bytes{Seq.length input <= max_input_length a})
  : Lemma
    (Spec.Blake2.blake2 (to_blake_alg a) input 0 Seq.empty (Spec.Blake2.max_output (to_blake_alg a)) ==
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
    let hash1 = update_last a hash0 (S.length bs) l in
    hash1 == update_last_blake a hash0 (S.length bs) l);
  admit()




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
