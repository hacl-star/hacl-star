module Hacl.Hash.Blake2.Lemmas

open Lib.IntTypes

open Spec.Hash.Lemmas
open FStar.Mul
open FStar.Math.Lemmas
open Hacl.Hash.Definitions

friend Spec.Agile.Hash

#push-options "--fuel 0 --ifuel 0"

/// TODO: A lemma I could not find in FStar.Math.Lemmas -
/// note: duplicated in Spec.Hash.Incremental, Hash.Streaming.Spec.fst
let mul_zero_left_is_zero (n : int) : Lemma(0 * n = 0) = ()

module B2 = Spec.Blake2

/// Proving spec equivalence

let blake2_init_no_key_is_agile (a : hash_alg{is_blake a}) :
  Lemma(
    ((Spec.Blake2.blake2_init (to_blake_alg a) 0 Seq.empty (Spec.Blake2.max_output (to_blake_alg a))
      <: words_state' a),
      Spec.Agile.Hash.nat_to_extra_state a 0) ==
      Spec.Agile.Hash.init a) = ()

#push-options "--z3rlimit 10"

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
    // Note that we can't do multiplication over uint128 integers, which is why
    // we use uint64 then convert to the ``extra_state`` type. Also note that
    // as ``i`` is a uint32, by converting it to a uint64 we make sure there is
    // no overflow during the multiplication.
    [@inline_let] let i' : uint64 = to_u64 i in
    [@inline_let] let s = (to_u64 i) *. (cast U64 SEC (block_len a)) in
    (ev <: extra_state_int_t a) +. (cast (extra_state_int_type a) SEC s)

let add_extra_s (a:hash_alg{is_blake a}) (ev:nat) (i:nat) : nat =
  let n = match a with | Blake2S -> 64 | Blake2B -> 128 in
  (ev + (i * size_block a)) % pow2 n

#push-options "--z3rlimit 100 --z3cliopt smt.arith.nl=false"
let add_s_i (a:hash_alg{is_blake a}) (ev:extra_state a) (i:U32.t) :
  Lemma
    (extra_state_v (add_extra_i a ev i) == add_extra_s a (extra_state_v ev) (v i))
  =
  let n = match a with | Blake2S -> 64 | Blake2B -> 128 in
  let itype = extra_state_int_type a in
  let ty = extra_state_int_t a in
  let ev1 : int_t itype SEC = ev in
  let ev2 : int_t itype SEC = add_extra_i a ev i in
  assert_norm(size_block a < pow2 64);
  calc (==) {
    v (cast U64 SEC (block_len a));
    (==) { }
    (v (block_len a)) % pow2 64;
    (==) { }
    (size_block a) % pow2 64;
    (==) { modulo_lemma (block_length a) (pow2 64) }
    block_length a;
  };
  assert(cast U64 SEC (block_len a) == u64 (size_block a));
  calc (==) {
    v ev2;
    (==) { }
    v (ev1  +. cast itype SEC (to_u64 i *. (cast U64 SEC (block_len a))));
    (==) { }
    v (ev1  +. cast itype SEC (to_u64 i *. u64 (size_block a)));
    (==) { }
    ((v ev1) + v (cast itype SEC (to_u64 i *. u64 (size_block a)))) % pow2 n;
    (==) { }
    ((v ev1) + ((v (to_u64 i *. u64 (size_block a))) % pow2 n)) % pow2 n;
    (==) { lemma_mod_add_distr (v ev1) (v (to_u64 i *. u64 (size_block a))) (pow2 n) }
    ((v ev1) + (v (to_u64 i *. u64 (size_block a)))) % pow2 n;
    (==) { mul_mod_lemma (to_u64 i) (u64 (size_block a)) }
    ((v ev1) + (v (to_u64 i) * v (u64 (size_block a))) % pow2 64) % pow2 n;
    (==) {  }
    ((v ev1) + (((v i) % pow2 64) * v (u64 (size_block a))) % pow2 64) % pow2 n;
    (==) {  }
    ((v ev1) + (((v i) % pow2 64) * (size_block a)) % pow2 64) % pow2 n;
    (==) { lemma_mod_mul_distr_l (v i) (size_block a) (pow2 64) }
    ((v ev1) + (v i * size_block a) % pow2 64) % pow2 n;
  };
  assert(v i <= pow2 32 - 1);
  assert_norm(size_block a <= pow2 32 - 1);
  assert_norm((pow2 32 - 1) * (pow2 32 - 1) < pow2 64);
  lemma_mult_le_right (v i) (size_block a) (pow2 32 - 1);
  assert(v i * size_block a <= v i * (pow2 32 - 1));
  lemma_mult_le_right (pow2 32 - 1) (v i) (pow2 32 - 1);
  assert(v i * (pow2 32 - 1) <= (pow2 32 - 1) * (pow2 32 - 1));
  assert(v i * size_block a <= (pow2 32 - 1) * (pow2 32 - 1));
  assert(v i * size_block a <  pow2 64);
  nat_times_nat_is_nat (v i) (size_block a);
  modulo_lemma (v i * size_block a) (pow2 64);
  assert((v i * size_block a) % pow2 64 = v i * size_block a)
#pop-options

let add_extra_s_zero (#a:hash_alg{is_blake a}) (ev:extra_state a) :
  Lemma (add_extra_s a (extra_state_v ev) 0 == extra_state_v ev)
  = ()

let add_extra_i_zero a ev =
    add_s_i a ev 0ul;
    add_extra_s_zero ev

#push-options "--z3rlimit 100 --z3cliopt smt.arith.nl=false"
let add_extra_s_assoc (a:hash_alg{is_blake a}) (ev:nat) (i j:nat) :
  Lemma
    (add_extra_s a (add_extra_s a ev j) i == add_extra_s a ev (i + j)) =
  let n = match a with | Blake2S -> 64 | Blake2B -> 128 in
  calc (==) {
    add_extra_s a (add_extra_s a ev j) i;
    (==) { }
    ((add_extra_s a ev j) + (i * size_block a)) % pow2 n;
    (==) { }
    ((ev + (j * size_block a)) % pow2 n + (i * size_block a)) % pow2 n;
    (==) { FStar.Math.Lemmas.lemma_mod_add_distr (i * size_block a)
      (ev + (j * size_block a)) (pow2 n) }
    (ev + i * size_block a + j * size_block a) % pow2 n;
    (==) { FStar.Math.Lemmas.distributivity_add_left i j (size_block a) }
    add_extra_s a ev (i+j);
 }
#pop-options

val lemma_update_s (a:hash_alg{is_blake a}) (h:words_state a) (i:nat) (input: bytes_blocks a) :
  Lemma (requires i + 1 < pow2 32 /\ Seq.length input == i * block_length a)
        (ensures (
          let h' = update_multi a h input in
          extra_state_v (snd h') == add_extra_s a (extra_state_v (snd h)) i))
        (decreases i)

val update1_add (a:hash_alg{is_blake a}) (h:words_state a)
                (l:bytes{Seq.length l == block_length a})
  : Lemma
  (let h' = update a h l in
   let _, ev = h in
   let _, ev' = h' in
   ev' == add_extra_i a ev 1ul)
let update1_add a h l =
  mul_mod_lemma (to_u64 1ul) (u64 (size_block a))

#restart-solver
#push-options "--fuel 1 --z3rlimit 50 --z3cliopt smt.arith.nl=false"

let rec lemma_update_s a h i input =
  let ev = snd h in
  let h' = update_multi a h input in
  let ev' = snd h' in

  if i = 0 then
    begin
    mul_zero_left_is_zero (block_length a);
    assert(Seq.length input = 0);
    assert(input `Seq.equal` Seq.empty);
    update_multi_zero a h;
    add_extra_s_zero ev
    end
  else
    begin
    Math.Lemmas.cancel_mul_div i (block_length a);
    assert(1 <= Seq.length input / block_length a);
    let block, rem = Lib.UpdateMulti.split_block (block_length a) input 1 in
    let h_mid = update a h block in
    let h_f = update_multi a h_mid rem in

    let ev_mid = snd h_mid in
    let ev_f = snd h_f in

    let itype = extra_state_int_type a in

    (* For the recursive call *)
    Math.Lemmas.distributivity_sub_left i 1 (block_length a);
    assert(Seq.length rem == (i-1) * block_length a);

    calc (==) {
      v #itype #SEC ev';
      (==) { }
      v #itype #SEC ev_f;
      (==) { lemma_update_s a h_mid (i-1) rem }
      add_extra_s a (v #itype #SEC ev_mid) (i-1);
      (==) { update1_add a h block }
      add_extra_s a (v #itype #SEC (add_extra_i a ev 1ul)) (i-1);
      (==) { calc (==) {
        v #itype #SEC (add_extra_i a ev 1ul);
        (==) { add_s_i a ev 1ul }
        add_extra_s a (v #itype #SEC ev) 1;
          }
        }
      add_extra_s a (add_extra_s a (v #itype #SEC ev) 1) (i-1);
      (==) { add_extra_s_assoc a (v #itype #SEC ev) (i-1) 1 }
      add_extra_s a (v #itype #SEC ev) i;
    }
    end

#pop-options

let update_multi_add_extra a h i input =
  let ev = snd h in
  let h' = update_multi a h input in
  let ev' = snd h' in
  add_s_i a ev (U32.uint_to_t i);
  lemma_update_s a h i input
#pop-options
