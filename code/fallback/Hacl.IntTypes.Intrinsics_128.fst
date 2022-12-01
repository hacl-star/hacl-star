module Hacl.IntTypes.Intrinsics_128

open Hacl.IntTypes.Intrinsics

open Lib.IntTypes
open Lib.Buffer

(* Versions of add_carry_u64 and sub_borrow_u64 that rely on uint128 *)

#set-options "--fuel 0 --ifuel 0 --z3rlimit 200"

val add_carry_u64: add_carry_st U64
let add_carry_u64 cin x y r =
  let res = to_u128 x +. to_u128 cin +. to_u128 y in
  let c = to_u64 (res >>. 64ul) in
  r.(0ul) <- to_u64 res;
  c

val sub_borrow_u64: sub_borrow_st U64
let sub_borrow_u64 cin x y r =
  let res = to_u128 x -. to_u128 y -. to_u128 cin in
  assert (v res == ((v x - v y) % pow2 128 - v cin) % pow2 128);
  Math.Lemmas.lemma_mod_add_distr (- v cin) (v x - v y) (pow2 128);
  assert (v res == (v x - v y - v cin) % pow2 128);

  assert (v res % pow2 64 = (v x - v y - v cin) % pow2 128 % pow2 64);
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (v x - v y - v cin) 64 128;
  assert (v res % pow2 64 = (v x - v y - v cin) % pow2 64);

  let c = to_u64 (res >>. 64ul) &. u64 1 in
  assert_norm (pow2 1 = 2);
  mod_mask_lemma (to_u64 (res >>. 64ul)) 1ul;
  assert (v ((mk_int #U64 #SEC 1 <<. 1ul) -! mk_int 1) == 1);
  assert (v c = v res / pow2 64 % pow2 1);

  r.(0ul) <- to_u64 res;
  assert (v c = (if 0 <= v x - v y - v cin then 0 else 1));
  c
