module AES_helpers

open Opaque_s
open Words_s
open Types_s
open FStar.Seq
open AES_s
open FStar.Mul

#reset-options "--initial_fuel 4 --max_fuel 4 --max_ifuel 0"
let lemma_expand_key_128_0 (key:aes_key_LE AES_128) =
  reveal_opaque expand_key_def

#reset-options "--initial_fuel 1 --max_fuel 1 --max_ifuel 0 --z3rlimit 10"
let lemma_expand_key_128_i (key:aes_key_LE AES_128) (i:nat) =
  reveal_opaque expand_key_def;
  let n = 4 * i in
  // unfold expand_key 4 times (could use fuel, but that unfolds everything):
  let _ = expand_key AES_128 key (n + 1) in
  let _ = expand_key AES_128 key (n + 2) in
  let _ = expand_key AES_128 key (n + 3) in
  ()
#reset-options

// expand_key for large 'size' argument agrees with expand_key for smaller 'size' argument
let rec lemma_expand_append (key:aes_key_LE AES_128) (size1:nat) (size2:nat) =
  reveal_opaque expand_key_def;
  if size1 < size2 then lemma_expand_append key size1 (size2 - 1)

#reset-options "--initial_fuel 1 --max_fuel 1 --max_ifuel 0 --z3rlimit 20 --using_facts_from '* -FStar.Seq.Properties'"
// quad32 key expansion is equivalent to nat32 key expansion
let rec lemma_expand_key_128 (key:seq nat32) (size:nat) =
  reveal_opaque expand_key_128_def;
  lemma_expand_append key (4 * size) 44;
  if size = 0 then ()
  else
  (
    let i = size - 1 in
    lemma_expand_append key (4 * i) 44;
    lemma_expand_key_128 key i;
    if i = 0 then lemma_expand_key_128_0 key
    else lemma_expand_key_128_i key i
  )
#reset-options

// SIMD version of round_key_128 is equivalent to scalar round_key_128
#push-options "--max_fuel 3 --initial_fuel 3 --max_ifuel 3 --initial_ifuel 3"  // REVIEW: Why do we need this?
let lemma_simd_round_key (prev:quad32) (rcon:nat32) =
  reveal_opaque quad32_xor_def;
  reveal_opaque reverse_bytes_nat32_def;  
  commute_rot_word_sub_word prev.hi3;
  Arch.Types.xor_lemmas ()
#pop-options

let commute_sub_bytes_shift_rows_forall () =
  FStar.Classical.forall_intro commute_sub_bytes_shift_rows

let init_rounds_opaque (init:quad32) (round_keys:seq quad32) =
  reveal_opaque rounds

#push-options "--max_ifuel 2 --initial_ifuel 2"  // REVIEW: Why do we need this?  Extra inversion to deal with opaque?
let finish_cipher (alg:algorithm) (input:quad32) (round_keys:seq quad32) =
  reveal_opaque rounds;
  reveal_opaque cipher;
  commute_sub_bytes_shift_rows_forall()
#pop-options  
