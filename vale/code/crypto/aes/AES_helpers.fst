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


let finish_cipher_opt (alg:algorithm) (input plain t0 t1 out:quad32) (round_keys:seq quad32) : Lemma
  (requires length round_keys == (nr alg) + 1 /\
            length round_keys > 0 /\ nr alg > 1 /\   // REVIEW: Why are these needed?
            t0 = quad32_xor input (index round_keys 0) /\
            t1 = rounds_opaque t0 round_keys (nr alg - 1) /\
            out = quad32_xor (sub_bytes (shift_rows_LE t1)) (quad32_xor plain (index round_keys (nr alg))))
  (ensures out == quad32_xor plain (cipher_opaque alg input round_keys))
  =
  calc (==) {
    out;
    == {} // From requires
    quad32_xor (sub_bytes (shift_rows_LE t1)) (quad32_xor plain (index round_keys (nr alg)));
    == { Arch.TypesNative.lemma_quad32_xor_commutes plain (index round_keys (nr alg)) }
    quad32_xor (sub_bytes (shift_rows_LE t1)) (quad32_xor (index round_keys (nr alg)) plain);
    == { Arch.TypesNative.lemma_quad32_xor_associates (sub_bytes (shift_rows_LE t1)) (index round_keys (nr alg)) plain }
    quad32_xor (quad32_xor (sub_bytes (shift_rows_LE t1)) (index round_keys (nr alg))) plain;
    == { reveal_opaque rounds;
         reveal_opaque cipher;
         commute_sub_bytes_shift_rows_forall();
         reveal_opaque quad32_xor_def
       }
    quad32_xor (cipher_opaque alg input round_keys) plain;
    == { Arch.TypesNative.lemma_quad32_xor_commutes plain (cipher_opaque alg input round_keys) }
    quad32_xor plain (cipher_opaque alg input round_keys);
  };
  ()
#pop-options  

#reset-options "--z3rlimit 20"
let lemma_add_0x1000000_reverse_mult (n:nat32) (increment:nat) : Lemma
  (requires (n % 256) + increment < 256)
  (ensures (let r = reverse_bytes_nat32 n in
            r + increment * 0x1000000 == reverse_bytes_nat32 (n + increment)))
  =
  let r = reverse_bytes_nat32 n in
  assert_norm (Words.Four_s.nat_to_four 8 (n+increment) == Mkfour ((n+increment) % 0x100) (((n+increment) / 0x100) % 0x100) (((n+increment) / 0x10000) % 0x100) (((n+increment) / 0x1000000) % 0x100)); 
  assert ((n+increment) / 0x1000000 == n / 0x1000000);
  assert ((n+increment) / 0x10000 == n / 0x10000);
  assert ((n+increment) / 0x100 == n / 0x100);
  assert      (Words.Four_s.nat_to_four 8 (n+increment) == Mkfour ((n+increment) % 0x100) ((n / 0x100) % 0x100) ((n / 0x10000) % 0x100) ((n / 0x1000000) % 0x100)); 
  
  assert_norm (Words.Four_s.nat_to_four 8 n     == Mkfour (n % 0x100)     ((n / 0x100) % 0x100) ((n / 0x10000) % 0x100) ((n / 0x1000000) % 0x100)); 
  let s = Words.Seq_s.four_to_seq_BE (Words.Four_s.nat_to_four 8 n) in
  let r_s = Collections.Seqs_s.reverse_seq s in
  assert_norm (be_bytes_to_nat32 r_s == ((n / 0x1000000) % 0x100) + 
                                        ((n / 0x10000) % 0x100) * 0x100 +
                                        ((n / 0x100) % 0x100) * 0x10000 +
                                        (n % 0x100) * 0x1000000);
  let s' = Words.Seq_s.four_to_seq_BE (Words.Four_s.nat_to_four 8 (n+increment)) in
  let r_s' = Collections.Seqs_s.reverse_seq s' in
  
  assert_norm (be_bytes_to_nat32 r_s' == (((n) / 0x1000000) % 0x100) + 
                                        (((n) / 0x10000) % 0x100) * 0x100 +
                                        (((n) / 0x100) % 0x100) * 0x10000 +
                                        ((n+increment) % 0x100) * 0x1000000);
  assert (be_bytes_to_nat32 r_s + increment * 0x1000000 == be_bytes_to_nat32 r_s');
  calc (==) {
     r;
     == { reveal_opaque reverse_bytes_nat32_def }
     be_bytes_to_nat32 r_s;
  };
  calc (==) {
    reverse_bytes_nat32 (n+increment);
    ==  { reveal_opaque reverse_bytes_nat32_def }
    be_bytes_to_nat32 (Collections.Seqs_s.reverse_seq (nat32_to_be_bytes (n+increment)));
  };
  ()

#reset-options ""
let lemma_incr_msb (orig ctr ctr':quad32) (increment:nat) : Lemma
  (requires increment < 256 /\
            ctr == reverse_bytes_quad32 orig /\
            ctr' == Arch.Types.add_wrap_quad32 ctr (Mkfour 0 0 0 (increment * 0x1000000)))
  (ensures  (orig.lo0 % 256) + increment < 256 ==> ctr' == reverse_bytes_quad32 (GCTR_s.inc32 orig increment))
  =
  let ctr_new = GCTR_s.inc32 orig increment in
  reveal_reverse_bytes_quad32 orig;
  reveal_reverse_bytes_quad32 ctr_new;
  if (orig.lo0 % 256) + increment < 256 then (
    lemma_add_0x1000000_reverse_mult orig.lo0 increment;
    ()
  ) else ();
  ()


let lemma_msb_in_bounds (ctr_BE inout5 t1':quad32) (counter:nat) : Lemma
  (requires inout5 == reverse_bytes_quad32 (GCTR_s.inc32 ctr_BE 5) /\
            counter == ctr_BE.lo0 % 256 /\
            counter + 6 < 256 /\
            t1' == Arch.Types.add_wrap_quad32 inout5 (Mkfour 0 0 0 0x1000000))
  (ensures  t1' == reverse_bytes_quad32 (GCTR_s.inc32 ctr_BE 6))
  =
  let ctr5 = GCTR_s.inc32 ctr_BE 5 in
  let ctr6 = GCTR_s.inc32 ctr_BE 6 in
  reveal_reverse_bytes_quad32 ctr5;
  reveal_reverse_bytes_quad32 ctr6;
  let r5 = reverse_bytes_quad32 ctr5 in
  let r6 = reverse_bytes_quad32 ctr6 in
  assert (ctr_BE.lo0 + 6 < pow2_32);  
  assert (ctr6.lo0 == ctr5.lo0 + 1);
  calc (==) {
    r6; 
    == {} 
    Mkfour (reverse_bytes_nat32 ctr6.hi3) (reverse_bytes_nat32 ctr6.hi2) (reverse_bytes_nat32 ctr6.lo1) (reverse_bytes_nat32 ctr6.lo0);
    == {}
    Mkfour (reverse_bytes_nat32 ctr5.hi3) (reverse_bytes_nat32 ctr5.hi2) (reverse_bytes_nat32 ctr5.lo1) (reverse_bytes_nat32 ctr6.lo0);
    == {}
    Mkfour (reverse_bytes_nat32 ctr5.hi3) (reverse_bytes_nat32 ctr5.hi2) (reverse_bytes_nat32 ctr5.lo1) (reverse_bytes_nat32 (ctr5.lo0 + 1));
    == {}
    Mkfour inout5.lo0 inout5.lo1 inout5.hi2 (reverse_bytes_nat32 (ctr5.lo0 + 1));
    == { lemma_add_0x1000000_reverse_mult ctr5.lo0 1 }
    t1';
  };  
  ()
            
