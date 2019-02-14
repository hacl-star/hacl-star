module AES_helpers

open Opaque_s
open Words_s
open Types_s
open FStar.Seq
open AES_s
open FStar.Mul

// syntax for seq accesses, s.[index] and s.[index] <- value
unfold
let op_String_Access (#a:Type) (s:seq a) (i:nat{ i < length s}) : Tot a = index s i

unfold
let op_String_Assignment = Seq.upd

unfold let ( *^ ) = nat32_xor
unfold let ( *^^ ) = quad32_xor

let quad32_shl32 (q:quad32) : quad32 =
  let Mkfour v0 v1 v2 v3 = q in
  Mkfour 0 v0 v1 v2


// Redefine key expansion in terms of quad32 values rather than nat32 values,
// then prove both definitions are equivalent.

let round_key_128_rcon (prev:quad32) (rcon:nat32) : quad32 =
  let Mkfour v0 v1 v2 v3 = prev in
  let w0 = v0 *^ (sub_word (rot_word_LE v3) *^ rcon) in
  let w1 = v1 *^ w0 in
  let w2 = v2 *^ w1 in
  let w3 = v3 *^ w2 in
  Mkfour w0 w1 w2 w3

let round_key_128 (prev:quad32) (round:nat) : quad32 =
  round_key_128_rcon prev (aes_rcon (round - 1))

let rec expand_key_128_def (key:seq nat32) (round:nat) : Pure quad32
  (requires is_aes_key_LE AES_128 key)
  (ensures fun _ -> True)
  =
  if round = 0 then Mkfour key.[0] key.[1] key.[2] key.[3]
  else round_key_128 (expand_key_128_def key (round - 1)) round

let expand_key_128 = make_opaque expand_key_128_def

val lemma_expand_key_128_0 (key:aes_key_LE AES_128) : Lemma
  (equal key (expand_key AES_128 key 4))

val lemma_expand_key_128_i (key:aes_key_LE AES_128) (i:nat) : Lemma
  (requires
    0 < i /\ i < 11
  )
  (ensures (
    let m = 4 * (i - 1) in
    let n = 4 * i in
    let v = expand_key AES_128 key n in
    let w = expand_key AES_128 key (n + 4) in
    let prev =              Mkfour v.[m + 0] v.[m + 1] v.[m + 2] v.[m + 3] in
    round_key_128 prev i == Mkfour w.[n + 0] w.[n + 1] w.[n + 2] w.[n + 3]
  ))

// expand_key for large 'size' argument agrees with expand_key for smaller 'size' argument
val lemma_expand_append (key:aes_key_LE AES_128) (size1:nat) (size2:nat) : Lemma
  (requires size1 <= size2 /\ size2 <= 44)
  (ensures equal (expand_key AES_128 key size1) (slice (expand_key AES_128 key size2) 0 size1))
  (decreases size2)

// quad32 key expansion is equivalent to nat32 key expansion
val lemma_expand_key_128 (key:seq nat32) (size:nat) : Lemma
  (requires size <= 11 /\ is_aes_key_LE AES_128 key)
  (ensures (
    let s = key_schedule_to_round_keys size (expand_key AES_128 key 44) in
    (forall (i:nat).{:pattern (expand_key_128 key i) \/ (expand_key_128_def key i)}
      i < size ==> expand_key_128 key i == s.[i])
  ))

// Refine round_key_128 to a SIMD computation
let simd_round_key_128 (prev:quad32) (rcon:nat32) : quad32 =
  let r = rot_word_LE (sub_word prev.hi3) *^ rcon in
  let q = prev in
  let q = q *^^ quad32_shl32 q in
  let q = q *^^ quad32_shl32 q in
  let q = q *^^ quad32_shl32 q in
  q *^^ Mkfour r r r r

// SIMD version of round_key_128 is equivalent to scalar round_key_128
val lemma_simd_round_key (prev:quad32) (rcon:nat32) : Lemma
  (simd_round_key_128 prev rcon == round_key_128_rcon prev rcon)

val commute_sub_bytes_shift_rows_forall (_:unit) :
  Lemma
    (forall q.{:pattern sub_bytes (shift_rows_LE q) \/ shift_rows_LE (sub_bytes q)}
      sub_bytes (shift_rows_LE q) == shift_rows_LE (sub_bytes q))

let rounds_opaque = make_opaque rounds
let cipher_opaque = make_opaque cipher

val init_rounds_opaque (init:quad32) (round_keys:seq quad32) :
  Lemma (length round_keys > 0 ==> rounds_opaque init round_keys 0 == init)

val finish_cipher (alg:algorithm) (input:quad32) (round_keys:seq quad32) :
  Lemma
    (length round_keys == (nr alg) + 1 ==>
        length round_keys > 0 /\ nr alg > 1 /\   // REVIEW: Why are these needed?
           (let state = quad32_xor input (index round_keys 0) in
            let state = rounds_opaque state round_keys (nr alg - 1) in
            let state = shift_rows_LE state in
            let state = sub_bytes state in
            let state = quad32_xor state (index round_keys (nr alg)) in
            state == cipher_opaque alg input round_keys))


val finish_cipher_opt (alg:algorithm) (input plain t0 t1 out:quad32) (round_keys:seq quad32) : Lemma
  (requires length round_keys == (nr alg) + 1 /\
            length round_keys > 0 /\ nr alg > 1 /\   // REVIEW: Why are these needed?
            t0 = quad32_xor input (index round_keys 0) /\
            t1 = rounds_opaque t0 round_keys (nr alg - 1) /\
            out = quad32_xor (sub_bytes (shift_rows_LE t1)) (quad32_xor plain (index round_keys (nr alg))))
  (ensures out == quad32_xor plain (cipher_opaque alg input round_keys))
(*
val finish_cipher_opt (alg:algorithm) (input plain:quad32) (round_keys:seq quad32) :
  Lemma
    (length round_keys == (nr alg) + 1 ==>
        length round_keys > 0 /\ nr alg > 1 /\   // REVIEW: Why are these needed?
           (let state = quad32_xor input (index round_keys 0) in
            let state = rounds_opaque state round_keys (nr alg - 1) in
            let state = shift_rows_LE state in
            let state = sub_bytes state in
            let state = quad32_xor state (quad32_xor plain (index round_keys (nr alg))) in
            state == quad32_xor plain (cipher_opaque alg input round_keys)))
*)


(*
open FStar.Calc
let lemma_reverse_bytes_nat32_byte (n:nat32) :
  Lemma ( (reverse_bytes_nat32 n) / 0x1000000 == n % pow2_8)
  =
  calc (==) {
    reverse_bytes_nat32 n;
    ==  { reveal_opaque reverse_bytes_nat32_def }
    be_bytes_to_nat32 (Collections.Seqs_s.reverse_seq (nat32_to_be_bytes n));
  };  
  
  assert (pow2_norm 8 == pow2_8);
  assert (pow2_norm 24 == 0x1000000);  
  assert_norm ((Words.Four_s.nat_to_four 8 n).hi3 == (n / 0x1000000) % pow2_8);
  assert ((n / 0x1000000) % pow2_8 == n / 0x1000000);

  let s = Collections.Seqs_s.reverse_seq (nat32_to_be_bytes n) in
  assert (index s 3 == n / 0x1000000);
  // TODO
  ()
*)

(*
let lemma_add_0x1000000_reverse (n:nat32) : Lemma
  (requires n % 256 < 255)
  (ensures (let r = reverse_bytes_nat32 n in
            r + 0x1000000 == reverse_bytes_nat32 (n + 1)))
  =
  let r = reverse_bytes_nat32 n in
  assert_norm (Words.Four_s.nat_to_four 8 (n+1) == Mkfour ((n+1) % 0x100) (((n+1) / 0x100) % 0x100) (((n+1) / 0x10000) % 0x100) (((n+1) / 0x1000000) % 0x100)); 
  assert ((n+1) / 0x1000000 == n / 0x1000000);
  assert ((n+1) / 0x10000 == n / 0x10000);
  assert ((n+1) / 0x100 == n / 0x100);
  assert      (Words.Four_s.nat_to_four 8 (n+1) == Mkfour ((n+1) % 0x100) ((n / 0x100) % 0x100) ((n / 0x10000) % 0x100) ((n / 0x1000000) % 0x100)); 
  
  assert_norm (Words.Four_s.nat_to_four 8 n     == Mkfour (n % 0x100)     ((n / 0x100) % 0x100) ((n / 0x10000) % 0x100) ((n / 0x1000000) % 0x100)); 
  let s = Words.Seq_s.four_to_seq_BE (Words.Four_s.nat_to_four 8 n) in
  let r_s = Collections.Seqs_s.reverse_seq s in
  assert_norm (be_bytes_to_nat32 r_s == ((n / 0x1000000) % 0x100) + 
                                        ((n / 0x10000) % 0x100) * 0x100 +
                                        ((n / 0x100) % 0x100) * 0x10000 +
                                        (n % 0x100) * 0x1000000);
  let s' = Words.Seq_s.four_to_seq_BE (Words.Four_s.nat_to_four 8 (n+1)) in
  let r_s' = Collections.Seqs_s.reverse_seq s' in
  
  assert_norm (be_bytes_to_nat32 r_s' == (((n) / 0x1000000) % 0x100) + 
                                        (((n) / 0x10000) % 0x100) * 0x100 +
                                        (((n) / 0x100) % 0x100) * 0x10000 +
                                        ((n+1) % 0x100) * 0x1000000);
  assert (be_bytes_to_nat32 r_s + 0x1000000 == be_bytes_to_nat32 r_s');
  calc (==) {
     r;
     == { reveal_opaque reverse_bytes_nat32_def }
     be_bytes_to_nat32 r_s;
  };
  calc (==) {
    reverse_bytes_nat32 (n + 1);
    ==  { reveal_opaque reverse_bytes_nat32_def }
    be_bytes_to_nat32 (Collections.Seqs_s.reverse_seq (nat32_to_be_bytes (n + 1)));
  };
  ()
*)
let lemma_add_0x1000000_reverse_mult (n:nat32) (increment:nat) : Lemma
  (requires (n % 256) + increment < 256 /\ increment < 6)
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

let lemma_incr_msb (orig ctr ctr':quad32) (increment:nat) : Lemma
  (requires increment < 6 /\
            ctr == reverse_bytes_quad32 orig /\
            ctr' == Arch.Types.add_wrap_quad32 ctr (Mkfour 0 0 0 (increment * 0x1000000)))
  (ensures  (orig.lo0 % 256) + 6 < 256 ==> ctr' == reverse_bytes_quad32 (GCTR_s.inc32 orig increment))
  =
  let ctr_new = GCTR_s.inc32 orig increment in
  reveal_reverse_bytes_quad32 orig;
  reveal_reverse_bytes_quad32 ctr_new;
  if (orig.lo0 % 256) + 6 < 256 then (
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
            
