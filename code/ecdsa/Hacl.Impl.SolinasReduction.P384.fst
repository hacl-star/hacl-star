module Hacl.Impl.SolinasReduction.P384

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open FStar.Math.Lemmas
open FStar.Math.Lib
open Lib.Buffer

open Spec.ECC
open Hacl.Spec.EC.Definition
open Hacl.Impl.EC.LowLevel

open FStar.Mul

module BV = FStar.BitVector
module Seq = FStar.Seq


#set-options "--fuel 0 --ifuel 0 --z3rlimit 500"
(* http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.46.2133&rep=rep1&type=pdf *)


inline_for_extraction noextract
val get_high_part: a:uint64 -> r:uint32{uint_v r == uint_v a / pow2 32}
let get_high_part a = to_u32 (shift_right a (size 32))

inline_for_extraction noextract
val get_low_part: a:uint64 -> r:uint32{uint_v r == uint_v a % pow2 32}
let get_low_part a = to_u32 a


val shift_bound: #n:nat -> num:UInt.uint_t n -> n':nat ->
  Lemma (num * pow2 n' <= pow2 (n' + n) - pow2 n')

let shift_bound #n num n' =
  Math.Lemmas.lemma_mult_le_right (pow2 n') num (pow2 n - 1);
  Math.Lemmas.distributivity_sub_left (pow2 n) 1 (pow2 n');
  Math.Lemmas.pow2_plus n' n


val logxor_vec_append (#n1 #n2: pos) (a1 b1: BV.bv_t n1) (a2 b2: BV.bv_t n2) :
  Lemma (Seq.append (BV.logxor_vec a1 b1) (BV.logxor_vec a2 b2) ==
         BV.logxor_vec #(n1 + n2) (FStar.Seq.append a1 a2) (FStar.Seq.append b1 b2))

let logxor_vec_append #n1 #n2 a1 b1 a2 b2 =
  Seq.lemma_eq_intro (Seq.append (BV.logxor_vec a1 b1) (BV.logxor_vec a2 b2))
                     (BV.logxor_vec #(n1 + n2) (Seq.append a1 a2) (Seq.append b1 b2))

val append_uint: #n1:nat -> #n2:nat
  -> num1:UInt.uint_t n1 -> num2:UInt.uint_t n2 -> UInt.uint_t (n1 + n2)

let append_uint #n1 #n2 num1 num2 =
  shift_bound num2 n1;
  num1 + num2 * pow2 n1

val to_vec_append : #n1:pos-> #n2:pos -> num1:UInt.uint_t n1 -> num2:UInt.uint_t n2 ->
  Lemma (UInt.to_vec (append_uint num1 num2) ==
         Seq.append (UInt.to_vec num2) (UInt.to_vec num1))

let to_vec_append #n1 #n2 num1 num2 =
  UInt.append_lemma (UInt.to_vec num2) (UInt.to_vec num1)

val to_vec_low_high: a:UInt.uint_t 64 -> Lemma
  (UInt.to_vec a ==
   Seq.append (UInt.to_vec #32 (a / pow2 32)) (UInt.to_vec #32 (a % pow2 32)))

let to_vec_low_high a =
  assert (a == append_uint #32 #32 (a % pow2 32) (a / pow2 32));
  to_vec_append #32 #32 (a % pow2 32) (a / pow2 32)


val lemma_xor_zero:
    low:  uint64{v (get_high_part low) == 0}
  -> high: uint64{v (get_low_part high) == 0}
  -> Lemma (v (logxor low high) = v high + v low)

let lemma_xor_zero l h =
  to_vec_low_high (v h);
  to_vec_low_high (v l);
  let a1 = BV.zero_vec #32 in
  let a2 = UInt.to_vec #32 (v l % pow2 32) in
  let b1 = UInt.to_vec #32 (v h / pow2 32) in
  let b2 = BV.zero_vec #32 in
  assert (Seq.equal (UInt.to_vec (UInt.zero 32)) (BV.zero_vec #32));
  assert (UInt.to_vec #64 (UInt.logxor (v l) (v h)) ==
          BV.logxor_vec (Seq.append a1 a2) (Seq.append b1 b2));
  logxor_vec_append a1 b1 a2 b2;
  assert (Seq.equal (BV.logxor_vec a1 b1) b1);
  assert (Seq.equal (BV.logxor_vec a2 b2) a2);
  UInt.append_lemma b1 a2;
  logxor_spec l h


val store_high_low_u: high:uint32 -> low:uint32 -> r:uint64{v r = v high * pow2 32 + v low}

let store_high_low_u high low =
  let as_uint64_high = to_u64 high in
  let as_uint64_high = Lib.IntTypes.shift_left as_uint64_high (size 32) in
  let as_uint64_low = to_u64 low in
  assert (v as_uint64_high = v high * pow2 32);
  assert (v as_uint64_low = v low);
  lemma_xor_zero as_uint64_low as_uint64_high;
  logxor as_uint64_low as_uint64_high


#push-options "--fuel 1"

inline_for_extraction noextract
val load_buffer: a0: uint64 -> a1: uint64 -> a2: uint64 -> a3: uint64 -> a4: uint64 -> a5: uint64 
  -> o: lbuffer uint64 (size 6) ->
  Stack unit
  (requires fun h -> live h o)
  (ensures  fun h0 _ h1 -> modifies (loc o) h0 h1 /\
    as_nat P384 h1 o = v a0  + v a1 * pow2 (2 * 32) + v a2 * pow2 (4 * 32) + v a3 * pow2 (6 * 32) + v a4 * pow2 (8 * 32) + v a5 * pow2 (10 * 32))


let load_buffer a0 a1 a2 a3 a4 a5 o =
  upd o (size 0) a0;
  upd o (size 1) a1;
  upd o (size 2) a2;
  upd o (size 3) a3;
  upd o (size 4) a4;
  upd o (size 5) a5;

  let h0 = ST.get() in 

  let o_seq = as_seq h0 o in 
  lseq_as_nat_zero o_seq;
  lseq_as_nat_definiton o_seq 1;
  lseq_as_nat_definiton o_seq 2;
  lseq_as_nat_definiton o_seq 3;
  lseq_as_nat_definiton o_seq 4;
  lseq_as_nat_definiton o_seq 5;


  assert_norm(pow2 (2 * 32) = pow2 64);
  assert_norm(pow2 (4 * 32) = pow2 (64 * 2));
  assert_norm(pow2 (6 * 32) = pow2 (64 * 3));
  assert_norm(pow2 (8 * 32) = pow2 (64 * 4));
  assert_norm(pow2 (10 * 32) = pow2 (64 * 5))

#pop-options


val upl_zer_buffer: c0: uint32 -> c1: uint32 ->  c2: uint32 -> c3: uint32 -> c4: uint32 -> c5: uint32 -> c6: uint32 
  -> c7: uint32 -> c8: uint32 -> c9: uint32 -> c10: uint32 -> c11: uint32 -> o: lbuffer uint64 (size 6) ->
  Stack unit
  (requires fun h -> live h o)
  (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\
    as_nat P384 h1 o == (v c0 + v c1 * pow2 (1 * 32) + v c2 * pow2 (2 * 32) + v c3 * pow2 (3 * 32) + v c4 * pow2 (4 * 32) + v c5 * pow2 (5 * 32) + v c6 * pow2 (6 * 32) + v c7 * pow2 (7 * 32) + v c8 * pow2 (8 * 32) + v c9 * pow2 (9 * 32) + v c10 * pow2 (10 * 32) + v c11 * pow2 (11 * 32)) % getPrime P384)


let upl_zer_buffer c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 o =
  assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
  assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
  assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
  assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
  assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
  assert_norm (pow2 (6 * 32) * pow2 (2 * 32) = pow2 (8 * 32));
  assert_norm (pow2 (7 * 32) * pow2 (2 * 32) = pow2 (9 * 32));
  assert_norm (pow2 (8 * 32) * pow2 (2 * 32) = pow2 (10 * 32));
  assert_norm (pow2 (9 * 32) * pow2 (2 * 32) = pow2 (11 * 32));


  let a0 = store_high_low_u c1 c0 in
  let a1 = store_high_low_u c3 c2 in
  let a2 = store_high_low_u c5 c4 in
  let a3 = store_high_low_u c7 c6 in
  let a4 = store_high_low_u c9 c8 in
  let a5 = store_high_low_u c11 c10 in

  load_buffer a0 a1 a2 a3 a4 a5 o;
  reduction_prime_2prime #P384 o o


val upl_fir_buffer: c21: uint32 -> c22: uint32 -> c23: uint32 -> o: lbuffer uint64 (size 6) ->
  Stack unit
    (requires fun h -> live h o)
    (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\
      as_nat P384 h1 o == (v c21 * pow2 (4 * 32) + v c22 * pow2 (5 * 32) + v c23 * pow2 (6 * 32)) % getPrime P384)

let upl_fir_buffer c21 c22 c23 o =
  assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
  assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));  assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
  assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
  assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));

  let b0 = store_high_low_u (u32 0) (u32 0) in
  let b1 = store_high_low_u (u32 0) (u32 0) in
  let b2 = store_high_low_u c22 c21 in
  let b3 = store_high_low_u (u32 0) c23 in
  let b4 = store_high_low_u (u32 0) (u32 0) in
  let b5 = store_high_low_u (u32 0) (u32 0) in

  load_buffer b0 b1 b2 b3 b4 b5 o;
    let h1 = ST.get() in
    assert_norm (pow2 (7 * 32) < prime384);
  modulo_lemma (as_nat P384 h1 o) prime384


val upl_sec_buffer: c12: uint32 -> c13: uint32 -> c14: uint32 -> c15: uint32 -> c16: uint32 -> c17: uint32 -> c18: uint32 -> c19: uint32 -> c20: uint32 -> c21: uint32 -> c22: uint32 -> c23: uint32 ->
o: lbuffer uint64 (size 6) ->
  Stack unit
    (requires fun h -> live h o)
    (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\
      as_nat P384 h1 o == (v c12 + v c13 * pow2 (1 * 32) + v c14 * pow2 (2 * 32) + v c15 * pow2 (3 * 32) + v c16 * pow2 (4 * 32) + v c17 * pow2 (5 * 32) + v c18 * pow2 (6 * 32) + v c19 * pow2 (7 * 32) + v c20 * pow2 (8 * 32) + v c21 * pow2 (9 * 32) + v c22 * pow2 (10 * 32) + v c23 * pow2 (11 * 32)) % prime384)

let upl_sec_buffer c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 o =
  assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
  assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
  assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
  assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
  assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
  assert_norm (pow2 (6 * 32) * pow2 (2 * 32) = pow2 (8 * 32));
  assert_norm (pow2 (7 * 32) * pow2 (2 * 32) = pow2 (9 * 32));
  assert_norm (pow2 (8 * 32) * pow2 (2 * 32) = pow2 (10 * 32));
  assert_norm (pow2 (9 * 32) * pow2 (2 * 32) = pow2 (11 * 32));

  let b0 = store_high_low_u c13 c12 in
  let b1 = store_high_low_u c15 c14 in
  let b2 = store_high_low_u c17 c16 in
  let b3 = store_high_low_u c19 c18 in
  let b4 = store_high_low_u c21 c20 in
  let b5 = store_high_low_u c23 c22 in

  load_buffer b0 b1 b2 b3 b4 b5 o;
  reduction_prime_2prime #P384 o o


val upl_thi_buffer: c12: uint32 -> c13: uint32 -> c14: uint32 -> c15: uint32 -> c16: uint32 -> c17: uint32 -> c18: uint32 -> c19: uint32 -> c20: uint32 -> c21: uint32 -> c22: uint32 -> c23: uint32 -> o: lbuffer uint64 (size 6) ->
  Stack unit
    (requires fun h -> live h o)
    (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\
      as_nat P384 h1 o = (v c21 + v c22 * pow2 (1 * 32) + v c23 * pow2 (2 * 32) + v c12 * pow2 (3 * 32) + v c13 * pow2 (4 * 32) + v c14 * pow2 (5 * 32) + v c15 * pow2 (6 * 32) + v c16 * pow2 (7 * 32) + v c17 * pow2 (8 * 32) + v c18 * pow2 (9 * 32) + v c19 * pow2 (10 * 32) + v c20 * pow2 (11 * 32)) % prime384)


let upl_thi_buffer c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 o =
  assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
  assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
  assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
  assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
  assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
  assert_norm (pow2 (6 * 32) * pow2 (2 * 32) = pow2 (8 * 32));
  assert_norm (pow2 (7 * 32) * pow2 (2 * 32) = pow2 (9 * 32));
  assert_norm (pow2 (8 * 32) * pow2 (2 * 32) = pow2 (10 * 32));
  assert_norm (pow2 (9 * 32) * pow2 (2 * 32) = pow2 (11 * 32));

  let b0 = store_high_low_u c22 c21 in
  let b1 = store_high_low_u c12 c23 in
  let b2 = store_high_low_u c14 c13 in
  let b3 = store_high_low_u c16 c15 in
  let b4 = store_high_low_u c18 c17 in
  let b5 = store_high_low_u c20 c19 in

  load_buffer b0 b1 b2 b3 b4 b5 o;
  reduction_prime_2prime #P384 o o


val upl_forth_buffer: c12: uint32 -> c13: uint32 -> c14: uint32 -> c15: uint32 -> c16: uint32 -> c17: uint32 -> c18: uint32 -> c19: uint32-> c20: uint32 -> c23: uint32 ->
o: lbuffer uint64 (size 6) ->
  Stack unit
    (requires fun h -> live h o)
    (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\
      as_nat P384 h1 o = (v c23 * pow2 (1 * 32) + v c20 * pow2 (3 * 32) + v c12 * pow2 (4 * 32) + v c13 * pow2 (5 * 32) + v c14 * pow2 (6 * 32) + v c15 * pow2 (7 * 32) + v c16 * pow2 (8 * 32) + v c17 * pow2 (9 * 32) + v c18 * pow2 (10 * 32) + v c19 * pow2 (11 * 32)) % prime384)


let upl_forth_buffer c12 c13 c14 c15 c16 c17 c18 c19 c20 c23 o =
  assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
  assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
  assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
  assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
  assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
  assert_norm (pow2 (6 * 32) * pow2 (2 * 32) = pow2 (8 * 32));
  assert_norm (pow2 (7 * 32) * pow2 (2 * 32) = pow2 (9 * 32));
  assert_norm (pow2 (8 * 32) * pow2 (2 * 32) = pow2 (10 * 32));
  assert_norm (pow2 (9 * 32) * pow2 (2 * 32) = pow2 (11 * 32));

  let b0 = store_high_low_u c23 (u32 0) in
  let b1 = store_high_low_u c20 (u32 0) in
  let b2 = store_high_low_u c13 c12 in
  let b3 = store_high_low_u c15 c14 in
  let b4 = store_high_low_u c17 c16 in
  let b5 = store_high_low_u c19 c18 in

  load_buffer b0 b1 b2 b3 b4 b5 o;
  reduction_prime_2prime #P384 o o


val upl_fif_buffer: c20: uint32 -> c21: uint32 -> c22: uint32 -> c23: uint32 ->
  o: lbuffer uint64 (size 6) ->
  Stack unit
    (requires fun h -> live h o)
    (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\
      as_nat P384 h1 o = ((v c20 * pow2 (4 * 32) + v c21 * pow2 (5 * 32) + v c22 * pow2 (6 * 32) + v c23 * pow2 (7 * 32)) % prime384))

let upl_fif_buffer c20 c21 c22 c23 o =
  assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
  assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
  assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
  assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
  assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
  assert_norm (pow2 (6 * 32) * pow2 (2 * 32) = pow2 (8 * 32));
  assert_norm (pow2 (7 * 32) * pow2 (2 * 32) = pow2 (9 * 32));
  assert_norm (pow2 (8 * 32) * pow2 (2 * 32) = pow2 (10 * 32));
  assert_norm (pow2 (9 * 32) * pow2 (2 * 32) = pow2 (11 * 32));

  let b0 = store_high_low_u (u32 0) (u32 0) in
  let b1 = store_high_low_u (u32 0) (u32 0) in
  let b2 = store_high_low_u c21 c20 in
  let b3 = store_high_low_u c23 c22 in
  let b4 = store_high_low_u (u32 0) (u32 0) in
  let b5 = store_high_low_u (u32 0) (u32 0) in

  load_buffer b0 b1 b2 b3 b4 b5 o;
  reduction_prime_2prime #P384 o o;
      let h1 = ST.get() in
  assert_norm (pow2 (8 * 32) < prime384);
  modulo_lemma (as_nat P384 h1 o) prime384


val upl_six_buffer: c20: uint32 -> c21: uint32 -> c22: uint32 -> c23: uint32 ->
  o: lbuffer uint64 (size 6) ->
  Stack unit
    (requires fun h -> live h o)
    (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\
      as_nat P384 h1 o == (v c20 + v c21 * pow2 (3 * 32) + v c22 * pow2 (4 * 32) + v c23 * pow2 (5 * 32)) % prime384)

let upl_six_buffer c20 c21 c22 c23 o =
  assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
  assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
  assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
  assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
  assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
  assert_norm (pow2 (6 * 32) * pow2 (2 * 32) = pow2 (8 * 32));
  assert_norm (pow2 (7 * 32) * pow2 (2 * 32) = pow2 (9 * 32));
  assert_norm (pow2 (8 * 32) * pow2 (2 * 32) = pow2 (10 * 32));
  assert_norm (pow2 (9 * 32) * pow2 (2 * 32) = pow2 (11 * 32));

  let b0 = store_high_low_u (u32 0) c20 in
  let b1 = store_high_low_u c21 (u32 0) in
  let b2 = store_high_low_u c23 c22 in
  let b3 = store_high_low_u (u32 0) (u32 0) in
  let b4 = store_high_low_u (u32 0) (u32 0) in
  let b5 = store_high_low_u (u32 0) (u32 0) in

  load_buffer b0 b1 b2 b3 b4 b5 o;
  reduction_prime_2prime #P384 o o;
      let h1 = ST.get() in
  assert_norm (pow2 (6 * 32) < prime384);
  modulo_lemma (as_nat P384 h1 o) prime384


val upl_sev_buffer: c12: uint32 -> c13: uint32 -> c14: uint32 -> c15: uint32 -> c16: uint32 -> c17: uint32 -> c18: uint32 -> c19: uint32 -> c20: uint32 -> c21: uint32 -> c22: uint32 -> c23: uint32 ->
  o: lbuffer uint64 (size 6) ->
  Stack unit
    (requires fun h -> live h o)
    (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\
    as_nat P384 h1 o = (v c23 + v c12 * pow2 (1 * 32) + v c13 * pow2 (2 * 32) + v c14 * pow2 (3 * 32) + v c15 * pow2 (4 * 32) + v c16 * pow2 (5 * 32) + v c17 * pow2 (6 * 32) + v c18 * pow2 (7 * 32) + v c19 * pow2 (8 * 32) + v c20 * pow2 (9 * 32) + v c21 * pow2 (10 * 32) + v c22 * pow2 (11 * 32)) % prime384)

let upl_sev_buffer c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 o =
  assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
  assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
  assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
  assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
  assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
  assert_norm (pow2 (6 * 32) * pow2 (2 * 32) = pow2 (8 * 32));
  assert_norm (pow2 (7 * 32) * pow2 (2 * 32) = pow2 (9 * 32));
  assert_norm (pow2 (8 * 32) * pow2 (2 * 32) = pow2 (10 * 32));
  assert_norm (pow2 (9 * 32) * pow2 (2 * 32) = pow2 (11 * 32));

  let b0 = store_high_low_u c12 c23 in
  let b1 = store_high_low_u c14 c13 in
  let b2 = store_high_low_u c16 c15 in
  let b3 = store_high_low_u c18 c17 in
  let b4 = store_high_low_u c20 c19 in
  let b5 = store_high_low_u c22 c21 in

  load_buffer b0 b1 b2 b3 b4 b5 o;
  reduction_prime_2prime #P384 o o


val upl_eit_buffer: c20: uint32 -> c21: uint32 -> c22: uint32 -> c23: uint32 ->
  o: lbuffer uint64 (size 6) ->
  Stack unit
    (requires fun h -> live h o)
    (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\
      as_nat P384 h1 o = (v c20 * pow2 (1 * 32) + v c21 * pow2 (2 * 32) + v c22 * pow2 (3 * 32) + v c23 * pow2 (4 * 32)) % prime384)

let upl_eit_buffer c20 c21 c22 c23 o =
  assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
  assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
  assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
  assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
  assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
  assert_norm (pow2 (6 * 32) * pow2 (2 * 32) = pow2 (8 * 32));
  assert_norm (pow2 (7 * 32) * pow2 (2 * 32) = pow2 (9 * 32));
  assert_norm (pow2 (8 * 32) * pow2 (2 * 32) = pow2 (10 * 32));
  assert_norm (pow2 (9 * 32) * pow2 (2 * 32) = pow2 (11 * 32));

  let b0 = store_high_low_u c20 (u32 0) in
  let b1 = store_high_low_u c22 c21 in
  let b2 = store_high_low_u (u32 0) c23 in
  let b3 = store_high_low_u (u32 0) (u32 0) in
  let b4 = store_high_low_u (u32 0) (u32 0) in
  let b5 = store_high_low_u (u32 0) (u32 0) in

  load_buffer b0 b1 b2 b3 b4 b5 o;
  reduction_prime_2prime #P384 o o;
      let h1 = ST.get() in
  assert_norm (pow2 (6 * 32) < prime384);
  modulo_lemma (as_nat P384 h1 o) prime384


val upl_nin_buffer: c23: uint32 ->
  o: lbuffer uint64 (size 6) ->
  Stack unit
    (requires fun h -> live h o)
    (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\
      as_nat P384 h1 o = (v c23 * pow2 (3 * 32) + v c23 * pow2 (4 * 32)) % prime384)

let upl_nin_buffer c23 o =
  assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
  assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
  assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
  assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
  assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
  assert_norm (pow2 (6 * 32) * pow2 (2 * 32) = pow2 (8 * 32));
  assert_norm (pow2 (7 * 32) * pow2 (2 * 32) = pow2 (9 * 32));
  assert_norm (pow2 (8 * 32) * pow2 (2 * 32) = pow2 (10 * 32));
  assert_norm (pow2 (9 * 32) * pow2 (2 * 32) = pow2 (11 * 32));

  let b0 = store_high_low_u (u32 0) (u32 0) in
  let b1 = store_high_low_u c23 (u32 0) in
  let b2 = store_high_low_u (u32 0) c23 in
  let b3 = store_high_low_u (u32 0) (u32 0) in
  let b4 = store_high_low_u (u32 0) (u32 0) in
  let b5 = store_high_low_u (u32 0) (u32 0) in

  load_buffer b0 b1 b2 b3 b4 b5 o;
  reduction_prime_2prime #P384 o o;
      let h1 = ST.get() in
  assert_norm (pow2 (6 * 32) < prime384);
  modulo_lemma (as_nat P384 h1 o) prime384


(* Not sure that FStar will manage to reason about such an input *)
val solinas_reduction_upload: c0: uint32 -> c1: uint32 ->  c2: uint32 ->  c3: uint32 ->
  c4: uint32 ->  c5: uint32 ->  c6: uint32 ->  c7: uint32 ->  c8: uint32 ->  c9: uint32 ->
  c10: uint32 ->  c11: uint32 ->  c12: uint32 ->  c13: uint32 ->  c14: uint32 ->  c15: uint32 ->
  c16: uint32 ->  c17: uint32 ->  c18: uint32 ->  c19: uint32 ->  c20: uint32 ->  c21: uint32 ->
  c22: uint32 ->  c23: uint32 ->
  tempBuffer: lbuffer uint64 (size 60) ->
  Stack unit
    (requires fun h -> live h tempBuffer)
    (ensures fun h0 _ h1 -> modifies (loc tempBuffer) h0 h1 /\
      (
	let t0 = as_nat P384 h1 (gsub tempBuffer (size 0) (size 6)) in
        let t1 = as_nat P384 h1 (gsub tempBuffer (size 6) (size 6)) in
        let t2 = as_nat P384 h1 (gsub tempBuffer (size 12) (size 6)) in
        let t3 = as_nat P384 h1 (gsub tempBuffer (size 18) (size 6)) in
        let t4 = as_nat P384 h1 (gsub tempBuffer (size 24) (size 6)) in
        let t5 = as_nat P384 h1 (gsub tempBuffer (size 30) (size 6)) in
        let t6 = as_nat P384 h1 (gsub tempBuffer (size 36) (size 6)) in
        let t7 = as_nat P384 h1 (gsub tempBuffer (size 42) (size 6)) in
        let t8 = as_nat P384 h1 (gsub tempBuffer (size 48) (size 6)) in
	let t9 = as_nat P384 h1 (gsub tempBuffer (size 54) (size 6)) in
	t0 = (v c0 + v c1 * pow2 (1 * 32) + v c2 * pow2 (2 * 32) + v c3 * pow2 (3 * 32) + v c4 * pow2 (4 * 32) + v c5 * pow2 (5 * 32) + v c6 * pow2 (6 * 32) + v c7 * pow2 (7 * 32) + v c8 * pow2 (8 * 32) + v c9 * pow2 (9 * 32) + v c10 * pow2 (10 * 32) + v c11 * pow2 (11 * 32)) % prime384 /\
	t1 = (v c21 * pow2 (4 * 32) + v c22 * pow2 (5 * 32) + v c23 * pow2 (6 * 32)) % prime384 /\
	t2 = (v c12 + v c13 * pow2 (1 * 32) + v c14 * pow2 (2 * 32) + v c15 * pow2 (3 * 32) + v c16 * pow2 (4 * 32) + v c17 * pow2 (5 * 32) + v c18 * pow2 (6 * 32) + v c19 * pow2 (7 * 32) + v c20 * pow2 (8 * 32) + v c21 * pow2 (9 * 32) + v c22 * pow2 (10 * 32) + v c23 * pow2 (11 * 32)) % prime384 /\
	t3 = (v c21 + v c22 * pow2 (1 * 32) + v c23 * pow2 (2 * 32) + v c12 * pow2 (3 * 32) + v c13 * pow2 (4 * 32) + v c14 * pow2 (5 * 32) + v c15 * pow2 (6 * 32) + v c16 * pow2 (7 * 32) + v c17 * pow2 (8 * 32) + v c18 * pow2 (9 * 32) + v c19 * pow2 (10 * 32) + v c20 * pow2 (11 * 32)) % prime384 /\
	t4 = (v c23 * pow2 (1 * 32) + v c20 * pow2 (3 * 32) + v c12 * pow2 (4 * 32) + v c13 * pow2 (5 * 32) + v c14 * pow2 (6 * 32) + v c15 * pow2 (7 * 32) + v c16 * pow2 (8 * 32) + v c17 * pow2 (9 * 32) + v c18 * pow2 (10 * 32) + v c19 * pow2 (11 * 32)) % prime384 /\
	t5 = (v c20 * pow2 (4 * 32) + v c21 * pow2 (5 * 32) + v c22 * pow2 (6 * 32) + v c23 * pow2 (7 * 32)) % prime384 /\
	t6 = (v c20 + v c21 * pow2 (3 * 32) + v c22 * pow2 (4 * 32) + v c23 * pow2 (5 * 32)) % prime384 /\
	t7 = (v c23 + v c12 * pow2 (1 * 32) + v c13 * pow2 (2 * 32) + v c14 * pow2 (3 * 32) + v c15 * pow2 (4 * 32) + v c16 * pow2 (5 * 32) + v c17 * pow2 (6 * 32) + v c18 * pow2 (7 * 32) + v c19 * pow2 (8 * 32) + v c20 * pow2 (9 * 32) + v c21 * pow2 (10 * 32) + v c22 * pow2 (11 * 32)) % prime384 /\
	t8 = (v c20 * pow2 (1 * 32) + v c21 * pow2 (2 * 32) + v c22 * pow2 (3 * 32) + v c23 * pow2 (4 * 32)) % prime384 /\
	t9 = (v c23 * pow2 (3 * 32) + v c23 * pow2 (4 * 32)) % prime384
      )
  )


let solinas_reduction_upload c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 tempBuffer =
  let t0 = sub tempBuffer (size 0) (size 6) in
  let t1 = sub tempBuffer (size 6) (size 6) in
  let t2 = sub tempBuffer (size 12) (size 6) in
  let t3 = sub tempBuffer (size 18) (size 6) in
  let t4 = sub tempBuffer (size 24) (size 6) in
  let t5 = sub tempBuffer (size 30) (size 6) in
  let t6 = sub tempBuffer (size 36) (size 6) in
  let t7 = sub tempBuffer (size 42) (size 6) in
  let t8 = sub tempBuffer (size 48) (size 6) in
  let t9 = sub tempBuffer (size 54) (size 6) in

  upl_zer_buffer c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 t0;
  upl_fir_buffer c21 c22 c23 t1;
  upl_sec_buffer c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 t2;
  upl_thi_buffer c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 t3;
  upl_forth_buffer c12 c13 c14 c15 c16 c17 c18 c19 c20 c23 t4;
  upl_fif_buffer c20 c21 c22 c23 t5;
  upl_six_buffer c20 c21 c22 c23 t6;
  upl_sev_buffer c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 t7;
  upl_eit_buffer c20 c21 c22 c23 t8;
  upl_nin_buffer c23 t9


val solinas_reduction_operations: tempBuffer: lbuffer uint64 (size 60) -> o: lbuffer uint64 (size 6) ->
  Stack unit
    (requires fun h -> live h o /\ live h tempBuffer /\ disjoint tempBuffer o /\
      (
          let t0 = as_nat P384 h (gsub tempBuffer (size 0) (size 6)) in
          let t1 = as_nat P384 h (gsub tempBuffer (size 6) (size 6)) in
          let t2 = as_nat P384 h (gsub tempBuffer (size 12) (size 6)) in
          let t3 = as_nat P384 h (gsub tempBuffer (size 18) (size 6)) in
          let t4 = as_nat P384 h (gsub tempBuffer (size 24) (size 6)) in
          let t5 = as_nat P384 h (gsub tempBuffer (size 30) (size 6)) in
          let t6 = as_nat P384 h (gsub tempBuffer (size 36) (size 6)) in
          let t7 = as_nat P384 h (gsub tempBuffer (size 42) (size 6)) in
          let t8 = as_nat P384 h (gsub tempBuffer (size 48) (size 6)) in
	  let t9 = as_nat P384 h (gsub tempBuffer (size 54) (size 6)) in
          t0 < prime384 /\ t1 < prime384 /\ t2 < prime384 /\ t3 < prime384 /\ t4 < prime384 /\
          t5 < prime384 /\ t6 < prime384 /\ t7 < prime384 /\ t8 < prime384 /\ t9 < prime384
      )
    )
    (ensures fun h0 _ h1 -> modifies (loc tempBuffer |+| loc o) h0 h1 /\
      (
	let t0 = as_nat P384 h0 (gsub tempBuffer (size 0) (size 6)) in
        let t1 = as_nat P384 h0 (gsub tempBuffer (size 6) (size 6)) in
        let t2 = as_nat P384 h0 (gsub tempBuffer (size 12) (size 6)) in
        let t3 = as_nat P384 h0 (gsub tempBuffer (size 18) (size 6)) in
        let t4 = as_nat P384 h0 (gsub tempBuffer (size 24) (size 6)) in
        let t5 = as_nat P384 h0 (gsub tempBuffer (size 30) (size 6)) in
        let t6 = as_nat P384 h0 (gsub tempBuffer (size 36) (size 6)) in
        let t7 = as_nat P384 h0 (gsub tempBuffer (size 42) (size 6)) in
        let t8 = as_nat P384 h0 (gsub tempBuffer (size 48) (size 6)) in
	let t9 = as_nat P384 h0 (gsub tempBuffer (size 54) (size 6)) in
	as_nat P384 h1 o = (t0 + 2 * t1 + t2 + t3 + t4 + t5 + t6 - t7 - t8 - t9) % prime384
      )
    )


let solinas_reduction_operations tempBuffer o =
  let t0 = sub tempBuffer (size 0) (size 6) in
  let t1 = sub tempBuffer (size 6) (size 6) in
  let t2 = sub tempBuffer (size 12) (size 6) in
  let t3 = sub tempBuffer (size 18) (size 6) in
  let t4 = sub tempBuffer (size 24) (size 6) in
  let t5 = sub tempBuffer (size 30) (size 6) in
  let t6 = sub tempBuffer (size 36) (size 6) in
  let t7 = sub tempBuffer (size 42) (size 6) in
  let t8 = sub tempBuffer (size 48) (size 6) in
  let t9 = sub tempBuffer (size 54) (size 6) in

  let h0 = ST.get() in

  felem_double #P384 t1 t1;
  felem_add #P384 t0 t1 t1;
  felem_add #P384 t1 t2 t2;
  felem_add #P384 t2 t3 t3;
  felem_add #P384 t3 t4 t4;
  felem_add #P384 t4 t5 t5;
  felem_add #P384 t5 t6 t6;
  felem_sub #P384 t6 t7 t7;
  felem_sub #P384 t7 t8 t8;
  felem_sub #P384 t8 t9 o;

  let h1 = ST.get() in
  assert(as_nat P384 h1 o = ((((((((((as_nat P384 h1 t0 + (as_nat P384 h0 t1 + as_nat P384 h0 t1) % prime384) % prime384 + as_nat P384 h0 t2) % prime384) + as_nat P384 h0 t3) % prime384 + as_nat P384 h0 t4) % prime384 + as_nat P384 h0 t5) % prime384 + as_nat P384 h0 t6) % prime384 - as_nat P384 h0 t7) % prime384 - as_nat P384 h0 t8) % prime384 - as_nat P384 h0 t9) % prime384);

  calc (==) {
  as_nat P384 h1 o;
  (==) {}
  ((((((((((as_nat P384 h1 t0 + (as_nat P384 h0 t1 + as_nat P384 h0 t1) % prime384) % prime384 + as_nat P384 h0 t2) % prime384) + as_nat P384 h0 t3) % prime384 + as_nat P384 h0 t4) % prime384 + as_nat P384 h0 t5) % prime384 + as_nat P384 h0 t6) % prime384 - as_nat P384 h0 t7) % prime384 - as_nat P384 h0 t8) % prime384 - as_nat P384 h0 t9) % prime384;
  (==)
  {lemma_mod_add_distr (as_nat P384 h1 t0) (as_nat P384 h0 t1 + as_nat P384 h0 t1) prime384}
  ((((((((((as_nat P384 h1 t0 + as_nat P384 h0 t1 + as_nat P384 h0 t1) % prime384 + as_nat P384 h0 t2) % prime384) + as_nat P384 h0 t3) % prime384 + as_nat P384 h0 t4) % prime384 + as_nat P384 h0 t5) % prime384 + as_nat P384 h0 t6) % prime384 - as_nat P384 h0 t7) % prime384 - as_nat P384 h0 t8) % prime384 - as_nat P384 h0 t9) % prime384;
  (==)
  {lemma_mod_add_distr (as_nat P384 h0 t2) (as_nat P384 h1 t0 + as_nat P384 h0 t1 + as_nat P384 h0 t1) prime384}
  (((((((((as_nat P384 h1 t0 + as_nat P384 h0 t1 + as_nat P384 h0 t1 + as_nat P384 h0 t2) % prime384) + as_nat P384 h0 t3) % prime384 + as_nat P384 h0 t4) % prime384 + as_nat P384 h0 t5) % prime384 + as_nat P384 h0 t6) % prime384 - as_nat P384 h0 t7) % prime384 - as_nat P384 h0 t8) % prime384 - as_nat P384 h0 t9) % prime384;
  (==)
  {lemma_mod_add_distr (as_nat P384 h0 t3) (as_nat P384 h1 t0 + as_nat P384 h0 t1 + as_nat P384 h0 t1 + as_nat P384 h0 t2) prime384}
  (((((((as_nat P384 h1 t0 + as_nat P384 h0 t1 + as_nat P384 h0 t1 + as_nat P384 h0 t2 + as_nat P384 h0 t3) % prime384 + as_nat P384 h0 t4) % prime384 + as_nat P384 h0 t5) % prime384 + as_nat P384 h0 t6) % prime384 - as_nat P384 h0 t7) % prime384 - as_nat P384 h0 t8) % prime384 - as_nat P384 h0 t9) % prime384;
  (==)
  {lemma_mod_add_distr (as_nat P384 h0 t4) (as_nat P384 h1 t0 + as_nat P384 h0 t1 + as_nat P384 h0 t1 + as_nat P384 h0 t2 + as_nat P384 h0 t3) prime384}
  ((((((as_nat P384 h1 t0 + as_nat P384 h0 t1 + as_nat P384 h0 t1 + as_nat P384 h0 t2 + as_nat P384 h0 t3 + as_nat P384 h0 t4) % prime384 + as_nat P384 h0 t5) % prime384 + as_nat P384 h0 t6) % prime384 - as_nat P384 h0 t7) % prime384 - as_nat P384 h0 t8) % prime384 - as_nat P384 h0 t9) % prime384;
  (==)
  {lemma_mod_add_distr (as_nat P384 h0 t5) (as_nat P384 h1 t0 + as_nat P384 h0 t1 + as_nat P384 h0 t1 + as_nat P384 h0 t2 + as_nat P384 h0 t3 + as_nat P384 h0 t4) prime384}
  (((((as_nat P384 h1 t0 + as_nat P384 h0 t1 + as_nat P384 h0 t1 + as_nat P384 h0 t2 + as_nat P384 h0 t3 + as_nat P384 h0 t4 + as_nat P384 h0 t5) % prime384 + as_nat P384 h0 t6) % prime384 - as_nat P384 h0 t7) % prime384 - as_nat P384 h0 t8) % prime384 - as_nat P384 h0 t9) % prime384;
  (==)
  {lemma_mod_add_distr (as_nat P384 h0 t6) (as_nat P384 h1 t0 + as_nat P384 h0 t1 + as_nat P384 h0 t1 + as_nat P384 h0 t2 + as_nat P384 h0 t3 + as_nat P384 h0 t4 + as_nat P384 h0 t5) prime384}
  ((((as_nat P384 h1 t0 + as_nat P384 h0 t1 + as_nat P384 h0 t1 + as_nat P384 h0 t2 + as_nat P384 h0 t3 + as_nat P384 h0 t4 + as_nat P384 h0 t5 + as_nat P384 h0 t6) % prime384 - as_nat P384 h0 t7) % prime384 - as_nat P384 h0 t8) % prime384 - as_nat P384 h0 t9) % prime384;
  (==)
  {lemma_mod_add_distr (-as_nat P384 h0 t7) (as_nat P384 h1 t0 + as_nat P384 h0 t1 + as_nat P384 h0 t1 + as_nat P384 h0 t2 + as_nat P384 h0 t3 + as_nat P384 h0 t4 + as_nat P384 h0 t5 + as_nat P384 h0 t6) prime384}
  (((as_nat P384 h1 t0 + as_nat P384 h0 t1 + as_nat P384 h0 t1 + as_nat P384 h0 t2 + as_nat P384 h0 t3 + as_nat P384 h0 t4 + as_nat P384 h0 t5 + as_nat P384 h0 t6 - as_nat P384 h0 t7) % prime384 - as_nat P384 h0 t8) % prime384 - as_nat P384 h0 t9) % prime384;
  (==)
  {lemma_mod_add_distr (- as_nat P384 h0 t8) (as_nat P384 h1 t0 + as_nat P384 h0 t1 + as_nat P384 h0 t1 + as_nat P384 h0 t2 + as_nat P384 h0 t3 + as_nat P384 h0 t4 + as_nat P384 h0 t5 + as_nat P384 h0 t6 - as_nat P384 h0 t7) prime384}
  ((as_nat P384 h1 t0 + as_nat P384 h0 t1 + as_nat P384 h0 t1 + as_nat P384 h0 t2 + as_nat P384 h0 t3 + as_nat P384 h0 t4 + as_nat P384 h0 t5 + as_nat P384 h0 t6 - as_nat P384 h0 t7 - as_nat P384 h0 t8) % prime384 - as_nat P384 h0 t9) % prime384;
  (==)
  {lemma_mod_add_distr (- as_nat P384 h0 t9) (as_nat P384 h1 t0 + as_nat P384 h0 t1 + as_nat P384 h0 t1 + as_nat P384 h0 t2 + as_nat P384 h0 t3 + as_nat P384 h0 t4 + as_nat P384 h0 t5 + as_nat P384 h0 t6 - as_nat P384 h0 t7 - as_nat P384 h0 t8) prime384}
  (as_nat P384 h1 t0 + 2 * as_nat P384 h0 t1 + as_nat P384 h0 t2 + as_nat P384 h0 t3 + as_nat P384 h0 t4 + as_nat P384 h0 t5 + as_nat P384 h0 t6 - as_nat P384 h0 t7 - as_nat P384 h0 t8 - as_nat P384 h0 t9) % prime384;}


let _uint32 = n:nat{n < pow2 32}

val solinas_reduction_mod:
  c0_n: _uint32->
  c1_n: _uint32 ->
  c2_n: _uint32 ->
  c3_n: _uint32 ->
  c4_n: _uint32 ->
  c5_n: _uint32 ->
  c6_n: _uint32 ->
  c7_n: _uint32 ->
  c8_n: _uint32 ->
  c9_n: _uint32 ->
  c10_n: _uint32 ->
  c11_n: _uint32 ->
  c12_n: _uint32 ->
  c13_n: _uint32 ->
  c14_n: _uint32 ->
  c15_n: _uint32 ->
  c16_n: _uint32 ->
  c17_n: _uint32 ->
  c18_n: _uint32 ->
  c19_n: _uint32 ->
  c20_n: _uint32 ->
  c21_n: _uint32 ->
  c22_n: _uint32 ->
  c23_n: _uint32 ->
  s0: nat {s0 = (c0_n + c1_n * pow2 (1 * 32) + c2_n * pow2 (2 * 32) + c3_n * pow2 (3 * 32) + c4_n * pow2 (4 * 32) + c5_n * pow2 (5 * 32) + c6_n * pow2 (6 * 32) + c7_n * pow2 (7 * 32) + c8_n * pow2 (8 * 32) + c9_n * pow2 (9 * 32) + c10_n * pow2 (10 * 32) + c11_n * pow2 (11 * 32)) % prime384} ->
  s1: nat {s1 = (c21_n * pow2 (4 * 32) + c22_n * pow2 (5 * 32) + c23_n * pow2 (6 * 32)) % prime384} ->
  s2: nat {s2 = (c12_n + c13_n * pow2 (1 * 32) + c14_n * pow2 (2 * 32) + c15_n * pow2 (3 * 32) + c16_n * pow2 (4 * 32) + c17_n * pow2 (5 * 32) + c18_n * pow2 (6 * 32) + c19_n * pow2 (7 * 32) + c20_n * pow2 (8 * 32) + c21_n * pow2 (9 * 32) + c22_n * pow2 (10 * 32) + c23_n * pow2 (11 * 32)) % prime384} ->
  s3: nat {s3 = (c21_n + c22_n * pow2 (1 * 32) + c23_n * pow2 (2 * 32) + c12_n * pow2 (3 * 32) + c13_n * pow2 (4 * 32) + c14_n * pow2 (5 * 32) + c15_n * pow2 (6 * 32) + c16_n * pow2 (7 * 32) + c17_n * pow2 (8 * 32) + c18_n * pow2 (9 * 32) + c19_n * pow2 (10 * 32) + c20_n * pow2 (11 * 32)) % prime384} ->
  s4: nat {s4 = (c23_n * pow2 (1 * 32) + c20_n * pow2 (3 * 32) + c12_n * pow2 (4 * 32) + c13_n * pow2 (5 * 32) + c14_n * pow2 (6 * 32) + c15_n * pow2 (7 * 32) + c16_n * pow2 (8 * 32) + c17_n * pow2 (9 * 32) + c18_n * pow2 (10 * 32) + c19_n * pow2 (11 * 32)) % prime384} ->
  s5: nat {s5 = (c20_n * pow2 (4 * 32) + c21_n * pow2 (5 * 32) + c22_n * pow2 (6 * 32) + c23_n * pow2 (7 * 32)) % prime384} ->
  s6: nat {s6 = (c20_n + c21_n * pow2 (3 * 32) + c22_n * pow2 (4 * 32) + c23_n * pow2 (5 * 32)) % prime384} ->
  s7: nat {s7 = (c23_n + c12_n * pow2 (1 * 32) + c13_n * pow2 (2 * 32) + c14_n * pow2 (3 * 32) + c15_n * pow2 (4 * 32) + c16_n * pow2 (5 * 32) + c17_n * pow2 (6 * 32) + c18_n * pow2 (7 * 32) + c19_n * pow2 (8 * 32) + c20_n * pow2 (9 * 32) + c21_n * pow2 (10 * 32) + c22_n * pow2 (11 * 32)) % prime384} ->
  s8: nat {s8 = (c20_n * pow2 (1 * 32) + c21_n * pow2 (2 * 32) + c22_n * pow2 (3 * 32) + c23_n * pow2 (4 * 32)) % prime384} ->
  s9: nat {s9 = (c23_n * pow2 (3 * 32) + c23_n * pow2 (4 * 32)) % prime384} ->
  n: int {n = (s0 + 2 * s1 + s2 + s3 + s4 + s5 + s6 - s7 - s8 - s9) % prime384} ->
  Lemma (n % prime384 == (c0_n + c1_n * pow2 32 + c2_n * pow2 (2 * 32) + c3_n * pow2 (3 * 32) + c4_n * pow2 (4 * 32) + c5_n * pow2 (5 * 32) + c6_n * pow2 (6 * 32) + c7_n * pow2 (7 * 32) + c8_n * pow2 256 + c9_n * pow2 (9 * 32) + c10_n * pow2 (10 * 32)  + c11_n * pow2 (11 * 32) + c12_n * pow2 (12 * 32) + c13_n* pow2 (13 * 32) + c14_n * pow2 (14 * 32) + c15_n * pow2 (15 * 32) + c16_n * pow2 (16 * 32) + c17_n * pow2 (17 * 32) + c18_n * pow2 (18 * 32) + c19_n * pow2 (19 * 32) + c20_n * pow2 (20 * 32) + c21_n * pow2 (21 * 32) + c22_n * pow2 (22 * 32) + c23_n * pow2 (23 * 32)) % prime384)


val sr_mod_0: f0: int -> f1: int -> f2: int -> f3: int -> f4: int -> f5: int -> f6: int
  -> f7: int -> f8: int -> f9: int ->
  Lemma (
    let p = prime384 in
    ((f0 % p) + 2 * (f1 % p) + (f2 % p) + (f3 % p) + (f4 % p) + (f5 % p) + (f6 % p) - (f7 % p) - f8 % p - f9 % p) % p ==
    (f0 + 2 * f1 + f2 + f3 + f4 + f5 + f6 - f7 - f8 - f9) % p)

let sr_mod_0 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 =
  let p = prime384 in
  calc (==) {
   ((f0 % p) + 2 * (f1 % p) + (f2 % p) + (f3 % p) + (f4 % p) + (f5 % p) + (f6 % p) - (f7 % p) - f8 % p - f9 % p) % p;

   (==) {lemma_mod_add_distr (2 * (f1 % p) + (f2 % p) + (f3 % p) + (f4 % p) + (f5 % p) + (f6 % p) - (f7 % p) - f8 % p - f9 % p) f0 p}

  (2 * (f1 % p) + f0 + (f2 % p) + (f3 % p) + (f4 % p) + (f5 % p) + (f6 % p) - (f7 % p) - f8 % p - f9 % p) % p;

  (==) {lemma_mod_add_distr (f0 + (f2 % p) + (f3 % p) + (f4 % p) + (f5 % p) + (f6 % p) - (f7 % p) - f8 % p - f9 % p) (2 * (f1 % p)) p}

  (2 * (f1 % p) % p + f0 + (f2 % p) + (f3 % p) + (f4 % p) + (f5 % p) + (f6 % p) - (f7 % p) - f8 % p - f9 % p) % p;

  (==) {lemma_mod_mul_distr_r 2 f1 p}

  (2 * f1 % p + f0 + (f2 % p) + (f3 % p) + (f4 % p) + (f5 % p) + (f6 % p) - (f7 % p) - f8 % p - f9 % p) % p;

  (==) {lemma_mod_add_distr (f0 + (f2 % p) + (f3 % p) + (f4 % p) + (f5 % p) + (f6 % p) - (f7 % p) - f8 % p - f9 % p) (2 * f1) p}

  (2 * f1 + f0 + (f2 % p) + (f3 % p) + (f4 % p) + (f5 % p) + (f6 % p) - (f7 % p) - f8 % p - f9 % p) % p;

  (==) {lemma_mod_add_distr (2 * f1 + f0 + (f3 % p) + (f4 % p) + (f5 % p) + (f6 % p) - (f7 % p) - f8 % p - f9 % p) f2 p}

  (2 * f1 + f0 + f2 + (f3 % p) + (f4 % p) + (f5 % p) + (f6 % p) - (f7 % p) - f8 % p - f9 % p) % p;

  (==) {lemma_mod_add_distr (2 * f1 + f0 + f2 + (f4 % p) + (f5 % p) + (f6 % p) - (f7 % p) - f8 % p - f9 % p) f3 p}

   (2 * f1 + f0 + f2 + f3 + (f4 % p) + (f5 % p) + (f6 % p) - (f7 % p) - f8 % p - f9 % p) % p;

  (==) {lemma_mod_add_distr (2 * f1 + f0 + f2 + f3 + (f5 % p) + (f6 % p) - (f7 % p) - f8 % p - f9 % p) f4 p}

   (2 * f1 + f0 + f2 + f3 + f4 + (f5 % p) + (f6 % p) - (f7 % p) - f8 % p - f9 % p) % p;

  (==) {lemma_mod_add_distr (2 * f1 + f0 + f2 + f3 + f4 + (f6 % p) - (f7 % p) - f8 % p - f9 % p) f5 p}

  (2 * f1 + f0 + f2 + f3 + f4 + f5 + (f6 % p) - (f7 % p) - f8 % p - f9 % p) % p;

 (==) {lemma_mod_add_distr (2 * f1 + f0 + f2 + f3 + f4 + f5 - (f7 % p) - f8 % p - f9 % p) f6 p}

  (2 * f1 + f0 + f2 + f3 + f4 + f5 + f6 - (f7 % p) - f8 % p - f9 % p) % p;

  (==) {lemma_mod_sub_distr (2 * f1 + f0 + f2 + f3 + f4 + f5 + f6 - (f7 % p) - f8 % p) f9 p}

  (2 * f1 + f0 + f2 + f3 + f4 + f5 + f6 - f9 - (f7 % p) - f8 % p) % p;

  (==) {lemma_mod_sub_distr (2 * f1 + f0 + f2 + f3 + f4 + f5 + f6 - f9 - (f7 % p)) f8 p}

  (2 * f1 + f0 + f2 + f3 + f4 + f5 + f6 - f9 - f8 - (f7 % p)) % p;

  (==) {lemma_mod_sub_distr (2 * f1 + f0 + f2 + f3 + f4 + f5 + f6 - f9 - f8) f7 p}

  (2 * f1 + f0 + f2 + f3 + f4 + f5 + f6 - f9 - f8 - f7) % p;

  }


open FStar.Tactics
open FStar.Tactics.Canon

val c12_reduction: c12: _uint32 -> Lemma (
  c12 * pow2 384 % prime384 ==
  (c12 + c12 * pow2 (3 * 32) + c12 * pow2 (4 * 32) - c12 * pow2 (1 * 32)) % prime384)

let c12_reduction c12 =
  calc (==) {
    c12 * pow2 384 % prime384;
    == { lemma_mod_mul_distr_r c12 (pow2 384) prime384 }
    c12 * ( pow2 384 % prime384) % prime384;
    == {assert_norm (pow2 384 % prime384 = (1 + pow2 (3 * 32) + pow2 (4 * 32) - pow2 (1 * 32)) % prime384)}
    c12 * ((1 + pow2 (3 * 32) + pow2 (4 * 32) - pow2 (1 * 32)) % prime384) % prime384;
    == { lemma_mod_mul_distr_r c12 (1 + pow2 (3 * 32) + pow2 (4 * 32) - pow2 (1 * 32)) prime384}
    c12 * ((1 + pow2 (3 * 32) + pow2 (4 * 32) - pow2 (1 * 32))) % prime384;
    == { _ by (canon())}
    (c12 + c12 * pow2 (3 * 32) + c12 * pow2 (4 * 32) - c12 * pow2 (1 * 32)) % prime384;
  }


val c13_reduction: c13: _uint32 -> Lemma (
  c13 * pow2 (13 * 32) % prime384 ==
  (c13 * pow2 (1 * 32) + c13 * pow2 (4 * 32) + c13 * pow2 (5 * 32) - c13 * pow2 (2 * 32)) % prime384)


let c13_reduction c13 =
  calc (==) {
    c13 * pow2 (13 * 32) % prime384;
    == { lemma_mod_mul_distr_r c13 (pow2 (13 * 32)) prime384 }
    c13 * ( pow2 (13 * 32) % prime384) % prime384;
    == {assert_norm (pow2 (13 * 32) % prime384 = (pow2 (1 * 32) + pow2 (4 * 32) + pow2 (5 * 32) - pow2 (2 * 32)) % prime384)}
    c13 * ((pow2 (1 * 32) + pow2 (4 * 32) + pow2 (5 * 32) - pow2 (2 * 32)) % prime384) % prime384;
    == { lemma_mod_mul_distr_r c13 (pow2 (1 * 32) + pow2 (4 * 32) + pow2 (5 * 32) - pow2 (2 * 32)) prime384}
    c13 * ((pow2 (1 * 32) + pow2 (4 * 32) + pow2 (5 * 32) - pow2 (2 * 32))) % prime384;
    == { _ by (canon())}
    (c13 * pow2 (1 * 32) + c13 * pow2 (4 * 32) + c13 * pow2 (5 * 32) - c13 * pow2 (2 * 32)) % prime384;}


val c14_reduction: c14: _uint32 -> Lemma (
  c14 * pow2 (14 * 32) % prime384 ==
  (c14 * pow2 (2 * 32) + c14 * pow2 (5 * 32) + c14 * pow2 (6 * 32) - c14 * pow2 (3 * 32)) % prime384)

let c14_reduction c14 =
  calc (==) {
    c14 * pow2 (14 * 32) % prime384;
    == { lemma_mod_mul_distr_r c14 (pow2 (14 * 32)) prime384 }
    c14 * ( pow2 (14 * 32) % prime384) % prime384;
    == {assert_norm (pow2 (14 * 32) % prime384 = (pow2 (2 * 32) + pow2 (5 * 32) + pow2 (6 * 32) - pow2 (3 * 32)) % prime384)}
    c14 * ((pow2 (2 * 32) + pow2 (5 * 32) + pow2 (6 * 32) - pow2 (3 * 32)) % prime384) % prime384;
    == { lemma_mod_mul_distr_r c14 (pow2 (2 * 32) + pow2 (5 * 32) + pow2 (6 * 32) - pow2 (3 * 32))  prime384}
    c14 * (pow2 (2 * 32) + pow2 (5 * 32) + pow2 (6 * 32) - pow2 (3 * 32)) % prime384;
    == { _ by (canon())}
     (c14 * pow2 (2 * 32) + c14 * pow2 (5 * 32) + c14 * pow2 (6 * 32) - c14 * pow2 (3 * 32)) % prime384;}


val c15_reduction: c15: _uint32 -> Lemma (
  c15 * pow2 (15 * 32) % prime384 ==
  (c15 * pow2 (3 * 32)  + c15 * pow2 (6 * 32) + c15 * pow2 (7 * 32) - c15 * pow2 (4 * 32)) % prime384)

let c15_reduction c15 =
  calc (==) {
    c15 * pow2 (15 * 32) % prime384;
    == { lemma_mod_mul_distr_r c15 (pow2 (15 * 32)) prime384 }
    c15 * ( pow2 (15 * 32) % prime384) % prime384;
    == {assert_norm (pow2 (15 * 32) % prime384 = (pow2 (3 * 32) + pow2 (6 * 32) + pow2 (7 * 32) - pow2 (4 * 32)) % prime384)}
    c15 * ((pow2 (3 * 32) + pow2 (6 * 32) + pow2 (7 * 32) - pow2 (4 * 32)) % prime384) % prime384;
    == { lemma_mod_mul_distr_r c15 (pow2 (3 * 32) + pow2 (6 * 32) + pow2 (7 * 32) - pow2 (4 * 32))  prime384}
    c15 * (pow2 (3 * 32) + pow2 (6 * 32) + pow2 (7 * 32) - pow2 (4 * 32)) % prime384;
    == { _ by (canon())}
    (c15 * pow2 (3 * 32)  + c15 * pow2 (6 * 32) + c15 * pow2 (7 * 32) - c15 * pow2 (4 * 32)) % prime384;
     }


val c16_reduction: c16: _uint32 -> Lemma (
  c16 * pow2 (16 * 32) % prime384 ==
  (c16 * pow2 (4 * 32) + c16 * pow2 (7 * 32)  + c16 * pow2 (8 * 32) - c16 * pow2 (5 * 32)) % prime384)

let c16_reduction c16 =
  calc (==) {
    c16 * pow2 (16 * 32) % prime384;
    == { lemma_mod_mul_distr_r c16 (pow2 (16 * 32)) prime384 }
    c16 * ( pow2 (16 * 32) % prime384) % prime384;
    == {assert_norm (pow2 (16 * 32) % prime384 = (pow2 (4 * 32) + pow2 (7 * 32) + pow2 (8 * 32) - pow2 (5 * 32)) % prime384)}
    c16 * ((pow2 (4 * 32) + pow2 (7 * 32) + pow2 (8 * 32) - pow2 (5 * 32)) % prime384) % prime384;
    == { lemma_mod_mul_distr_r c16 (pow2 (4 * 32) + pow2 (7 * 32) + pow2 (8 * 32) - pow2 (5 * 32))  prime384}
    c16 * (pow2 (4 * 32) + pow2 (7 * 32) + pow2 (8 * 32) - pow2 (5 * 32)) % prime384;
    == { _ by (canon())}
      (c16 * pow2 (4 * 32) + c16 * pow2 (7 * 32)  + c16 * pow2 (8 * 32) - c16 * pow2 (5 * 32))  % prime384;}


val c17_reduction: c17: _uint32 -> Lemma (
  c17 * pow2 (17 * 32) % prime384 ==
  (c17 * pow2 (5 * 32) + c17 * pow2 (8 * 32)  - c17 * pow2 (6 * 32) + c17 * pow2 (9 * 32)) % prime384)

let c17_reduction c17 =
  calc (==) {
    c17 * pow2 (17 * 32) % prime384;
    == { lemma_mod_mul_distr_r c17 (pow2 (17 * 32)) prime384 }
    c17 * (pow2 (17 * 32) % prime384) % prime384;
    == {assert_norm (pow2 (17 * 32) % prime384 = (pow2 (5 * 32) + pow2 (8 * 32) - pow2 (6 * 32) + pow2 (9 * 32)) % prime384)}
    c17 * ((pow2 (5 * 32) + pow2 (8 * 32) - pow2 (6 * 32) + pow2 (9 * 32)) % prime384) % prime384;
    == { lemma_mod_mul_distr_r c17 (pow2 (5 * 32) + pow2 (8 * 32) - pow2 (6 * 32) + pow2 (9 * 32))  prime384}
    c17 * (pow2 (5 * 32) + pow2 (8 * 32) - pow2 (6 * 32) + pow2 (9 * 32)) % prime384;
    == { _ by (canon())}
    (c17 * pow2 (5 * 32) + c17 * pow2 (8 * 32)  - c17 * pow2 (6 * 32) + c17 * pow2 (9 * 32)) % prime384;
  }


val c18_reduction: c18: _uint32 -> Lemma (
  c18 * pow2 (18 * 32) % prime384 ==
  (c18 * pow2 (6 * 32) + c18 * pow2 (9 * 32) + c18 * pow2 (10 * 32) - c18 * pow2 (7 * 32)) % prime384)

let c18_reduction c18 =
  calc (==) {
    c18 * pow2 (18 * 32) % prime384;
    == { lemma_mod_mul_distr_r c18 (pow2 (18 * 32)) prime384 }
    c18 * (pow2 (18 * 32) % prime384) % prime384;
    == {assert_norm (pow2 (18 * 32) % prime384 = (pow2 (6 * 32) + pow2 (9 * 32) + pow2 (10 * 32) - pow2 (7 * 32)) % prime384)}
    c18 * ((pow2 (6 * 32) + pow2 (9 * 32) + pow2 (10 * 32) - pow2 (7 * 32)) % prime384) % prime384;
    == { lemma_mod_mul_distr_r c18 (pow2 (6 * 32) + pow2 (9 * 32) + pow2 (10 * 32) - pow2 (7 * 32)) prime384}
    c18 * (pow2 (6 * 32) + pow2 (9 * 32) + pow2 (10 * 32) - pow2 (7 * 32)) % prime384;
    == { _ by (canon())}
    (c18 * pow2 (6 * 32) + c18 * pow2 (9 * 32) + c18 * pow2 (10 * 32) - c18 * pow2 (7 * 32)) % prime384;
  }


val c19_reduction: c19: _uint32 -> Lemma (
  c19 * pow2 (19 * 32) % prime384 ==
  (c19 * pow2 (7 * 32)  + c19 * pow2 (10 * 32)  + c19 * pow2 (11 * 32) - c19 * pow2 (8 * 32)) % prime384)

let c19_reduction c19 =
  calc (==) {
    c19 * pow2 (19 * 32) % prime384;
    == { lemma_mod_mul_distr_r c19 (pow2 (19 * 32)) prime384 }
    c19 * (pow2 (19 * 32) % prime384) % prime384;
    == {assert_norm (pow2 (19 * 32) % prime384 = (pow2 (7 * 32) + pow2 (10 * 32)  + pow2 (11 * 32) - pow2 (8 * 32)) % prime384)}
    c19 * ((pow2 (7 * 32) + pow2 (10 * 32) + pow2 (11 * 32) - pow2 (8 * 32)) % prime384) % prime384;
    == { lemma_mod_mul_distr_r c19 (pow2 (7 * 32) + pow2 (10 * 32) + pow2 (11 * 32) - pow2 (8 * 32)) prime384}
    c19 * (pow2 (7 * 32) + pow2 (10 * 32)  + pow2 (11 * 32) - pow2 (8 * 32)) % prime384;
    == { _ by (canon())}
    (c19 * pow2 (7 * 32)  + c19 * pow2 (10 * 32)  + c19 * pow2 (11 * 32) - c19 * pow2 (8 * 32)) % prime384;
  }


val c20_reduction: c20: _uint32 -> Lemma (
  c20 * pow2 (20 * 32) % prime384 ==
  (c20 * pow2 (8 * 32) + c20 * pow2 (11 * 32) + c20 * pow2 (3 * 32) + c20 * pow2 (4 * 32) + c20 - c20 * pow2 (9 * 32) - c20 * pow2 (1 * 32)) % prime384)

let c20_reduction c20 =
  calc (==) {
    c20 * pow2 (20 * 32) % prime384;
    == { lemma_mod_mul_distr_r c20 (pow2 (20 * 32)) prime384 }
    c20 * (pow2 (20 * 32) % prime384) % prime384;
    == {assert_norm (pow2 (20 * 32) % prime384 = (pow2 (8 * 32) + pow2 (11 * 32) + pow2 (3 * 32) + pow2 (4 * 32) + 1 - pow2 (9 * 32) - pow2 (1 * 32)) % prime384)}
    c20 * ((pow2 (8 * 32) + pow2 (11 * 32) + pow2 (3 * 32) + pow2 (4 * 32) + 1 - pow2 (9 * 32) - pow2 (1 * 32)) % prime384) % prime384;
    == { lemma_mod_mul_distr_r c20 (pow2 (8 * 32) + pow2 (11 * 32) + pow2 (3 * 32) + pow2 (4 * 32) + 1 - pow2 (9 * 32) - pow2 (1 * 32)) prime384}
    c20 * (pow2 (8 * 32) + pow2 (11 * 32) + pow2 (3 * 32) + pow2 (4 * 32) + 1 - pow2 (9 * 32) - pow2 (1 * 32)) % prime384;
    == { _ by (canon())}
    (c20 * pow2 (8 * 32) + c20 * pow2 (11 * 32) + c20 * pow2 (3 * 32) + c20 * pow2 (4 * 32) + c20 - c20 * pow2 (9 * 32) - c20 * pow2 (1 * 32)) % prime384;
  }


val c21_reduction: c21: _uint32 -> Lemma (
  c21 * pow2 (21 * 32) % prime384 ==
  (2 * c21 * pow2 (4 * 32) + c21 * pow2 (9 * 32) + c21 + c21 * pow2 (5 * 32) + c21 * pow2 (3 * 32) - c21 * pow2 (10 * 32) - c21 * pow2 (2 * 32)) % prime384)

let c21_reduction c21 =
  calc (==) {
    c21 * pow2 (21 * 32) % prime384;
    == { lemma_mod_mul_distr_r c21 (pow2 (21 * 32)) prime384 }
    c21 * (pow2 (21 * 32) % prime384) % prime384;
    == {assert_norm (pow2 (21 * 32) % prime384 = (2 * pow2 (4 * 32) + pow2 (9 * 32) + 1 + pow2 (5 * 32) + pow2 (3 * 32) - pow2 (10 * 32) - pow2 (2 * 32)) % prime384)}
    c21 * ((2 * pow2 (4 * 32) + pow2 (9 * 32) + 1 + pow2 (5 * 32) + pow2 (3 * 32) - pow2 (10 * 32) - pow2 (2 * 32)) % prime384) % prime384;
    == { lemma_mod_mul_distr_r c21 (2 * pow2 (4 * 32) + pow2 (9 * 32) + 1 + pow2 (5 * 32) + pow2 (3 * 32) - pow2 (10 * 32) - pow2 (2 * 32)) prime384}
    c21 * (2 * pow2 (4 * 32) + pow2 (9 * 32) + 1 + pow2 (5 * 32) + pow2 (3 * 32) - pow2 (10 * 32) - pow2 (2 * 32)) % prime384;
    == { _ by (canon())}
    (2 * c21 * pow2 (4 * 32) + c21 * pow2 (9 * 32) + c21 + c21 * pow2 (5 * 32) + c21 * pow2 (3 * 32) - c21 * pow2 (10 * 32) - c21 * pow2 (2 * 32)) % prime384;
  }


val c22_reduction: c22: _uint32 -> Lemma (
  c22 * pow2 (22 * 32) % prime384 ==
  (2 * c22 * pow2 (5 * 32) + c22 * pow2 (10 * 32) + c22 * pow2 (1 * 32) +  c22 * pow2 (6 * 32) + c22 * pow2 (4 * 32) - c22 * pow2 (11 * 32) - c22 * pow2 (3 * 32)) % prime384)

let c22_reduction c22 =
  calc (==) {
    c22 * pow2 (22 * 32) % prime384;
    == { lemma_mod_mul_distr_r c22 (pow2 (22 * 32)) prime384 }
    c22 * (pow2 (22 * 32) % prime384) % prime384;
    == {assert_norm (pow2 (22 * 32) % prime384 = (2 * pow2 (5 * 32) + pow2 (10 * 32) + pow2 (1 * 32) + pow2 (6 * 32) + pow2 (4 * 32) - pow2 (11 * 32) - pow2 (3 * 32)) % prime384)}
    c22 * ((2 * pow2 (5 * 32) + pow2 (10 * 32) + pow2 (1 * 32) + pow2 (6 * 32) + pow2 (4 * 32) - pow2 (11 * 32) - pow2 (3 * 32)) % prime384) % prime384;
    == { lemma_mod_mul_distr_r c22 (2 * pow2 (5 * 32) + pow2 (10 * 32) + pow2 (1 * 32) + pow2 (6 * 32) + pow2 (4 * 32) - pow2 (11 * 32) - pow2 (3 * 32)) prime384}
    c22 * (2 * pow2 (5 * 32) + pow2 (10 * 32) + pow2 (1 * 32) + pow2 (6 * 32) + pow2 (4 * 32) - pow2 (11 * 32) - pow2 (3 * 32)) % prime384;
    == { _ by (canon())}
    (2 * c22 * pow2 (5 * 32) + c22 * pow2 (10 * 32) + c22 * pow2 (1 * 32) +  c22 * pow2 (6 * 32) + c22 * pow2 (4 * 32) - c22 * pow2 (11 * 32) - c22 * pow2 (3 * 32)) % prime384;}


val c23_reduction: c23: _uint32 -> Lemma (
  c23 * pow2 (23 * 32) % prime384 ==
  (2 * c23 * pow2 (6 * 32) + c23 * pow2 (11 * 32) + c23 * pow2 (2 * 32) + c23 * pow2 (1 * 32) + c23 * pow2 (7 * 32) +  c23 * pow2 (5 * 32) - c23 -  c23 * pow2 (4 * 32) - c23 * pow2 (3 * 32) - c23 * pow2 (4 * 32)) % prime384)

let c23_reduction c23 =
  calc (==) {
    c23 * pow2 (23 * 32) % prime384;
    == { lemma_mod_mul_distr_r c23 (pow2 (23 * 32)) prime384 }
    c23 * (pow2 (23 * 32) % prime384) % prime384;
    == {assert_norm (pow2 (23 * 32) % prime384 = (2 * pow2 (6 * 32) + pow2 (11 * 32) + pow2 (2 * 32) + pow2 (1 * 32) + pow2 (7 * 32) + pow2 (5 * 32) - 1 - pow2 (4 * 32) -pow2 (3 * 32) - pow2 (4 * 32)) % prime384)}
    c23 * ((2 * pow2 (6 * 32) + pow2 (11 * 32) + pow2 (2 * 32) + pow2 (1 * 32) + pow2 (7 * 32) + pow2 (5 * 32) - 1 - pow2 (4 * 32) -pow2 (3 * 32) - pow2 (4 * 32)) % prime384) % prime384;
    == { lemma_mod_mul_distr_r c23 (2 * pow2 (6 * 32) + pow2 (11 * 32) + pow2 (2 * 32) + pow2 (1 * 32) + pow2 (7 * 32) + pow2 (5 * 32) - 1 - pow2 (4 * 32) -pow2 (3 * 32) - pow2 (4 * 32)) prime384}
    c23 * (2 * pow2 (6 * 32) + pow2 (11 * 32) + pow2 (2 * 32) + pow2 (1 * 32) + pow2 (7 * 32) + pow2 (5 * 32) - 1 - pow2 (4 * 32) -pow2 (3 * 32) - pow2 (4 * 32)) % prime384;
    == { _ by (canon())}
    (2 * c23 * pow2 (6 * 32) + c23 * pow2 (11 * 32) + c23 * pow2 (2 * 32) + c23 * pow2 (1 * 32) + c23 * pow2 (7 * 32) +  c23 * pow2 (5 * 32) - c23 -  c23 * pow2 (4 * 32) - c23 * pow2 (3 * 32) - c23 * pow2 (4 * 32)) % prime384;}




val solinas_reduction_nat:
  c0: _uint32 ->
  c1: _uint32 ->
  c2: _uint32 ->
  c3: _uint32 ->
  c4: _uint32 ->
  c5: _uint32 ->
  c6: _uint32 ->
  c7: _uint32 ->
  c8: _uint32 ->
  c9: _uint32 ->
  c10: _uint32 ->
  c11: _uint32 ->
  c12: _uint32 ->
  c13: _uint32 ->
  c14: _uint32 ->
  c15: _uint32 ->
  c16: _uint32 ->
  c17: _uint32 ->
  c18: _uint32 ->
  c19: _uint32 ->
  c20: _uint32 ->
  c21: _uint32 ->
  c22: _uint32 ->
  c23: _uint32 ->
  f0: int {f0 = c0 + c1 * pow2 (1 * 32) + c2 * pow2 (2 * 32) + c3 * pow2 (3 * 32) + c4 * pow2 (4 * 32) + c5 * pow2 (5 * 32) + c6 * pow2 (6 * 32) + c7 * pow2 (7 * 32) + c8 * pow2 (8 * 32) + c9 * pow2 (9 * 32) + c10 * pow2 (10 * 32) + c11 * pow2 (11 * 32)} ->
  f1: int {f1 = c21 * pow2 (4 * 32) + c22 * pow2 (5 * 32) + c23 * pow2 (6 * 32)} ->

  f2: int {f2 = c12 + c13 * pow2 (1 * 32) + c14 * pow2 (2 * 32) + c15 * pow2 (3 * 32) + c16 * pow2 (4 * 32) + c17 * pow2 (5 * 32) + c18 * pow2 (6 * 32) + c19 * pow2 (7 * 32) + c20 * pow2 (8 * 32) + c21 * pow2 (9 * 32) + c22 * pow2 (10 * 32) + c23 * pow2 (11 * 32)} ->

  f3: int {f3 = c21 + c22 * pow2 (1 * 32) + c23 * pow2 (2 * 32) + c12 * pow2 (3 * 32) + c13 * pow2 (4 * 32) + c14 * pow2 (5 * 32) + c15 * pow2 (6 * 32) + c16 * pow2 (7 * 32) + c17 * pow2 (8 * 32) + c18 * pow2 (9 * 32) + c19 * pow2 (10 * 32) + c20 * pow2 (11 * 32)} ->

  f4: int {f4 = c23 * pow2 (1 * 32) + c20 * pow2 (3 * 32) + c12 * pow2 (4 * 32) + c13 * pow2 (5 * 32) + c14 * pow2 (6 * 32) + c15 * pow2 (7 * 32) + c16 * pow2 (8 * 32) + c17 * pow2 (9 * 32) + c18 * pow2 (10 * 32) + c19 * pow2 (11 * 32)} ->

  f5: int {f5 = c20 * pow2 (4 * 32) + c21 * pow2 (5 * 32) + c22 * pow2 (6 * 32) + c23 * pow2 (7 * 32)} ->

  f6: int {f6 = c20 + c21 * pow2 (3 * 32) + c22 * pow2 (4 * 32) + c23 * pow2 (5 * 32)} ->

  f7: int {f7 = c23 + c12 * pow2 (1 * 32) + c13 * pow2 (2 * 32) + c14 * pow2 (3 * 32) + c15 * pow2 (4 * 32) + c16 * pow2 (5 * 32) + c17 * pow2 (6 * 32) + c18 * pow2 (7 * 32) + c19 * pow2 (8 * 32) + c20 * pow2 (9 * 32) + c21 * pow2 (10 * 32) + c22 * pow2 (11 * 32)} ->

  f8: int {f8 = c20 * pow2 (1 * 32) + c21 * pow2 (2 * 32) + c22 * pow2 (3 * 32) + c23 * pow2 (4 * 32)} ->
  f9: int {f9 = c23 * pow2 (3 * 32) + c23 * pow2 (4 * 32)} ->
  n: int {n = f0 + 2 * f1 + f2 + f3 + f4 + f5 + f6 - f7 - f8 - f9} ->
  Lemma (n % prime384 ==  (c0 + c1 * pow2 32 + c2 * pow2 (2 * 32) + c3 * pow2 (3 * 32) + c4 * pow2 (4 * 32) + c5 * pow2 (5 * 32) + c6 * pow2 (6 * 32) + c7 * pow2 (7 * 32) + c8 * pow2 256 + c9 * pow2 (9 * 32) + c10 * pow2 (10 * 32)  + c11 * pow2 (11 * 32) + c12 * pow2 (12 * 32) + c13 * pow2 (13 * 32) + c14 * pow2 (14 * 32) + c15 * pow2 (15 * 32) + c16 * pow2 (16 * 32) + c17 * pow2 (17 * 32) + c18 * pow2 (18 * 32) + c19 * pow2 (19 * 32) + c20 * pow2 (20 * 32) + c21 * pow2 (21 * 32) + c22 * pow2 (22 * 32) + c23 * pow2 (23 * 32)) % prime384)


noextract
val inside_mod: a: int -> b: int -> c: int -> d: int -> e: int -> f: int -> g: int -> h: int -> i: int -> j: int -> k: int -> l: int -> m: int ->
  Lemma (
    let prime = prime384 in
    (a + b + c + d + e + f + g + h + i + j + k + l + m) % prime ==
    (a + (b % prime) + (c % prime) + (d % prime) + (e % prime) + (f % prime) + (g % prime) + (h % prime) + (i % prime) + (j % prime) + (k % prime) + (l % prime) + (m % prime)) % prime)

let inside_mod a b c d e f g h i j k l m =
  let prime = prime384 in
  calc (==)
  {
    (a + (b % prime) + (c % prime) + (d % prime) + (e % prime) + (f % prime) + (g % prime) + (h % prime) + (i % prime) + (j % prime) + (k % prime) + (l % prime) + (m % prime)) % prime;
    == {lemma_mod_add_distr (a + (b % prime) + (c % prime) + (d % prime) + (e % prime) + (f % prime) + (g % prime) + (h % prime) + (i % prime) + (j % prime) + (k % prime) + (l % prime)) m prime}

    (a + (b % prime) + (c % prime) + (d % prime) + (e % prime) + (f % prime) + (g % prime) + (h % prime) + (i % prime) + (j % prime) + (k % prime) + (l % prime) + m) % prime;

    == {lemma_mod_add_distr (a + (b % prime) + (c % prime) + (d % prime) + (e % prime) + (f % prime) + (g % prime) + (h % prime) + (i % prime) + (j % prime) + (k % prime) + m) l prime}

    (a + (b % prime) + (c % prime) + (d % prime) + (e % prime) + (f % prime) + (g % prime) + (h % prime) + (i % prime) + (j % prime) + (k % prime) + l + m) % prime;

    == {lemma_mod_add_distr (a + (b % prime) + (c % prime) + (d % prime) + (e % prime) + (f % prime) + (g % prime) + (h % prime) + (i % prime) + (j % prime) + l + m) k prime}

    (a + (b % prime) + (c % prime) + (d % prime) + (e % prime) + (f % prime) + (g % prime) + (h % prime) + (i % prime) + (j % prime) + k + l + m) % prime;

    == {lemma_mod_add_distr (a + (b % prime) + (c % prime) + (d % prime) + (e % prime) + (f % prime) + (g % prime) + (h % prime) + (i % prime) + k + l + m) j prime}

    (a + (b % prime) + (c % prime) + (d % prime) + (e % prime) + (f % prime) + (g % prime) + (h % prime) + (i % prime) + j + k + l + m) % prime;

    == {lemma_mod_add_distr (a + (b % prime) + (c % prime) + (d % prime) + (e % prime) + (f % prime) + (g % prime) + (h % prime) + j + k + l + m) i prime}

    (a + (b % prime) + (c % prime) + (d % prime) + (e % prime) + (f % prime) + (g % prime) + (h % prime) + i + j + k + l + m) % prime;

    == {lemma_mod_add_distr (a + (b % prime) + (c % prime) + (d % prime) + (e % prime) + (f % prime) + (g % prime) + i + j + k + l + m) h prime}

    (a + (b % prime) + (c % prime) + (d % prime) + (e % prime) + (f % prime) + (g % prime) + h + i + j + k + l + m) % prime;

    == {lemma_mod_add_distr (a + (b % prime) + (c % prime) + (d % prime) + (e % prime) + (f % prime) + h + i + j + k + l + m) g prime}

    (a + (b % prime) + (c % prime) + (d % prime) + (e % prime) + (f % prime) + g + h + i + j + k + l + m) % prime;

    == {lemma_mod_add_distr (a + (b % prime) + (c % prime) + (d % prime) + (e % prime) + g + h + i + j + k + l + m) f prime}

    (a + (b % prime) + (c % prime) + (d % prime) + (e % prime) + f + g + h + i + j + k + l + m) % prime;

    == {lemma_mod_add_distr (a + (b % prime) + (c % prime) + (d % prime) + f + g + h + i + j + k + l + m) e prime}

    (a + (b % prime) + (c % prime) + (d % prime) + e + f + g + h + i + j + k + l + m) % prime;

    == {lemma_mod_add_distr (a + (b % prime) + (c % prime) + e + f + g + h + i + j + k + l + m) d prime}

    (a + (b % prime) + (c % prime) + d + e + f + g + h + i + j + k + l + m) % prime;

    == {lemma_mod_add_distr (a + (b % prime) + d + e + f + g + h + i + j + k + l + m) c prime}

    (a + (b % prime) + c + d + e + f + g + h + i + j + k + l + m) % prime;

    == {lemma_mod_add_distr (a + c + d + e + f + g + h + i + j + k + l + m) b prime}

    (a + b + c + d + e + f + g + h + i + j + k + l + m) % prime;

  }


let solinas_reduction_nat c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 n =
  assert_by_tactic (2 * (c21 * pow2 (4 * 32) + c22 * pow2 (5 * 32) + c23 * pow2 (6 * 32)) ==
    2 * c21 * pow2 (4 * 32) + 2 * c22 * pow2 (5 * 32) + 2*  c23 * pow2 (6 * 32)) canon;

  let a_ = c0 + c1 * pow2 32 + c2 * pow2 (2 * 32) + c3 * pow2 (3 * 32) + c4 * pow2 (4 * 32) + c5 * pow2 (5 * 32) + c6 * pow2 (6 * 32) + c7 * pow2 (7 * 32) + c8 * pow2 (8 * 32) + c9 * pow2 (9 * 32) + c10 * pow2 (10 * 32) + c11 * pow2 (11 * 32) in

  let c12_ = c12 + c12 * pow2 (3 * 32) + c12 * pow2 (4 * 32) - c12 * pow2 (1 * 32) in
  let c13_ = c13 * pow2 (1 * 32) + c13 * pow2 (4 * 32) + c13 * pow2 (5 * 32) - c13 * pow2 (2 * 32) in
  let c14_ = c14 * pow2 (2 * 32) + c14 * pow2 (5 * 32) + c14 * pow2 (6 * 32) - c14 * pow2 (3 * 32) in
  let c15_ = c15 * pow2 (3 * 32)  + c15 * pow2 (6 * 32) + c15 * pow2 (7 * 32) - c15 * pow2 (4 * 32) in
  let c16_ = c16 * pow2 (4 * 32) + c16 * pow2 (7 * 32)  + c16 * pow2 (8 * 32) - c16 * pow2 (5 * 32) in
  let c17_ = c17 * pow2 (5 * 32) + c17 * pow2 (8 * 32)  - c17 * pow2 (6 * 32) + c17 * pow2 (9 * 32) in
  let c18_ = c18 * pow2 (6 * 32) + c18 * pow2 (9 * 32) + c18 * pow2 (10 * 32) - c18 * pow2 (7 * 32) in
  let c19_ = c19 * pow2 (7 * 32)  + c19 * pow2 (10 * 32)  + c19 * pow2 (11 * 32) - c19 * pow2 (8 * 32) in
  let c20_ = c20 * pow2 (8 * 32) + c20 * pow2 (11 * 32) + c20 * pow2 (3 * 32) + c20 * pow2 (4 * 32) + c20 - c20 * pow2 (9 * 32) - c20 * pow2 (1 * 32) in
  let c21_ = 2 * c21 * pow2 (4 * 32) + c21 * pow2 (9 * 32) + c21 + c21 * pow2 (5 * 32) + c21 * pow2 (3 * 32) - c21 * pow2 (10 * 32) - c21 * pow2 (2 * 32) in
  let c22_ = 2 * c22 * pow2 (5 * 32) + c22 * pow2 (10 * 32) + c22 * pow2 (1 * 32) +  c22 * pow2 (6 * 32) + c22 * pow2 (4 * 32) - c22 * pow2 (11 * 32) - c22 * pow2 (3 * 32) in
  let c23_ = 2 * c23 * pow2 (6 * 32) + c23 * pow2 (11 * 32) + c23 * pow2 (2 * 32) + c23 * pow2 (1 * 32) + c23 * pow2 (7 * 32) +  c23 * pow2 (5 * 32) - c23 -  c23 * pow2 (4 * 32) - c23 * pow2 (3 * 32) - c23 * pow2 (4 * 32) in

  inside_mod a_ c12_ c13_ c14_ c15_ c16_ c17_ c18_ c19_ c20_ c21_ c22_ c23_;

   c12_reduction c12;
   c13_reduction c13;
   c14_reduction c14;
   c15_reduction c15;
   c16_reduction c16;
   c17_reduction c17;
   c18_reduction c18;
   c19_reduction c19;
   c20_reduction c20;
   c21_reduction c21;
   c22_reduction c22;
   c23_reduction c23;

   inside_mod a_ (c12 * pow2 (12 * 32)) (c13 * pow2 (13 * 32)) (c14 * pow2 (14 * 32)) (c15 * pow2 (15 * 32)) (c16 * pow2 (16 * 32)) (c17 * pow2 (17 * 32)) (c18 * pow2 (18 * 32)) (c19 * pow2 (19 * 32)) (c20 * pow2 (20 * 32)) (c21 * pow2 (21 * 32)) (c22 * pow2 (22 * 32)) (c23 * pow2 (23 * 32))


let solinas_reduction_mod c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 n =

  let f0 = c0 + c1 * pow2 (1 * 32) + c2 * pow2 (2 * 32) + c3 * pow2 (3 * 32) + c4 * pow2 (4 * 32) + c5 * pow2 (5 * 32) + c6 * pow2 (6 * 32) + c7 * pow2 (7 * 32) + c8 * pow2 (8 * 32) + c9 * pow2 (9 * 32) + c10 * pow2 (10 * 32) + c11 * pow2 (11 * 32) in

  let f1 = c21 * pow2 (4 * 32) + c22 * pow2 (5 * 32) + c23 * pow2 (6 * 32) in

  let f2 = c12 + c13 * pow2 (1 * 32) + c14 * pow2 (2 * 32) + c15 * pow2 (3 * 32) + c16 * pow2 (4 * 32) + c17 * pow2 (5 * 32) + c18 * pow2 (6 * 32) + c19 * pow2 (7 * 32) + c20 * pow2 (8 * 32) + c21 * pow2 (9 * 32) + c22 * pow2 (10 * 32) + c23 * pow2 (11 * 32) in

  let f3 = c21 + c22 * pow2 (1 * 32) + c23 * pow2 (2 * 32) + c12 * pow2 (3 * 32) + c13 * pow2 (4 * 32) + c14 * pow2 (5 * 32) + c15 * pow2 (6 * 32) + c16 * pow2 (7 * 32) + c17 * pow2 (8 * 32) + c18 * pow2 (9 * 32) + c19 * pow2 (10 * 32) + c20 * pow2 (11 * 32) in

  let f4 = c23 * pow2 (1 * 32) + c20 * pow2 (3 * 32) + c12 * pow2 (4 * 32) + c13 * pow2 (5 * 32) + c14 * pow2 (6 * 32) + c15 * pow2 (7 * 32) + c16 * pow2 (8 * 32) + c17 * pow2 (9 * 32) + c18 * pow2 (10 * 32) + c19 * pow2 (11 * 32) in

  let f5 = c20 * pow2 (4 * 32) + c21 * pow2 (5 * 32) + c22 * pow2 (6 * 32) + c23 * pow2 (7 * 32) in

  let f6 = c20 + c21 * pow2 (3 * 32) + c22 * pow2 (4 * 32) + c23 * pow2 (5 * 32) in

  let f7 = c23 + c12 * pow2 (1 * 32) + c13 * pow2 (2 * 32) + c14 * pow2 (3 * 32) + c15 * pow2 (4 * 32) + c16 * pow2 (5 * 32) + c17 * pow2 (6 * 32) + c18 * pow2 (7 * 32) + c19 * pow2 (8 * 32) + c20 * pow2 (9 * 32) + c21 * pow2 (10 * 32) + c22 * pow2 (11 * 32) in

  let f8 = c20 * pow2 (1 * 32) + c21 * pow2 (2 * 32) + c22 * pow2 (3 * 32) + c23 * pow2 (4 * 32) in

  let f9 = c23 * pow2 (3 * 32) + c23 * pow2 (4 * 32) in

  let n_ = f0 + 2 * f1 + f2 + f3 + f4 + f5 + f6 - f7 - f8 - f9 in

  sr_mod_0 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9;
  solinas_reduction_nat c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 n_;
  small_modulo_lemma_1 ((f0 + 2 * f1 + f2 + f3 + f4 + f5 + f6 - f7 - f8 - f9) % prime384) prime384


val lemma_opened: i:Lib.Sequence.lseq uint64 12 -> Lemma
  (let open Lib.Sequence in

    let i0 = index i  0 in
    let i1 = index i  1 in
    let i2 = index i  2 in
    let i3 = index i  3 in
    let i4 = index i  4 in
    let i5 = index i  5 in
    let i6 = index i  6 in
    let i7 = index i  7 in
    let i8 = index i  8 in
    let i9 = index i  9 in
    let i10 = index i 10 in
    let i11 = index i 11 in


    let c0 = get_low_part   i0 in
    let c1 = get_high_part  i0 in
    let c2 = get_low_part   i1 in
    let c3 = get_high_part  i1 in
    let c4 = get_low_part   i2 in
    let c5 = get_high_part  i2 in
    let c6 = get_low_part   i3 in
    let c7 = get_high_part  i3 in
    let c8 = get_low_part   i4 in
    let c9 = get_high_part  i4 in
    let c10 = get_low_part  i5 in
    let c11 = get_high_part i5 in
    let c12 = get_low_part  i6 in
    let c13 = get_high_part i6 in
    let c14 = get_low_part  i7 in
    let c15 = get_high_part i7 in
    let c16 = get_low_part  i8 in
    let c17 = get_high_part i8 in
    let c18 = get_low_part  i9 in
    let c19 = get_high_part i9 in
    let c20 = get_low_part  i10 in
    let c21 = get_high_part i10 in
    let c22 = get_low_part  i11 in
    let c23 = get_high_part i11 in

    lseq_as_nat i =
     v c0  * pow2 (0 * 32) +
     v c1  * pow2 (1 * 32) +
     v c2  * pow2 (2 * 32) +
     v c3  * pow2 (3 * 32) +
     v c4  * pow2 (4 * 32) +
     v c5  * pow2 (5 * 32) +
     v c6  * pow2 (6 * 32) +
     v c7  * pow2 (7 * 32) +
     v c8  * pow2 (8 * 32) +
     v c9  * pow2 (9 * 32) +
     v c10 * pow2 (10 * 32) +
     v c11 * pow2 (11 * 32) +
     v c12 * pow2 (12 * 32) +
     v c13 * pow2 (13 * 32) +
     v c14 * pow2 (14 * 32) +
     v c15 * pow2 (15 * 32) +
     v c16 * pow2 (16 * 32) +
     v c17 * pow2 (17 * 32) +
     v c18 * pow2 (18 * 32) +
     v c19 * pow2 (19 * 32) +
     v c20 * pow2 (20 * 32) +
     v c21 * pow2 (21 * 32) +
     v c22 * pow2 (22 * 32) +
     v c23 * pow2 (23 * 32)
  )

#push-options "--fuel 1"

val lemma_lseq_12_as_definition: i: Lib.Sequence.lseq uint64 12 -> Lemma (
  let open Lib.Sequence in 
  let i0 = index i 0 in
  let i1 = index i 1 in
  let i2 = index i 2 in
  let i3 = index i 3 in
  let i4 = index i 4 in
  let i5 = index i 5 in
  let i6 = index i 6 in
  let i7 = index i 7 in
  let i8 = index i 8 in 
  let i9 = index i 9 in 
  let i10 = index i 10 in 
  let i11 = index i 11 in 
  lseq_as_nat i == v i0 * pow2 (0 * 64) + v i1 * pow2 (1 * 64) + v i2 * pow2 (2 * 64) + v i3 * pow2 (3 * 64) + v i4 * pow2 (4 * 64) + v i5 * pow2 (5 * 64) + v i6 * pow2 (6 * 64) + v i7 * pow2 (7 * 64) +
  v i8 * pow2 (8 * 64) + v i9 * pow2 (9 * 64) + v i10 * pow2 (10 * 64) + v i11 * pow2 (11 * 64))

let lemma_lseq_12_as_definition i = 
  lseq_as_nat_zero i;
  lseq_as_nat_definiton i 1;
  lseq_as_nat_definiton i 2;
  lseq_as_nat_definiton i 3;
  lseq_as_nat_definiton i 4;
  lseq_as_nat_definiton i 5;
  
  lseq_as_nat_definiton i 6;
  lseq_as_nat_definiton i 7;
  lseq_as_nat_definiton i 8;
  lseq_as_nat_definiton i 9;
  lseq_as_nat_definiton i 10;
  lseq_as_nat_definiton i 11

#pop-options


let lemma_opened i =   
  let open Lib.Sequence in

  let i0 = index i 0 in
  let i1 = index i 1 in
  let i2 = index i 2 in
  let i3 = index i 3 in
  let i4 = index i 4 in
  let i5 = index i 5 in
  let i6 = index i 6 in
  let i7 = index i 7 in
  let i8 = index i 8 in 
  let i9 = index i 9 in 
  let i10 = index i 10 in 
  let i11 = index i 11 in 

  let c0  = get_low_part  i0 in
  let c1  = get_high_part i0 in
  let c2  = get_low_part  i1 in
  let c3  = get_high_part i1 in
  let c4  = get_low_part  i2 in
  let c5  = get_high_part i2 in
  let c6  = get_low_part  i3 in
  let c7  = get_high_part i3 in
  let c8  = get_low_part  i4 in
  let c9  = get_high_part i4 in
  let c10 = get_low_part  i5 in
  let c11 = get_high_part i5 in
  let c12 = get_low_part  i6 in
  let c13 = get_high_part i6 in
  let c14 = get_low_part  i7 in
  let c15 = get_high_part i7 in
  let c16 = get_low_part i8 in
  let c17 = get_high_part i8 in
  let c18 = get_low_part i9 in
  let c19 = get_high_part i9 in
  let c20 = get_low_part i10 in
  let c21 = get_high_part i10 in
  let c22 = get_low_part i11 in
  let c23 = get_high_part i11 in
   
  assert_norm (pow2 64 * pow2 64 = pow2 (2 * 64));
  assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 (3 * 64));
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (4 * 64));
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (5 * 64));
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (6 * 64));
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (7 * 64));
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (8 * 64));
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (9 * 64));
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (10 * 64));
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (11 * 64));

  calc (==) {
    v i0 * pow2 (0 * 64);
    == { }
    (v c0 + v c1 * pow2 32) * pow2 (0 * 64);
    == { }
    (v c0 + v c1 * pow2 32) * pow2 (0 * 32);
    == { }
    v c0 * pow2 (0 * 32) + v c1 * pow2 (1 * 32);
  };

  calc (==) {
    v i1 * pow2 (1 * 64);
    == { }
    (v c2 + v c3 * pow2 32) * pow2 (1 * 64);
    == { }
    (v c2 + v c3 * pow2 32) * pow2 (2 * 32);
    == { pow2_plus 32 (2 * 32) }
    v c2 * pow2 (2 * 32) + v c3 * pow2 (3 * 32);
  };

  calc (==) {
    v i2 * pow2 (2 * 64);
    == { }
    (v c4 + v c5 * pow2 32) * pow2 (2 * 64);
    == { }
    (v c4 + v c5 * pow2 32) * pow2 (4 * 32);
    == { pow2_plus 32 (4 * 32) }
    v c4 * pow2 (4 * 32) + v c5 * pow2 (5 * 32);
  };

  calc (==) {
    v i3 * pow2 (3 * 64);
    == { }
    (v c6 + v c7 * pow2 32) * pow2 (3 * 64);
    == { }
    (v c6 + v c7 * pow2 32) * pow2 (6 * 32);
    == { pow2_plus 32 (6 * 32) }
    v c6 * pow2 (6 * 32) + v c7 * pow2 (7 * 32);
  };

  calc (==) {
    v i4 * pow2 (4 * 64);
    == { }
    (v c8 + v c9 * pow2 32) * pow2 (4 * 64);
    == { }
    (v c8 + v c9 * pow2 32) * pow2 (8 * 32);
    == { pow2_plus 32 (8 * 32) }
    v c8 * pow2 (8 * 32) + v c9 * pow2 (9 * 32);
  };

  calc (==) {
    v i5 * pow2 (5 * 64);
    == { }
    (v c10 + v c11 * pow2 32) * pow2 (5 * 64);
    == { }
    (v c10 + v c11 * pow2 32) * pow2 (10 * 32);
    == { pow2_plus 32 (10 * 32) }
    v c10 * pow2 (10 * 32) + v c11 * pow2 (11 * 32);
  };

  calc (==) {
    v i6 * pow2 (6 * 64);
    == { }
    (v c12 + v c13 * pow2 32) * pow2 (6 * 64);
    == { }
    (v c12 + v c13 * pow2 32) * pow2 (12 * 32);
    == { pow2_plus 32 (12 * 32) }
    v c12 * pow2 (12 * 32) + v c13 * pow2 (13 * 32);
  };

  calc (==) {
    v i7 * pow2 (7 * 64);
    == { }
    (v c14 + v c15 * pow2 32) * pow2 (7 * 64);
    == { }
    (v c14 + v c15 * pow2 32) * pow2 (14 * 32);
    == { pow2_plus 32 (14 * 32) }
    v c14 * pow2 (14 * 32) + v c15 * pow2 (15 * 32);
  };

  calc (==) {
    v i8 * pow2 (8 * 64);
    == { }
    (v c16 + v c17 * pow2 32) * pow2 (8 * 64);
    == { }
    (v c16 + v c17 * pow2 32) * pow2 (16 * 32);
    == { pow2_plus 32 (16 * 32) }
    v c16 * pow2 (16 * 32) + v c17 * pow2 (17 * 32);
  };

  calc (==) {
    v i9 * pow2 (9 * 64);
    == { }
    (v c18 + v c19 * pow2 32) * pow2 (9 * 64);
    == { }
    (v c18 + v c19 * pow2 32) * pow2 (18 * 32);
    == { pow2_plus 32 (18 * 32) }
    v c18 * pow2 (18 * 32) + v c19 * pow2 (19 * 32);
  };

  calc (==) {
    v i10 * pow2 (10 * 64);
    == { }
    (v c20 + v c21 * pow2 32) * pow2 (10 * 64);
    == { }
    (v c20 + v c21 * pow2 32) * pow2 (20 * 32);
    == { pow2_plus 32 (20 * 32) }
    v c20 * pow2 (20 * 32) + v c21 * pow2 (21 * 32);
  };


  calc (==) {
    v i11 * pow2 (11 * 64);
    == { }
    (v c22 + v c23 * pow2 32) * pow2 (11 * 64);
    == { }
    (v c22 + v c23 * pow2 32) * pow2 (22 * 32);
    == { pow2_plus 32 (22 * 32) }
    v c22 * pow2 (22 * 32) + v c23 * pow2 (23 * 32);
  };


  calc (==) {
    lseq_as_nat i;
      
    == {lemma_lseq_12_as_definition i}
    v i0 * pow2 (0 * 64) +
    v i1 * pow2 (1 * 64) +
    v i2 * pow2 (2 * 64) +
    v i3 * pow2 (3 * 64) +
    v i4 * pow2 (4 * 64) +
    v i5 * pow2 (5 * 64) +
    v i6 * pow2 (6 * 64) +
    v i7 * pow2 (7 * 64) +
    v i8 * pow2 (8 * 64) +
    v i9 * pow2 (9 * 64) +
    v i10 * pow2 (10 * 64) +
    v i11 * pow2 (11 * 64); 
    == { }
    (v c0  * pow2 (0 * 32)  + v c1  * pow2 (1 * 32)) +
    (v c2  * pow2 (2 * 32)  + v c3  * pow2 (3 * 32)) +
    (v c4  * pow2 (4 * 32)  + v c5  * pow2 (5 * 32)) +
    (v c6  * pow2 (6 * 32)  + v c7  * pow2 (7 * 32)) +
    (v c8  * pow2 (8 * 32)  + v c9  * pow2 (9 * 32)) +
    (v c10 * pow2 (10 * 32) + v c11 * pow2 (11 * 32)) +
    (v c12 * pow2 (12 * 32) + v c13 * pow2 (13 * 32)) +
    (v c14 * pow2 (14 * 32) + v c15 * pow2 (15 * 32)) +
    (v c16 * pow2 (16 * 32) + v c17 * pow2 (17 * 32)) +
    (v c18 * pow2 (18 * 32) + v c19 * pow2 (19 * 32)) +
    (v c20 * pow2 (20 * 32) + v c21 * pow2 (21 * 32)) +
    (v c22 * pow2 (22 * 32) + v c23 * pow2 (23 * 32));
    == { }
    v c0  * pow2 (0 * 32) +
    v c1  * pow2 (1 * 32) +
    v c2  * pow2 (2 * 32) +
    v c3  * pow2 (3 * 32) +
    v c4  * pow2 (4 * 32) +
    v c5  * pow2 (5 * 32) +
    v c6  * pow2 (6 * 32) +
    v c7  * pow2 (7 * 32) +
    v c8  * pow2 (8 * 32) +
    v c9  * pow2 (9 * 32) +
    v c10 * pow2 (10 * 32) +
    v c11 * pow2 (11 * 32) +
    v c12 * pow2 (12 * 32) +
    v c13 * pow2 (13 * 32) +
    v c14 * pow2 (14 * 32) +
    v c15 * pow2 (15 * 32) +
    v c16 * pow2 (16 * 32) +
    v c17 * pow2 (17 * 32) +
    v c18 * pow2 (18 * 32) +
    v c19 * pow2 (19 * 32) +
    v c20 * pow2 (20 * 32) +
    v c21 * pow2 (21 * 32) +
    v c22 * pow2 (22 * 32) +
    v c23 * pow2 (23 * 32) ; 
  }


let solinas_reduction_impl_p384 i o =
  push_frame();
    let h0 = ST.get() in
    let tempBuffer = create (size 60) (u64 0) in

    let t0 = sub tempBuffer (size 0) (size 6) in
    let t1 = sub tempBuffer (size 6) (size 6) in
    let t2 = sub tempBuffer (size 12) (size 6) in
    let t3 = sub tempBuffer (size 18) (size 6) in
    let t4 = sub tempBuffer (size 24) (size 6) in
    let t5 = sub tempBuffer (size 30) (size 6) in
    let t6 = sub tempBuffer (size 36) (size 6) in
    let t7 = sub tempBuffer (size 42) (size 6) in
    let t8 = sub tempBuffer (size 48) (size 6) in
    let t9 = sub tempBuffer (size 54) (size 6) in

    let i0 = i.(size 0) in
    let i1 = i.(size 1) in
    let i2 = i.(size 2) in
    let i3 = i.(size 3) in
    let i4 = i.(size 4) in
    let i5 = i.(size 5) in
    let i6 = i.(size 6) in
    let i7 = i.(size 7) in
    let i8 = i.(size 8) in
    let i9 = i.(size 9) in
    let i10 = i.(size 10) in
    let i11 = i.(size 11) in

    let c0 = get_low_part i0 in
    let c1 = get_high_part i0 in
    let c2 = get_low_part i1 in
    let c3 = get_high_part i1 in
    let c4 = get_low_part i2 in
    let c5 = get_high_part i2 in
    let c6 = get_low_part i3 in
    let c7 = get_high_part i3 in
    let c8 = get_low_part i4 in
    let c9 = get_high_part i4 in
    let c10 = get_low_part i5 in
    let c11 = get_high_part i5 in
    let c12 = get_low_part i6 in
    let c13 = get_high_part i6 in
    let c14 = get_low_part i7 in
    let c15 = get_high_part i7 in
    let c16 = get_low_part i8 in
    let c17 = get_high_part i8 in
    let c18 = get_low_part i9 in
    let c19 = get_high_part i9 in
    let c20 = get_low_part i10 in
    let c21 = get_high_part i10 in
    let c22 = get_low_part i11 in
    let c23 = get_high_part i11 in

    solinas_reduction_upload c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 tempBuffer;
      let h1 = ST.get() in
    solinas_reduction_operations tempBuffer o;
      let h2 = ST.get() in

    solinas_reduction_mod (v c0) (v c1) (v c2) (v c3) (v c4) (v c5) (v c6) (v c7) (v c8) (v c9) (v c10) (v c11) (v c12) (v c13) (v c14) (v c15) (v c16) (v c17) (v c18) (v c19) (v c20) (v c21) (v c22) (v c23)
    (as_nat P384 h1 t0) (as_nat P384 h1 t1) (as_nat P384 h1 t2) (as_nat P384 h1 t3) (as_nat P384 h1 t4) (as_nat P384 h1 t5) (as_nat P384 h1 t6) (as_nat P384 h1 t7) (as_nat P384 h1 t8) (as_nat P384 h1 t9) (as_nat P384 h2 o);

    modulo_lemma (as_nat P384 h2 o) prime384;
    lemma_opened (as_seq h0 i);
    pop_frame()


