module Hacl.Impl.SolinasReduction.P256

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open FStar.Math.Lemmas
open FStar.Math.Lib
open Lib.Buffer

open Hacl.SolinasReductionP256.Lemmas
open Spec.ECC
open Spec.ECC.Curves
open Hacl.Impl.EC.LowLevel

open Hacl.Impl.EC.Setup

open Hacl.Spec.EC.Definition
open FStar.Mul

module BV = FStar.BitVector
module Seq = FStar.Seq

#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"

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


inline_for_extraction noextract
val store_high_low_u: high:uint32 -> low:uint32 -> r:uint64{v r = v high * pow2 32 + v low}

let store_high_low_u high low =
  let as_uint64_high = to_u64 high in
  let as_uint64_high = Lib.IntTypes.shift_left as_uint64_high (size 32) in
  let as_uint64_low = to_u64 low in
  assert (v as_uint64_high = v high * pow2 32);
  assert (v as_uint64_low = v low);
  lemma_xor_zero as_uint64_low as_uint64_high;
  logxor as_uint64_low as_uint64_high


#push-options "--z3rlimit 100 --fuel 1"


inline_for_extraction noextract
val load_buffer: a0: uint64 -> a1: uint64 -> a2: uint64 -> a3: uint64
  -> o: lbuffer uint64 (size 4)
  -> Stack unit
  (requires fun h -> live h o)
  (ensures  fun h0 _ h1 -> modifies (loc o) h0 h1 /\
    as_nat P256 h1 o = v a0 + v a1 * pow2 64 + v a2 * pow2 (64 * 2) + v a3 * pow2 (64 * 3))

let load_buffer a0 a1 a2 a3 o =
  assert_norm (pow2 64 * pow2 64 = pow2 (64 * 2));
  assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 (64 * 3)); 
  upd o (size 0) a0;
  upd o (size 1) a1;
  upd o (size 2) a2;
  upd o (size 3) a3;

  let h0 = ST.get() in
  
  let o_seq = as_seq h0 o in 
  lseq_as_nat_zero o_seq;
  lseq_as_nat_definiton o_seq 1;
  lseq_as_nat_definiton o_seq 2;
  lseq_as_nat_definiton o_seq 3
  

#pop-options


inline_for_extraction noextract
val upl_zer_buffer: c0: uint32 -> c1: uint32 -> c2: uint32 -> c3: uint32 -> c4: uint32 -> c5: uint32 -> c6: uint32 
  -> c7: uint32 -> o: lbuffer uint64 (size 4) ->
  Stack unit
  (requires fun h -> live h o)
  (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\
    as_nat P256 h1 o == (v c0 + v c1 * pow2 (1 * 32) + v c2 * pow2 (2 * 32) + v c3 * pow2 (3 * 32) + v c4 * pow2 (4 * 32) + v c5 * pow2 (5 * 32) + v  c6 * pow2 (6 * 32) + v c7 * pow2 (7 * 32)) % prime256)

let upl_zer_buffer c0 c1 c2 c3 c4 c5 c6 c7 o =
  let b0 = store_high_low_u c1 c0 in
  let b1 = store_high_low_u c3 c2 in
  let b2 = store_high_low_u c5 c4 in
  let b3 = store_high_low_u c7 c6 in
    assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
    assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
    assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
    assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
    assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));

  load_buffer b0 b1 b2 b3 o;
  reduction_prime_2prime #P256 o o


inline_for_extraction noextract
val upl_fir_buffer: c11: uint32 -> c12: uint32 -> c13: uint32 -> c14: uint32 -> c15: uint32
  -> o: lbuffer uint64 (size 4) ->
  Stack unit
  (requires fun h -> live h o)
  (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\
    as_nat P256 h1 o == (v c11 * pow2 (3 * 32) + v c12 * pow2 (4 * 32) + v c13 * pow2 (5 * 32) + v c14 * pow2 (6 * 32) + v c15 * pow2 (7 * 32)) % prime256)

let upl_fir_buffer c11 c12 c13 c14 c15 o =
  assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
  assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
  assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
  assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
  assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
  
  let b0 = u64 0 in
  let b1 = store_high_low_u c11 (u32 0) in
  let b2 = store_high_low_u c13 c12 in
  let b3 = store_high_low_u c15 c14 in
  
  load_buffer b0 b1 b2 b3 o;
  reduction_prime_2prime #P256 o o


inline_for_extraction noextract
val upl_sec_buffer: c12: uint32 -> c13: uint32 -> c14: uint32 -> c15: uint32
  -> o: lbuffer uint64 (size 4) ->
  Stack unit
  (requires fun h -> live h o)
  (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\ as_nat P256 h1 o < prime /\
    as_nat P256 h1 o == (v c12 * pow2 (3 * 32) + v c13 * pow2 (4 * 32) + v c14 * pow2 (5 * 32) + v c15 * pow2 (6 * 32)) % prime
  )

let upl_sec_buffer c12 c13 c14 c15 o =
  assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
  assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
  assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
  assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
  assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
  
  let b0 = u64 0 in
  let b1 = store_high_low_u c12 (u32 0) in
  let b2 = store_high_low_u c14 c13 in
  let b3 = store_high_low_u (u32 0) c15 in
  load_buffer b0 b1 b2 b3 o;
  assert_norm(v c12 * pow2 (3 * 32) + v c13 * pow2 (4 * 32) + v c14 * pow2 (5 * 32) + v c15 * pow2 (6 * 32) < prime);
  
  let h1 = ST.get() in
  modulo_lemma (as_nat P256 h1 o) prime


inline_for_extraction noextract
val upl_thi_buffer: c8: uint32 -> c9: uint32 -> c10: uint32 -> c14: uint32 -> c15: uint32
  -> o: lbuffer uint64 (size 4) ->
  Stack unit
  (requires fun h -> live h o)
  (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\
    as_nat P256 h1 o == (v c8 + v c9 * pow2 32 + v c10 * pow2 (2 * 32) +  v c14 * pow2 (6 * 32) + v c15 * pow2 (7 * 32)) % prime256)

let upl_thi_buffer c8 c9 c10 c14 c15 o =
  assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
  assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
  assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
  assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
  assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
   
  let b0 = store_high_low_u c9 c8 in
  let b1 = store_high_low_u (u32 0) c10 in
  let b2 = u64 0 in
  let b3 = store_high_low_u c15 c14 in
  
  load_buffer b0 b1 b2 b3 o;
  reduction_prime_2prime #P256 o o


inline_for_extraction noextract
val upl_for_buffer: c8: uint32 -> c9: uint32 -> c10: uint32 -> c11: uint32 -> c13: uint32 -> c14: uint32 -> c15: uint32 
  -> o: lbuffer uint64 (size 4) ->
  Stack unit
  (requires fun h -> live h o)
  (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\
    as_nat P256 h1 o == (v c9 + v c10 * pow2 32 + v c11 * pow2 (2 * 32) + v c13 * pow2 (3 * 32) + v c14 * pow2 (4 * 32) + v c15 * pow2 (5 * 32) + v c13 * pow2 (6 * 32) +  v c8 * pow2 (7 * 32)) % prime256)

let upl_for_buffer c8 c9 c10 c11 c13 c14 c15 o =
  assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
  assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
  assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
  assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
  assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
  
  let b0 = store_high_low_u c10 c9 in
  let b1 = store_high_low_u c13 c11 in
  let b2 = store_high_low_u c15 c14 in
  let b3 = store_high_low_u c8 c13 in
  
  load_buffer b0 b1 b2 b3 o;
  reduction_prime_2prime #P256 o o


inline_for_extraction noextract
val upl_fif_buffer: c8: uint32 -> c10: uint32 -> c11: uint32 -> c12: uint32 -> c13: uint32
  -> o: lbuffer uint64 (size 4) ->
  Stack unit
  (requires fun h -> live h o)
  (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\
    as_nat P256 h1 o == (v c11 + v c12 * pow2 32 + v c13 * pow2 (2 * 32) + v c8 * pow2 (6 * 32) + v c10 * pow2 (7 * 32)) % prime256)

let upl_fif_buffer c8 c10 c11 c12 c13 o =
  assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
  assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
  assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
  assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
  assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
  
  let b0 = store_high_low_u c12 c11 in
  let b1 = store_high_low_u (u32 0) c13 in
  let b2 = u64 0 in
  let b3 = store_high_low_u c10 c8 in
  
  load_buffer b0 b1 b2 b3 o;
  reduction_prime_2prime #P256 o o


inline_for_extraction noextract
val upl_six_buffer: c9: uint32 -> c11: uint32 -> c12: uint32 -> c13: uint32 -> c14: uint32 -> c15: uint32 
  -> o: lbuffer uint64 (size 4) ->
  Stack unit
  (requires fun h -> live h o)
  (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\ 
    as_nat P256 h1 o == (v c12 + v c13 * pow2 32 + v c14 * pow2 (2 * 32) + v c15 * pow2 (3 * 32) + v c9 * pow2 (6 * 32) + v c11 * pow2 (7 * 32)) % prime256)

let upl_six_buffer c9 c11 c12 c13 c14 c15 o =
  assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
  assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
  assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
  assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
  assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
  
  let b0 = store_high_low_u c13 c12 in
  let b1 = store_high_low_u c15 c14 in
  let b2 = u64 0 in
  let b3 = store_high_low_u c11 c9 in
  
  load_buffer b0 b1 b2 b3 o;
  reduction_prime_2prime #P256 o o


inline_for_extraction noextract
val upl_sev_buffer: c8: uint32 -> c9: uint32 -> c10: uint32 -> c12: uint32 -> c13: uint32 ->
  c14: uint32 -> c15: uint32 -> o: lbuffer uint64 (size 4) ->
  Stack unit
  (requires fun h -> live h o)
  (ensures fun h0 _ h1 -> modifies (loc o)  h0 h1 /\
    as_nat P256 h1 o == (v c13 + v c14 * pow2 32 + v c15 * pow2 (2 * 32) + v c8 * pow2 (3 * 32) +  v c9 * pow2 (4 * 32) + v c10 * pow2 (5 * 32) + v c12 * pow2 (7 * 32)) % prime256)

let upl_sev_buffer c8 c9 c10 c12 c13 c14 c15 o =
  assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
  assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
  assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
  assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
  assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
  
  let b0 = store_high_low_u c14 c13 in
  let b1 = store_high_low_u c8 c15 in
  let b2 = store_high_low_u c10 c9 in
  let b3 = store_high_low_u c12 (u32 0) in
  
  load_buffer b0 b1 b2 b3 o;
  reduction_prime_2prime #P256 o o


inline_for_extraction noextract
val upl_eig_buffer: c9: uint32 -> c10: uint32 -> c11: uint32 -> c12: uint32 -> c13: uint32 ->
  c14: uint32 -> c15: uint32 -> o: lbuffer uint64 (size 4) ->
  Stack unit
  (requires fun h -> live h o)
  (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\ as_nat P256 h1 o == (v c14 + v c15 * pow2 32 + v c9 * pow2 (3 * 32) + v c10 * pow2 (4 * 32) + v c11 * pow2 (5 * 32) + v c13 * pow2 (7 * 32)) % prime256)

let upl_eig_buffer c9 c10 c11 c12 c13 c14 c15 o =
  assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
  assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
  assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
  assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
  assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
  
  let b0 = store_high_low_u c15 c14 in
  let b1 = store_high_low_u c9 (u32 0) in
  let b2 = store_high_low_u c11 c10 in
  let b3 = store_high_low_u c13 (u32 0) in
  
  load_buffer b0 b1 b2 b3 o;
  reduction_prime_2prime #P256 o o


inline_for_extraction noextract
val solinas_reduction_upload: c0: uint32 -> c1: uint32 -> c2: uint32 -> c3: uint32 -> c4: uint32 -> c5: uint32 -> c6: uint32 
  -> c7: uint32 -> c8: uint32 -> c9: uint32 -> c10: uint32 -> c11: uint32 -> c12: uint32 -> c13: uint32 -> c14: uint32 
  -> c15: uint32 -> tempBuffer: lbuffer uint64 (size 36) ->
  Stack unit
  (requires fun h -> live h tempBuffer)
  (ensures fun h0 _ h1 -> modifies1 tempBuffer h0 h1 /\ (
    let t0 = as_nat P256 h1 (gsub tempBuffer (size 0) (size 4)) in
    let t1 = as_nat P256 h1 (gsub tempBuffer (size 4) (size 4)) in
    let t2 = as_nat P256 h1 (gsub tempBuffer (size 8) (size 4)) in
    let t3 = as_nat P256 h1 (gsub tempBuffer (size 12) (size 4)) in
    let t4 = as_nat P256 h1 (gsub tempBuffer (size 16) (size 4)) in
    let t5 = as_nat P256 h1 (gsub tempBuffer (size 20) (size 4)) in
    let t6 = as_nat P256 h1 (gsub tempBuffer (size 24) (size 4)) in
    let t7 = as_nat P256 h1 (gsub tempBuffer (size 28) (size 4)) in
    let t8 = as_nat P256 h1 (gsub tempBuffer (size 32) (size 4)) in
    
    t0 == (v c0 + v c1 * pow2 (1 * 32) + v c2 * pow2 (2 * 32) + v c3 * pow2 (3 * 32) + v c4 * pow2 (4 * 32) + v c5 * pow2 (5 * 32) + v  c6 * pow2 (6 * 32) +  v c7 * pow2 (7 * 32)) % prime /\
    t1 == (v c11 * pow2 (3 * 32) + v c12 * pow2 (4 * 32) + v c13 * pow2 (5 * 32) + v c14 * pow2 (6 * 32) + v c15 * pow2 (7 * 32)) % prime /\
    t2 == (v c12 * pow2 (3 * 32) + v c13 * pow2 (4 * 32) +  v c14 * pow2 (5 * 32) + v c15 * pow2 (6 * 32)) % prime  /\
    t3 == (v c8 + v c9 * pow2 32 + v c10 * pow2 (2 * 32) + v c14 * pow2 (6 * 32) + v c15 * pow2 (7 * 32)) % prime /\
    t4 == (v c9 + v c10 * pow2 32 + v c11 * pow2 (2 * 32) + v c13 * pow2 (3 * 32) + v c14 * pow2 (4 * 32) + v c15 * pow2 (5 * 32) + v c13 * pow2 (6 * 32) + v c8 * pow2 (7 * 32)) % prime /\
    t5 == (v c11 + v c12 * pow2 32 + v c13 * pow2 (2 * 32) + v c8 * pow2 (6 * 32) + v c10 * pow2 (7 * 32)) % prime /\
    t6 == (v c12 + v c13 * pow2 32 + v c14 * pow2 (2 * 32) + v c15 * pow2 (3 * 32) + v c9 * pow2 (6 * 32) + v c11 * pow2 (7 * 32)) % prime /\
    t7 == (v c13 + v c14 * pow2 32 + v c15 * pow2 (2 * 32) +  v c8 * pow2 (3 * 32) +  v c9 * pow2 (4 * 32) + v c10 * pow2 (5 * 32) + v c12 * pow2 (7 * 32)) % prime /\
    t8 == (v c14 + v c15 * pow2 32 + v c9 * pow2 (3 * 32) +  v c10 * pow2 (4 * 32) + v c11 * pow2 (5 * 32) + v c13 * pow2 (7 * 32)) % prime))


let solinas_reduction_upload c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 tempBuffer =
  let t0 = sub tempBuffer (size 0) (size 4) in
  let t1 = sub tempBuffer (size 4) (size 4) in
  let t2 = sub tempBuffer (size 8) (size 4) in
  let t3 = sub tempBuffer (size 12) (size 4) in
  let t4 = sub tempBuffer (size 16) (size 4) in
  let t5 = sub tempBuffer (size 20) (size 4) in
  let t6 = sub tempBuffer (size 24) (size 4) in
  let t7 = sub tempBuffer (size 28) (size 4) in
  let t8 = sub tempBuffer (size 32) (size 4) in
  
  upl_zer_buffer c0 c1 c2 c3 c4 c5 c6 c7 t0;
  upl_fir_buffer c11 c12 c13 c14 c15 t1;
  upl_sec_buffer c12 c13 c14 c15 t2;
  upl_thi_buffer c8 c9 c10 c14 c15  t3;
  upl_for_buffer c8 c9 c10 c11 c13 c14 c15 t4;
  upl_fif_buffer c8 c10 c11 c12 c13 t5;
  upl_six_buffer c9 c11 c12 c13 c14 c15 t6;
  upl_sev_buffer c8 c9 c10 c12 c13 c14 c15 t7;
  upl_eig_buffer c9 c10 c11 c12 c13 c14 c15 t8


inline_for_extraction noextract
val solinas_reduction_operations: tempBuffer: lbuffer uint64 (size 36) -> o: lbuffer uint64 (size 4) ->
  Stack unit
  (requires fun h -> live h o /\ live h tempBuffer /\ disjoint tempBuffer o /\ (
    let t0 = as_nat P256 h (gsub tempBuffer (size 0) (size 4)) in
    let t1 = as_nat P256 h (gsub tempBuffer (size 4) (size 4)) in
    let t2 = as_nat P256 h (gsub tempBuffer (size 8) (size 4)) in
    let t3 = as_nat P256 h (gsub tempBuffer (size 12) (size 4)) in
    let t4 = as_nat P256 h (gsub tempBuffer (size 16) (size 4)) in
    let t5 = as_nat P256 h (gsub tempBuffer (size 20) (size 4)) in
    let t6 = as_nat P256 h (gsub tempBuffer (size 24) (size 4)) in
    let t7 = as_nat P256 h (gsub tempBuffer (size 28) (size 4)) in
    let t8 = as_nat P256 h (gsub tempBuffer (size 32) (size 4)) in
    t0 < prime /\ t1 < prime /\ t2 < prime /\ t3 < prime /\ t4 < prime /\ t5 < prime /\ t6 < prime /\ t7 < prime /\ t8 < prime))
  (ensures fun h0 _ h1 -> modifies2 tempBuffer o h0 h1 /\ (
    let t0 = as_nat P256 h0 (gsub tempBuffer (size 0) (size 4)) in
    let t1 = as_nat P256 h0 (gsub tempBuffer (size 4) (size 4)) in
    let t2 = as_nat P256 h0 (gsub tempBuffer (size 8) (size 4)) in
    let t3 = as_nat P256 h0 (gsub tempBuffer (size 12) (size 4)) in
    let t4 = as_nat P256 h0 (gsub tempBuffer (size 16) (size 4)) in
    let t5 = as_nat P256 h0 (gsub tempBuffer (size 20) (size 4)) in
    let t6 = as_nat P256 h0 (gsub tempBuffer (size 24) (size 4)) in
    let t7 = as_nat P256 h0 (gsub tempBuffer (size 28) (size 4)) in
    let t8 = as_nat P256 h0 (gsub tempBuffer (size 32) (size 4)) in
    as_nat P256 h1 o == (t0 + 2 * t1 + 2 * t2  + t3 + t4 - t5  - t6 - t7 - t8) % prime))

let solinas_reduction_operations tempBuffer o =
    let h0 = ST.get() in
    let t0 = sub tempBuffer (size 0) (size 4) in
    let t1 = sub tempBuffer (size 4) (size 4) in
    let t2 = sub tempBuffer (size 8) (size 4) in
    let t3 = sub tempBuffer (size 12) (size 4) in
    let t4 = sub tempBuffer (size 16) (size 4) in
    let t5 = sub tempBuffer (size 20) (size 4) in
    let t6 = sub tempBuffer (size 24) (size 4) in
    let t7 = sub tempBuffer (size 28) (size 4) in
    let t8 = sub tempBuffer (size 32) (size 4) in

    felem_double #P256 t2 t2;
    felem_double #P256 t1 t1;
    felem_add #P256 t0 t1 o;
    felem_add #P256 t2 o o;
    felem_add #P256 t3 o o;
    felem_add #P256 t4 o o;
    felem_sub #P256 o t5 o;
    felem_sub #P256 o t6 o;
    felem_sub #P256 o t7 o;
    felem_sub #P256 o t8 o;

    reduce_brackets (as_nat P256 h0 t0) (as_nat P256 h0 t1) (as_nat P256 h0 t2) (as_nat P256 h0 t3) (as_nat P256 h0 t4) (as_nat P256 h0 t5) (as_nat P256 h0 t6) (as_nat P256 h0 t7) (as_nat P256 h0 t8)


val lemma_opened: i:Lib.Sequence.lseq uint64 8 -> Lemma
  (let open Lib.Sequence in

   let i0 = index i 0 in
   let i1 = index i 1 in
   let i2 = index i 2 in
   let i3 = index i 3 in
   let i4 = index i 4 in
   let i5 = index i 5 in
   let i6 = index i 6 in
   let i7 = index i 7 in

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
     v c15 * pow2 (15 * 32))

#push-options "--z3rlimit 400 --fuel 1"

val lemma_lseq_8_as_definition: i: Lib.Sequence.lseq uint64 8 -> Lemma (
  let open Lib.Sequence in 
  let i0 = index i 0 in
  let i1 = index i 1 in
  let i2 = index i 2 in
  let i3 = index i 3 in
  let i4 = index i 4 in
  let i5 = index i 5 in
  let i6 = index i 6 in
  let i7 = index i 7 in 
  lseq_as_nat i == v i0 * pow2 (0 * 64) + v i1 * pow2 (1 * 64) + v i2 * pow2 (2 * 64) + v i3 * pow2 (3 * 64) + v i4 * pow2 (4 * 64) + v i5 * pow2 (5 * 64) + v i6 * pow2 (6 * 64) + v i7 * pow2 (7 * 64))

let lemma_lseq_8_as_definition i = 
  lseq_as_nat_zero i;
  lseq_as_nat_definiton i 1;
  lseq_as_nat_definiton i 2;
  lseq_as_nat_definiton i 3;
  
  lseq_as_nat_definiton i 4;
  lseq_as_nat_definiton i 5;
  lseq_as_nat_definiton i 6;
  lseq_as_nat_definiton i 7

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

  assert_norm (pow2 64 * pow2 64 = pow2 (2 * 64));
  assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 (3 * 64));
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (4 * 64));
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (5 * 64));
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64  = pow2 (6 * 64));
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (7 * 64));

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
    lseq_as_nat i;
    == { lemma_lseq_8_as_definition i }
    v i0 * pow2 (0 * 64) +
    v i1 * pow2 (1 * 64) +
    v i2 * pow2 (2 * 64) +
    v i3 * pow2 (3 * 64) +
    v i4 * pow2 (4 * 64) +
    v i5 * pow2 (5 * 64) +
    v i6 * pow2 (6 * 64) +
    v i7 * pow2 (7 * 64);
    == { }
    (v c0  * pow2 (0 * 32)  + v c1  * pow2 (1 * 32)) +
    (v c2  * pow2 (2 * 32)  + v c3  * pow2 (3 * 32)) +
    (v c4  * pow2 (4 * 32)  + v c5  * pow2 (5 * 32)) +
    (v c6  * pow2 (6 * 32)  + v c7  * pow2 (7 * 32)) +
    (v c8  * pow2 (8 * 32)  + v c9  * pow2 (9 * 32)) +
    (v c10 * pow2 (10 * 32) + v c11 * pow2 (11 * 32)) +
    (v c12 * pow2 (12 * 32) + v c13 * pow2 (13 * 32)) +
    (v c14 * pow2 (14 * 32) + v c15 * pow2 (15 * 32));
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
    v c15 * pow2 (15 * 32);
  }

[@CInline]
val solinas_reduction_impl_p256: i: lbuffer uint64 (getCoordinateLenU64 P256 *. 2ul) 
  -> o: lbuffer uint64 (getCoordinateLenU64 P256) -> 
  Stack unit
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures fun h0 _ h1 -> modifies1 o h0 h1 /\ wide_as_nat P256 h0 i % (getPrime P256) == as_nat P256 h1 o)


let solinas_reduction_impl_p256 i o =
  push_frame();

    let h0 = ST.get() in
    let tempBuffer = create (size 36) (u64 0) in

    let t0 = sub tempBuffer (size 0) (size 4) in
    let t1 = sub tempBuffer (size 4) (size 4) in
    let t2 = sub tempBuffer (size 8) (size 4) in
    let t3 = sub tempBuffer (size 12) (size 4) in
    let t4 = sub tempBuffer (size 16) (size 4) in
    let t5 = sub tempBuffer (size 20) (size 4) in
    let t6 = sub tempBuffer (size 24) (size 4) in
    let t7 = sub tempBuffer (size 28) (size 4) in
    let t8 = sub tempBuffer (size 32) (size 4) in

    let i0 = i.(size 0) in
    let i1 = i.(size 1) in
    let i2 = i.(size 2) in
    let i3 = i.(size 3) in
    let i4 = i.(size 4) in
    let i5 = i.(size 5) in
    let i6 = i.(size 6) in
    let i7 = i.(size 7) in
    let i8 = i.(size 7) in

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

    lemma_opened (as_seq h0 i);
    solinas_reduction_upload c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 tempBuffer;
    let h1 = ST.get() in
    solinas_reduction_operations tempBuffer o;
    let h2 = ST.get() in

    solinas_reduction_mod (v c0) (v c1) (v c2) (v c3) (v c4) (v c5) (v c6) (v c7) (v c8) (v c9) (v c10) (v c11) (v c12) (v c13) (v c14) (v c15) (as_nat P256 h1 t0) (as_nat P256 h1 t1) (as_nat P256 h1 t2) (as_nat P256 h1 t3) (as_nat P256 h1 t4) (as_nat P256 h1 t5) (as_nat P256 h1 t6) (as_nat P256 h1 t7) (as_nat P256 h1 t8) (as_nat P256 h2 o);

    modulo_lemma (as_nat P256 h2 o) prime;
  pop_frame()


