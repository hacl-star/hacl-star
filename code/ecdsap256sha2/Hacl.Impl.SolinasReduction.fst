module Hacl.Impl.SolinasReduction

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes 
open FStar.Math.Lemmas
open FStar.Math.Lib
open Lib.Buffer

open Hacl.Spec.P256.SolinasReduction
open Hacl.Impl.LowLevel
open Hacl.Impl.P256.LowLevel

open Hacl.Spec.P256.Definitions
open FStar.Mul


module Seq = Lib.Sequence

inline_for_extraction noextract
val get_high_part: a: uint64 -> Tot (r: uint32{uint_v r == uint_v a / (pow2 32)})

let get_high_part a = 
  to_u32(shift_right a (size 32))

inline_for_extraction noextract
val get_low_part: a: uint64 -> Tot (r: uint32{uint_v r == uint_v a % (pow2 32)}) 

let get_low_part a = to_u32 a

val lemma_xor_zero: low: uint64{uint_v (get_high_part low) ==  0} -> high: uint64{uint_v (get_low_part high) == 0} ->  Lemma (uint_v (logxor low high) = uint_v high * pow2 32 + uint_v low)

let lemma_xor_zero low high = 
  assert(uint_v low = uint_v (get_low_part low));
  assert(uint_v high = uint_v (get_high_part high) * pow2 32);
  admit()

val store_high_low_u: high: uint32 -> low: uint32 -> Tot (r: uint64 {uint_v r = uint_v high * pow2 32 + uint_v low})

let store_high_low_u high low = 
  let as_uint64_high = to_u64 high in 
  let as_uint64_high = Lib.IntTypes.shift_left as_uint64_high (size 32) in 
  let as_uint64_low = to_u64 low in
  lemma_xor_zero as_uint64_low as_uint64_high;
  logxor as_uint64_low as_uint64_high


#reset-options "--z3refresh --z3rlimit 300"

inline_for_extraction noextract
val load_buffer: a0: uint64 -> a1: uint64 -> a2: uint64 -> a3: uint64 -> o: lbuffer uint64 (size 4) -> 
  Stack unit
    (requires fun h -> live h o)
    (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\ 
    as_nat h1 o = uint_v a0 + uint_v a1 * pow2 64 + uint_v a2 * pow2 128 + uint_v a3 * pow2 192)

let load_buffer a0 a1 a2 a3 o = 
  assert_norm (pow2 64 * pow2 64 = pow2 128);
  assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);
  upd o (size 0) a0;
  upd o (size 1) a1;
  upd o (size 2) a2;
  upd o (size 3) a3


val upl_zer_buffer: c0: uint32 -> c1: uint32 -> c2: uint32 -> c3: uint32 -> c4: uint32 -> 
  c5: uint32 -> c6: uint32 -> c7: uint32
  -> temp: lbuffer uint64 (size 4) 
  -> o: lbuffer uint64 (size 4) -> 
  Stack unit
    (requires fun h -> 
      live h o /\ live h temp /\ disjoint o temp)
    (ensures fun h0 _ h1 -> 
      modifies (loc o |+| loc temp) h0 h1 /\ 
      (
	as_nat h1 o == (uint_v c0 + uint_v c1 * pow2 (1 * 32) + uint_v c2 * pow2 (2 * 32) + uint_v c3 * pow2 (3 * 32) + uint_v c4 * pow2 (4 * 32) + uint_v c5 * pow2 (5 * 32) + uint_v  c6 * pow2 (6 * 32) + uint_v c7 * pow2 (7 * 32)) % prime256
      )
   )

let upl_zer_buffer c0 c1 c2 c3 c4 c5 c6 c7 temp o = 
    let b0 = store_high_low_u c1 c0 in 
    let b1 = store_high_low_u c3 c2 in 
    let b2 = store_high_low_u c5 c4 in 
    let b3 = store_high_low_u c7 c6 in 
      assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
      assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
      assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
      assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
      assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
   
    assert(uint_v b0 = uint_v c1 * pow2 32 + uint_v c0);
    assert(uint_v b1 = uint_v c3 * pow2 32 + uint_v c2);
    assert(uint_v b2 = uint_v c5 * pow2 32 + uint_v c4);
    assert(uint_v b3 = uint_v c7 * pow2 32 + uint_v c6);
    
    load_buffer b0 b1 b2 b3 temp;
    reduction_prime_2prime_impl temp o;
      let h2 = ST.get() in 
    assert(as_nat h2 o = (uint_v c1 * pow2 32 + uint_v c0 + uint_v c3 * pow2 (3 * 32) + uint_v c2 * pow2 (2 * 32) + uint_v c5 * pow2 (32 * 5) + uint_v c4 * pow2 (32 * 4) + uint_v c7 * pow2 (32 * 7) + uint_v c6 * pow2 (32 * 6)) % prime256)


val upl_fir_buffer: c11: uint32 -> c12: uint32 -> c13: uint32 -> c14: uint32 -> c15: uint32
  -> temp: lbuffer uint64 (size 4) 
  -> o: lbuffer uint64 (size 4) -> 
  Stack unit
    (requires fun h -> live h o /\ live h temp /\ disjoint o temp)
    (ensures fun h0 _ h1 -> 
      modifies (loc o |+| loc temp) h0 h1 /\
      as_nat h1 o == (uint_v c11 * pow2 (3 * 32) + uint_v c12 * pow2 (4 * 32) + uint_v c13 * pow2 (5 * 32) + uint_v c14 * pow2 (6 * 32) + uint_v c15 * pow2 (7 * 32)) % prime256
    )


let upl_fir_buffer c11 c12 c13 c14 c15 temp o = 
      assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
      assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
      assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
      assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
      assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
  let b0 = u64(0) in 
  let b1 = store_high_low_u c11 (u32 0) in 
  let b2 = store_high_low_u c13 c12 in 
  let b3 = store_high_low_u c15 c14 in 
  load_buffer b0 b1 b2 b3 temp;
  reduction_prime_2prime_impl temp o


val upl_sec_buffer: c12: uint32 -> c13: uint32 -> c14: uint32 -> c15: uint32 
  -> temp: lbuffer uint64 (size 4) 
  -> o: lbuffer uint64 (size 4) -> 
  Stack unit
    (requires fun h -> live h o)
    (ensures fun h0 _ h1 -> 
      modifies (loc o |+| loc temp) h0 h1 /\
      as_nat h1 o == (uint_v c12 * pow2 (3 * 32) + uint_v c13 * pow2 (4 * 32) + uint_v c14 * pow2 (5 * 32) + uint_v c15 * pow2 (6 * 32)) % prime /\ as_nat h1 o < prime
    )

let upl_sec_buffer c12 c13 c14 c15 temp o = 
      assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
      assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
      assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
      assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
      assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
    let b0 = u64 (0) in 
    let b1 = store_high_low_u c12 (u32 0) in 
    let b2 = store_high_low_u c14 c13 in 
    let b3 = store_high_low_u (u32 0) c15 in
    load_buffer b0 b1 b2 b3 o;
    assert_norm(uint_v c12 * pow2 (3 * 32) + uint_v c13 * pow2 (4 * 32) + uint_v c14 * pow2 (5 * 32) + uint_v c15 * pow2 (6 * 32) < prime);
    let h1 = ST.get() in 
    modulo_lemma (as_nat h1 o) prime


val upl_thi_buffer: c8: uint32 -> c9: uint32 -> c10: uint32 -> c14: uint32 -> c15: uint32 
  -> temp: lbuffer uint64 (size 4) 
  -> o: lbuffer uint64 (size 4) -> 
  Stack unit
 (requires fun h -> live h o /\ live h temp /\ disjoint o temp)
 (ensures fun h0 _ h1 -> modifies2 o temp h0 h1 /\
      as_nat h1 o == (uint_v c8 + uint_v c9 * pow2 32 + uint_v c10 * pow2 (2 * 32) +  uint_v c14 * pow2 (6 * 32) + uint_v c15 * pow2 (7 * 32)) % prime256)
	

let upl_thi_buffer c8 c9 c10 c14 c15 temp o = 
   assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
   assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
   assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
   assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
   assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
   let b0 = store_high_low_u c9 c8 in 
   let b1 = store_high_low_u (u32 0) c10 in 
   let b2 = u64 0 in 
   let b3 = store_high_low_u c15 c14 in 
   load_buffer b0 b1 b2 b3 temp;
   reduction_prime_2prime_impl temp o


val upl_for_buffer: c8: uint32 -> c9: uint32 -> c10: uint32 -> c11: uint32 -> c13: uint32 -> 
  c14: uint32 -> c15: uint32 ->
  temp: lbuffer uint64 (size 4)
  -> o: lbuffer uint64 (size 4) -> 
  Stack unit
    (requires fun h -> live h o /\ live h temp /\ disjoint o temp)
    (ensures fun h0 _ h1 -> modifies2 o temp h0 h1 /\
	as_nat h1 o == (uint_v c9 + uint_v c10 * pow2 32 + uint_v c11 * pow2 (2 * 32) + uint_v c13 * pow2 (3 * 32) + uint_v c14 * pow2 (4 * 32) + uint_v c15 * pow2 (5 * 32) + uint_v c13 * pow2 (6 * 32) +  uint_v c8 * pow2 (7 * 32)) % prime256)

let upl_for_buffer c8 c9 c10 c11 c13 c14 c15 temp o = 
  assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
  assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
  assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
  assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
  assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
  let b0 = store_high_low_u c10 c9 in 
  let b1 = store_high_low_u c13 c11 in 
  let b2 = store_high_low_u c15 c14 in 
  let b3 = store_high_low_u c8 c13 in 
  load_buffer b0 b1 b2 b3 temp;
  reduction_prime_2prime_impl temp o


val upl_fif_buffer: c8: uint32 -> c10: uint32 -> c11: uint32 -> c12: uint32 -> c13: uint32 
  -> temp: lbuffer uint64 (size 4) 
  -> o: lbuffer uint64 (size 4) -> 
  Stack unit
    (requires fun h -> live h o /\ live h temp /\ disjoint o temp)
    (ensures fun h0 _ h1 -> modifies2 o temp h0 h1 /\ 
    as_nat h1 o == (uint_v c11 + uint_v c12 * pow2 32 + uint_v c13 * pow2 (2 * 32) + uint_v c8 * pow2 (6 * 32) + uint_v c10 * pow2 (7 * 32)) % prime256)  


let upl_fif_buffer c8 c10 c11 c12 c13 temp o = 
     assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
     assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
     assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
     assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
     assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
    let b0 = store_high_low_u c12 c11 in 
    let b1 = store_high_low_u (u32 0) c13 in 
    let b2 = u64 0 in 
    let b3 = store_high_low_u c10 c8 in 
    load_buffer b0 b1 b2 b3 temp;
    reduction_prime_2prime_impl temp o


val upl_six_buffer: c9: uint32 -> c11: uint32 -> c12: uint32 -> c13: uint32 -> c14: uint32 -> c15: uint32
  -> temp: lbuffer uint64 (size 4) 
  -> o: lbuffer uint64 (size 4) -> 
  Stack unit
    (requires fun h -> live h o /\ live h temp /\ disjoint o temp)
    (ensures fun h0 _ h1 -> modifies2 o temp h0 h1 /\ as_nat h1 o == (
    uint_v c12 + uint_v c13 * pow2 32 + uint_v c14 * pow2 (2 * 32) + uint_v c15 * pow2 (3 * 32) + 
	  uint_v c9 * pow2 (6 * 32) + uint_v c11 * pow2 (7 * 32)) % prime256)  


let upl_six_buffer c9 c11 c12 c13 c14 c15 temp o = 
  assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
  assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
  assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
  assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
  assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
    let b0 = store_high_low_u c13 c12 in 
    let b1 = store_high_low_u c15 c14 in 
    let b2 = u64 0 in 
    let b3 = store_high_low_u c11 c9 in 
    load_buffer b0 b1 b2 b3 temp;
    reduction_prime_2prime_impl temp o


val upl_sev_buffer: c8: uint32 -> c9: uint32 -> c10: uint32 -> c12: uint32 -> c13: uint32 -> 
  c14: uint32 -> c15: uint32 
  -> temp: lbuffer uint64 (size 4) 
  -> o: lbuffer uint64 (size 4) -> 
  Stack unit
    (requires fun h -> live h o /\ live h temp /\ disjoint o temp)
      (ensures fun h0 _ h1 -> modifies2 o temp h0 h1 /\
	as_nat h1 o == (uint_v c13 + uint_v c14 * pow2 32 + uint_v c15 * pow2 (2 * 32) + uint_v c8 * pow2 (3 * 32) +  uint_v c9 * pow2 (4 * 32) + uint_v c10 * pow2 (5 * 32) + uint_v c12 * pow2 (7 * 32)) % prime256) 
  

let upl_sev_buffer c8 c9 c10 c12 c13 c14 c15 temp o = 
  assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
  assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
  assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
  assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
  assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
    let b0 = store_high_low_u c14 c13 in 
    let b1 = store_high_low_u c8 c15 in 
    let b2 = store_high_low_u c10 c9 in 
    let b3 = store_high_low_u c12 (u32 0) in 
    load_buffer b0 b1 b2 b3 temp;
    reduction_prime_2prime_impl temp o


val upl_eig_buffer: c9: uint32 -> c10: uint32 -> c11: uint32 -> c12: uint32 -> c13: uint32 -> 
  c14: uint32 -> c15: uint32 
  -> temp: lbuffer uint64 (size 4) 
  -> o: lbuffer uint64 (size 4) -> 
  Stack unit
    (requires fun h -> live h o /\ live h temp /\ disjoint o temp)
    (ensures fun h0 _ h1 -> modifies2 o temp h0 h1 /\ as_nat h1 o == (uint_v c14 + uint_v c15 * pow2 32 + uint_v c9 * pow2 (3 * 32) + uint_v c10 * pow2 (4 * 32) + uint_v c11 * pow2 (5 * 32) + uint_v c13 * pow2 (7 * 32)) % prime256) 
  

let upl_eig_buffer c9 c10 c11 c12 c13 c14 c15 temp o = 
  assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
  assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
  assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
  assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
  assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
    let b0 = store_high_low_u c15 c14 in 
    let b1 = store_high_low_u c9 (u32 0) in 
    let b2 = store_high_low_u c11 c10 in 
    let b3 = store_high_low_u c13 (u32 0) in 
    load_buffer b0 b1 b2 b3 temp;
    reduction_prime_2prime_impl temp o


inline_for_extraction noextract
val solinas_reduction_upload0: c0: uint32 -> c1: uint32 -> c2: uint32 -> c3: uint32 -> c4: uint32 -> c5: uint32 -> 
  c6: uint32 -> c7: uint32 -> c8: uint32 -> c9: uint32 -> c10: uint32 -> c11: uint32 -> c12: uint32 -> c13: uint32 -> 
  c14: uint32 -> c15: uint32 -> tempBuffer: lbuffer uint64 (size 36) -> redBuffer: felem ->
    Stack unit 
      (fun h -> live h tempBuffer /\ live h redBuffer /\ disjoint redBuffer tempBuffer)
      (fun h0 _ h1 -> modifies2 tempBuffer redBuffer h0 h1 /\
	(
	  let t0 = felem_seq_as_nat (as_seq h1 (gsub tempBuffer (size 0) (size 4))) in 
	  let t1 = felem_seq_as_nat (as_seq h1 (gsub tempBuffer (size 4) (size 4))) in 
	  let t2 = felem_seq_as_nat (as_seq h1 (gsub tempBuffer (size 8) (size 4))) in 
	  let t3 = felem_seq_as_nat (as_seq h1 (gsub tempBuffer (size 12) (size 4))) in 
	  let t4 = felem_seq_as_nat (as_seq h1 (gsub tempBuffer (size 16) (size 4))) in 
	  let t5 = felem_seq_as_nat (as_seq h1 (gsub tempBuffer (size 20) (size 4))) in 
 	  t0 == (uint_v c0 + uint_v c1 * pow2 (1 * 32) + uint_v c2 * pow2 (2 * 32) + uint_v c3 * pow2 (3 * 32) + uint_v c4 * pow2 (4 * 32) + uint_v c5 * pow2 (5 * 32) + uint_v  c6 * pow2 (6 * 32) +  uint_v c7 * pow2 (7 * 32)) % prime /\
	  t1 == (uint_v c11 * pow2 (3 * 32) + uint_v c12 * pow2 (4 * 32) + uint_v c13 * pow2 (5 * 32) + 
	   uint_v c14 * pow2 (6 * 32) + uint_v c15 * pow2 (7 * 32)) % prime /\
	  t2 == (uint_v c12 * pow2 (3 * 32) + uint_v c13 * pow2 (4 * 32) +  uint_v c14 * pow2 (5 * 32) + uint_v c15 * pow2 (6 * 32)) % prime  /\
	  t3 == (uint_v c8 + uint_v c9 * pow2 32 + uint_v c10 * pow2 (2 * 32) + uint_v c14 * pow2 (6 * 32) + uint_v c15 * pow2 (7 * 32)) % prime /\
	  t4 == (uint_v c9 + uint_v c10 * pow2 32 + uint_v c11 * pow2 (2 * 32) + uint_v c13 * pow2 (3 * 32) + uint_v c14 * pow2 (4 * 32) + uint_v c15 * pow2 (5 * 32) + uint_v c13 * pow2 (6 * 32) + uint_v c8 * pow2 (7 * 32)) % prime /\
	  t5 == (uint_v c11 + uint_v c12 * pow2 32 + uint_v c13 * pow2 (2 * 32) + uint_v c8 * pow2 (6 * 32) + uint_v c10 * pow2 (7 * 32)) % prime))

let solinas_reduction_upload0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 tempBuffer redBuffer = 
    let t0 = sub tempBuffer (size 0) (size 4) in
    let t1 = sub tempBuffer (size 4) (size 4) in 
    let t2 = sub tempBuffer (size 8) (size 4) in 
    let t3 = sub tempBuffer (size 12) (size 4) in 
    let t4 = sub tempBuffer (size 16) (size 4) in 
    let t5 = sub tempBuffer (size 20) (size 4) in 
  upl_zer_buffer c0 c1 c2 c3 c4 c5 c6 c7 redBuffer t0; 
  upl_fir_buffer c11 c12 c13 c14 c15 redBuffer t1;
  upl_sec_buffer c12 c13 c14 c15 redBuffer t2; 
  upl_thi_buffer c8 c9 c10 c14 c15 redBuffer  t3;
  upl_for_buffer c8 c9 c10 c11 c13 c14 c15 redBuffer t4;
  upl_fif_buffer c8 c10 c11 c12 c13 redBuffer  t5


inline_for_extraction noextract
val solinas_reduction_upload: c0: uint32 -> c1: uint32 -> c2: uint32 -> c3: uint32 -> c4: uint32 -> c5: uint32 -> 
  c6: uint32 -> c7: uint32 -> c8: uint32 -> c9: uint32 -> c10: uint32 -> c11: uint32 -> c12: uint32 -> c13: uint32 -> 
  c14: uint32 -> c15: uint32 -> tempBuffer: lbuffer uint64 (size 36) -> 
  Stack unit
    (requires fun h -> live h tempBuffer)
    (ensures fun h0 _ h1 -> modifies1 tempBuffer h0 h1 /\ 
	(
	  let t0 = felem_seq_as_nat (as_seq h1 (gsub tempBuffer (size 0) (size 4))) in 
	  let t1 = felem_seq_as_nat (as_seq h1 (gsub tempBuffer (size 4) (size 4))) in 
	  let t2 = felem_seq_as_nat (as_seq h1 (gsub tempBuffer (size 8) (size 4))) in 
	  let t3 = felem_seq_as_nat (as_seq h1 (gsub tempBuffer (size 12) (size 4))) in 
	  let t4 = felem_seq_as_nat (as_seq h1 (gsub tempBuffer (size 16) (size 4))) in 
	  let t5 = felem_seq_as_nat (as_seq h1 (gsub tempBuffer (size 20) (size 4))) in 
	  let t6 = felem_seq_as_nat (as_seq h1 (gsub tempBuffer (size 24) (size 4))) in 
	  let t7 = felem_seq_as_nat (as_seq h1 (gsub tempBuffer (size 28) (size 4))) in 
	  let t8 = felem_seq_as_nat (as_seq h1 (gsub tempBuffer (size 32) (size 4))) in 
 	  t0 == (uint_v c0 + uint_v c1 * pow2 (1 * 32) + uint_v c2 * pow2 (2 * 32) + uint_v c3 * pow2 (3 * 32) + uint_v c4 * pow2 (4 * 32) + uint_v c5 * pow2 (5 * 32) + uint_v  c6 * pow2 (6 * 32) +  uint_v c7 * pow2 (7 * 32)) % prime /\
	  t1 == (uint_v c11 * pow2 (3 * 32) + uint_v c12 * pow2 (4 * 32) + uint_v c13 * pow2 (5 * 32) + 
	   uint_v c14 * pow2 (6 * 32) + uint_v c15 * pow2 (7 * 32)) % prime /\
	  t2 == (uint_v c12 * pow2 (3 * 32) + uint_v c13 * pow2 (4 * 32) +  uint_v c14 * pow2 (5 * 32) + uint_v c15 * pow2 (6 * 32)) % prime  /\
	  t3 == (uint_v c8 + uint_v c9 * pow2 32 + uint_v c10 * pow2 (2 * 32) + uint_v c14 * pow2 (6 * 32) + uint_v c15 * pow2 (7 * 32)) % prime /\
	  t4 == (uint_v c9 + uint_v c10 * pow2 32 + uint_v c11 * pow2 (2 * 32) + uint_v c13 * pow2 (3 * 32) + uint_v c14 * pow2 (4 * 32) + uint_v c15 * pow2 (5 * 32) + uint_v c13 * pow2 (6 * 32) + uint_v c8 * pow2 (7 * 32)) % prime /\
	  t5 == (uint_v c11 + uint_v c12 * pow2 32 + uint_v c13 * pow2 (2 * 32) + uint_v c8 * pow2 (6 * 32) + uint_v c10 * pow2 (7 * 32)) % prime /\
	  t6 == (uint_v c12 + uint_v c13 * pow2 32 + uint_v c14 * pow2 (2 * 32) + uint_v c15 * pow2 (3 * 32) + uint_v c9 * pow2 (6 * 32) + uint_v c11 * pow2 (7 * 32)) % prime /\
	  t7 == (uint_v c13 + uint_v c14 * pow2 32 + uint_v c15 * pow2 (2 * 32) +  uint_v c8 * pow2 (3 * 32) +  uint_v c9 * pow2 (4 * 32) + uint_v c10 * pow2 (5 * 32) + uint_v c12 * pow2 (7 * 32)) % prime /\
	  t8 == (uint_v c14 + uint_v c15 * pow2 32 + uint_v c9 * pow2 (3 * 32) +  uint_v c10 * pow2 (4 * 32) + uint_v c11 * pow2 (5 * 32) + uint_v c13 * pow2 (7 * 32)) % prime
    ))


let solinas_reduction_upload c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 tempBuffer  =  
  push_frame();
    let redBuffer = create (size 4) (u64 0) in 
    let t6 = sub tempBuffer (size 24) (size 4) in 
    let t7 = sub tempBuffer (size 28) (size 4) in 
    let t8 = sub tempBuffer (size 32) (size 4) in   
    
    let h0 = ST.get() in 
    solinas_reduction_upload0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 tempBuffer redBuffer;
    upl_six_buffer c9 c11 c12 c13 c14 c15 redBuffer  t6;
    upl_sev_buffer c8 c9 c10 c12 c13 c14 c15 redBuffer t7;
    upl_eig_buffer c9 c10 c11 c12 c13 c14 c15 redBuffer t8;
  pop_frame()


inline_for_extraction noextract
val solinas_reduction_operations: tempBuffer: lbuffer uint64 (size 36) ->  o: lbuffer uint64 (size 4) -> 
  Stack unit
    (requires fun h -> live h o /\ live h tempBuffer /\ disjoint tempBuffer o /\
      (
      	  let t0 = felem_seq_as_nat (as_seq h (gsub tempBuffer (size 0) (size 4))) in 
	  let t1 = felem_seq_as_nat (as_seq h (gsub tempBuffer (size 4) (size 4))) in 
	  let t2 = felem_seq_as_nat (as_seq h (gsub tempBuffer (size 8) (size 4))) in 
	  let t3 = felem_seq_as_nat (as_seq h (gsub tempBuffer (size 12) (size 4))) in 
	  let t4 = felem_seq_as_nat (as_seq h (gsub tempBuffer (size 16) (size 4))) in 
	  let t5 = felem_seq_as_nat (as_seq h (gsub tempBuffer (size 20) (size 4))) in 
	  let t6 = felem_seq_as_nat (as_seq h (gsub tempBuffer (size 24) (size 4))) in 
	  let t7 = felem_seq_as_nat (as_seq h (gsub tempBuffer (size 28) (size 4))) in 
	  let t8 = felem_seq_as_nat (as_seq h (gsub tempBuffer (size 32) (size 4))) in 
	  t0 < prime /\ t1 < prime /\ t2 < prime /\ t3 < prime /\ t4 < prime /\
	  t5 < prime /\ t6 < prime /\ t7 < prime /\ t8 < prime
      )
    )
    (ensures fun h0 _ h1 -> modifies2 tempBuffer o h0 h1 /\ 
       (
      	  let t0 = felem_seq_as_nat (as_seq h0 (gsub tempBuffer (size 0) (size 4))) in 
	  let t1 = felem_seq_as_nat (as_seq h0 (gsub tempBuffer (size 4) (size 4))) in 
	  let t2 = felem_seq_as_nat (as_seq h0 (gsub tempBuffer (size 8) (size 4))) in 
	  let t3 = felem_seq_as_nat (as_seq h0 (gsub tempBuffer (size 12) (size 4))) in 
	  let t4 = felem_seq_as_nat (as_seq h0 (gsub tempBuffer (size 16) (size 4))) in 
	  let t5 = felem_seq_as_nat (as_seq h0 (gsub tempBuffer (size 20) (size 4))) in 
	  let t6 = felem_seq_as_nat (as_seq h0 (gsub tempBuffer (size 24) (size 4))) in 
	  let t7 = felem_seq_as_nat (as_seq h0 (gsub tempBuffer (size 28) (size 4))) in 
	  let t8 = felem_seq_as_nat (as_seq h0 (gsub tempBuffer (size 32) (size 4))) in 
	  felem_seq_as_nat (as_seq h1 o) == ((t0 + 2 * t1 + 2 * t2  + t3 + t4 - t5  - t6 - t7 - t8) % prime
       )
    )
    )


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

    assert(LowStar.Monotonic.Buffer.all_disjoint [loc t0; loc t1; loc t2; loc t3; loc t4; loc t5; loc t6; loc t7; loc t8; loc o]);

    p256_double t2 t2;  
    p256_double t1 t1;
    p256_add t0 t1 o; 
    p256_add t2 o o;
    p256_add t3 o o;
    p256_add t4 o o; 
    p256_sub o t5 o;
    p256_sub o t6 o;
    p256_sub o t7 o;
    p256_sub o t8 o;

    reduce_brackets 
      (felem_seq_as_nat (as_seq h0 t0)) 
      (felem_seq_as_nat (as_seq h0 t1)) 
      (felem_seq_as_nat (as_seq h0 t2))
      (felem_seq_as_nat (as_seq h0 t3)) 
      (felem_seq_as_nat (as_seq h0 t4))
      (felem_seq_as_nat (as_seq h0 t5)) 
      (felem_seq_as_nat (as_seq h0 t6)) 
      (felem_seq_as_nat (as_seq h0 t7)) 
      (felem_seq_as_nat (as_seq h0 t8))

val lemma_opened: i: Lib.Sequence.lseq uint64 8 -> Lemma
  ( 
    let open Lib.Sequence in 

     let i0 = index i 0 in let i1 = index i 1 in let i2 = index i 2 in let i3 = index i 3 in 
     let i4 = index i 4 in let i5 = index i 5 in let i6 = index i 6 in let i7 = index i 7 in 
  
     let c0 = get_low_part i0 in let c1 = get_high_part i0 in let c2 = get_low_part i1 in 
     let c3 = get_high_part i1 in  let c4 = get_low_part i2 in let c5 = get_high_part i2 in   
     let c6 = get_low_part i3 in let c7 = get_high_part i3 in  let c8 = get_low_part i4 in 
     let c9 = get_high_part i4 in let c10 = get_low_part i5 in let c11 = get_high_part i5 in   
     let c12 = get_low_part i6 in let c13 = get_high_part i6 in  let c14 = get_low_part i7 in 
     let c15 = get_high_part i7 in

    felem_seq_as_nat_8 i =  uint_v c0 + uint_v c1 * pow2 32 + uint_v c2 * pow2 (2 * 32) + uint_v c3 * pow2 (3 * 32) + uint_v c4 * pow2 (4 * 32) + 
    uint_v c5 * pow2 (5 * 32) + uint_v c6 * pow2 (6 * 32) + uint_v c7 * pow2 (7 * 32) + uint_v c8 * pow2 (8 * 32) + 
    uint_v c9 * pow2 (9 * 32) + uint_v c10 * pow2 (10 * 32) +  uint_v c11 * pow2 (11 * 32) + uint_v c12 * pow2 (12 * 32) + 
    uint_v c13 * pow2 (13 * 32) + uint_v c14 * pow2 (14 * 32) + uint_v c15 * pow2 (15 * 32)
    )


#reset-options " --z3rlimit 300 --z3refresh"

let lemma_opened i = 
     let open Lib.Sequence in 

    assert_norm (pow2 64 * pow2 64 = pow2 (2 * 64));
    assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 (3 * 64));
    assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (4 * 64));
    assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (5 * 64));
    assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64  = pow2 (6 * 64));
    assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (7 * 64));


     let i0 = index i 0 in let i1 = index i 1 in let i2 = index i 2 in let i3 = index i 3 in 
     let i4 = index i 4 in let i5 = index i 5 in let i6 = index i 6 in let i7 = index i 7 in 

     assert(felem_seq_as_nat_8 i = uint_v i0 + uint_v i1 * pow2 64 + uint_v i2 * pow2 (2 * 64) + uint_v i3 * pow2 (3 * 64) + 
       uint_v i4 * pow2 (4 * 64) + uint_v i5 * pow2 (5 * 64) + uint_v i6 * pow2 (6 * 64) + uint_v i7 * pow2 (7 * 64));
  
     let c0 = get_low_part i0 in let c1 = get_high_part i0 in let c2 = get_low_part i1 in 
     let c3 = get_high_part i1 in  let c4 = get_low_part i2 in let c5 = get_high_part i2 in   
     let c6 = get_low_part i3 in let c7 = get_high_part i3 in  let c8 = get_low_part i4 in 
     let c9 = get_high_part i4 in let c10 = get_low_part i5 in let c11 = get_high_part i5 in   
     let c12 = get_low_part i6 in let c13 = get_high_part i6 in  let c14 = get_low_part i7 in 
     let c15 = get_high_part i7 in

     assert(uint_v c0 + uint_v c1 * pow2 32 == uint_v i0);
     assert(uint_v c2 + uint_v c3 * pow2 32 == uint_v i1);
     assert(uint_v c4 + uint_v c5 * pow2 32 == uint_v i2);
     assert(uint_v c6 + uint_v c7 * pow2 32 == uint_v i3);
     assert(uint_v c8 + uint_v c9 * pow2 32 == uint_v i4);
     assert(uint_v c10 + uint_v c11 * pow2 32 == uint_v i5);
     assert(uint_v c12 + uint_v c13 * pow2 32 == uint_v i6);
     assert(uint_v c14 + uint_v c15 * pow2 32 == uint_v i7);

        assert_norm (pow2 (1 * 32) * pow2 64 = pow2 (3 * 32));
  assert_norm (pow2 (2 * 32) * pow2 64 = pow2 (4 * 32));
  assert_norm (pow2 (3 * 32) * pow2 64 = pow2 (5 * 32));
  assert_norm (pow2 (4 * 32) * pow2 64 = pow2 (6 * 32));
  assert_norm (pow2 (5 * 32) * pow2 64 = pow2 (7 * 32));
  assert_norm (pow2 (6 * 32) * pow2 64 = pow2 (8 * 32));
  assert_norm (pow2 (7 * 32) * pow2 64 = pow2 (9 * 32));
  assert_norm (pow2 (8 * 32) * pow2 64 = pow2 (10 * 32));
  assert_norm (pow2 (9 * 32) * pow2 64 = pow2 (11 * 32));
  assert_norm (pow2 (10 * 32) * pow2 64 = pow2 (12 * 32));
  assert_norm (pow2 (11 * 32) * pow2 64 = pow2 (13 * 32));

  assert_norm (pow2 (12 * 32) * pow2 64 = pow2 (14 * 32));
  assert_norm (pow2 (13 * 32) * pow2 64 = pow2 (15 * 32));

  assert(felem_seq_as_nat_8 i =  uint_v c0 + uint_v c1 * pow2 32 + uint_v c2 * pow2 (2 * 32) + uint_v c3 * pow2 (3 * 32) + uint_v c4 * pow2 (4 * 32) + 
    uint_v c5 * pow2 (5 * 32) + uint_v c6 * pow2 (6 * 32) + uint_v c7 * pow2 (7 * 32) + uint_v c8 * pow2 (8 * 32) + 
    uint_v c9 * pow2 (9 * 32) + uint_v c10 * pow2 (10 * 32) +  uint_v c11 * pow2 (11 * 32) + uint_v c12 * pow2 (12 * 32) + 
    uint_v c13 * pow2 (13 * 32) + uint_v c14 * pow2 (14 * 32) + uint_v c15 * pow2 (15 * 32))

let solinas_reduction_impl i o = 
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
  
      let h0 = ST.get() in 
    solinas_reduction_upload c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 tempBuffer;
      let h1 = ST.get() in 
    solinas_reduction_operations tempBuffer o;
    let h2 = ST.get() in 

    solinas_reduction_mod 
      (uint_v c0) (uint_v c1) (uint_v c2) (uint_v c3) (uint_v c4) (uint_v c5) (uint_v c6) (uint_v c7) (uint_v c8) (uint_v c9)   (uint_v c10) (uint_v c11) (uint_v c12) (uint_v c13) (uint_v c14) (uint_v c15)
      (felem_seq_as_nat (as_seq h1 t0)) 
      (felem_seq_as_nat (as_seq h1 t1)) 
      (felem_seq_as_nat (as_seq h1 t2)) 
      (felem_seq_as_nat (as_seq h1 t3))  
      (felem_seq_as_nat (as_seq h1 t4)) 
      (felem_seq_as_nat (as_seq h1 t5)) 
      (felem_seq_as_nat (as_seq h1 t6)) 
      (felem_seq_as_nat (as_seq h1 t7)) 
      (felem_seq_as_nat (as_seq h1 t8)) 
      (felem_seq_as_nat (as_seq h2 o));


  modulo_lemma (felem_seq_as_nat(as_seq h2 o)) prime;
  assert(felem_seq_as_nat_8 (as_seq h0 i) % prime == felem_seq_as_nat (as_seq h2 o));
    pop_frame() 

  
