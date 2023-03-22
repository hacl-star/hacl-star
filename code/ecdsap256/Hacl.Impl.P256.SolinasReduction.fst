module Hacl.Impl.P256.SolinasReduction

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.Bignum
open Hacl.Impl.P256.Field

module S = Spec.P256
module SB = Hacl.Spec.P256.Bignum
module SL = Hacl.Spec.P256.SolinasReduction.Lemmas

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val get_high_part: a:uint64 -> r:uint32{uint_v r == uint_v a / pow2 32}
let get_high_part a = to_u32 (shift_right a (size 32))

inline_for_extraction noextract
val get_low_part: a:uint64 -> r:uint32{uint_v r == uint_v a % pow2 32}
let get_low_part a = to_u32 a


val lemma_logor_zero:
    low:uint64{v (get_high_part low) == 0}
  -> high:uint64{v (get_low_part high) == 0} ->
  Lemma (v (logor low high) = v high + v low)

let lemma_logor_zero l h =
  assert (v l / pow2 32 = 0);
  Math.Lemmas.small_division_lemma_2 (v l) (pow2 32);
  assert (v l < pow2 32);
  assert (v h % pow2 32 = 0);
  logor_disjoint l h 32;
  assert (v (l `logor` h) == v l + v h)


inline_for_extraction noextract
val store_high_low_u: high:uint32 -> low:uint32 -> r:uint64{v r = v high * pow2 32 + v low}
let store_high_low_u high low =
  [@inline_let] let as_uint64_high = Lib.IntTypes.shift_left (to_u64 high) (size 32) in
  [@inline_let] let as_uint64_low = to_u64 low in
  assert (v as_uint64_high = v high * pow2 32);
  assert (v as_uint64_low = v low);
  lemma_logor_zero as_uint64_low as_uint64_high;
  logor as_uint64_low as_uint64_high

#push-options "--z3rlimit 100"

inline_for_extraction noextract
val upl_zer_buffer:
    c0: uint32 -> c1: uint32 -> c2: uint32 -> c3: uint32
  -> c4: uint32 -> c5: uint32 -> c6: uint32 -> c7: uint32
  -> o: lbuffer uint64 (size 4) ->
  Stack unit
    (requires fun h -> live h o)
    (ensures fun h0 _ h1 ->
      modifies (loc o) h0 h1 /\
      as_nat h1 o == (v c0 + v c1 * pow2 (1 * 32) + v c2 * pow2 (2 * 32) + v c3 * pow2 (3 * 32) + v c4 * pow2 (4 * 32) + v c5 * pow2 (5 * 32) + v  c6 * pow2 (6 * 32) + v c7 * pow2 (7 * 32)) % S.prime
   )

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

    assert(v b0 = v c1 * pow2 32 + v c0);
    assert(v b1 = v c3 * pow2 32 + v c2);
    assert(v b2 = v c5 * pow2 32 + v c4);
    assert(v b3 = v c7 * pow2 32 + v c6);

    bn_make_u64_4 o b0 b1 b2 b3;
    fmod_short o o;
    let h2 = ST.get() in
    assert(as_nat h2 o = (v c1 * pow2 32 + v c0 + v c3 * pow2 (3 * 32) + v c2 * pow2 (2 * 32) + v c5 * pow2 (32 * 5) + v c4 * pow2 (32 * 4) + v c7 * pow2 (32 * 7) + v c6 * pow2 (32 * 6)) % S.prime)

inline_for_extraction noextract
val upl_fir_buffer: c11: uint32 -> c12: uint32 -> c13: uint32 -> c14: uint32 -> c15: uint32
  -> o: lbuffer uint64 (size 4) ->
  Stack unit
    (requires fun h -> live h o)
    (ensures fun h0 _ h1 ->
      modifies (loc o) h0 h1 /\
      as_nat h1 o == (v c11 * pow2 (3 * 32) + v c12 * pow2 (4 * 32) + v c13 * pow2 (5 * 32) + v c14 * pow2 (6 * 32) + v c15 * pow2 (7 * 32)) % S.prime
    )

let upl_fir_buffer c11 c12 c13 c14 c15 o =
      assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
      assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
      assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
      assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
      assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
  let b0 = u64(0) in
  let b1 = store_high_low_u c11 (u32 0) in
  let b2 = store_high_low_u c13 c12 in
  let b3 = store_high_low_u c15 c14 in
  bn_make_u64_4 o b0 b1 b2 b3;
  fmod_short o o

inline_for_extraction noextract
val upl_sec_buffer: c12: uint32 -> c13: uint32 -> c14: uint32 -> c15: uint32
  -> o: lbuffer uint64 (size 4) ->
  Stack unit
    (requires fun h -> live h o)
    (ensures fun h0 _ h1 ->
      modifies (loc o) h0 h1 /\
      as_nat h1 o == (v c12 * pow2 (3 * 32) + v c13 * pow2 (4 * 32) + v c14 * pow2 (5 * 32) + v c15 * pow2 (6 * 32)) % S.prime /\ as_nat h1 o < S.prime
    )

let upl_sec_buffer c12 c13 c14 c15 o =
      assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
      assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
      assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
      assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
      assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
    let b0 = u64 (0) in
    let b1 = store_high_low_u c12 (u32 0) in
    let b2 = store_high_low_u c14 c13 in
    let b3 = store_high_low_u (u32 0) c15 in
    bn_make_u64_4 o b0 b1 b2 b3;
    assert_norm(v c12 * pow2 (3 * 32) + v c13 * pow2 (4 * 32) + v c14 * pow2 (5 * 32) + v c15 * pow2 (6 * 32) < S.prime);
    let h1 = ST.get() in
    FStar.Math.Lemmas.modulo_lemma (as_nat h1 o) S.prime

inline_for_extraction noextract
val upl_thi_buffer: c8: uint32 -> c9: uint32 -> c10: uint32 -> c14: uint32 -> c15: uint32
  -> o: lbuffer uint64 (size 4) ->
  Stack unit
 (requires fun h -> live h o)
 (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\
      as_nat h1 o == (v c8 + v c9 * pow2 32 + v c10 * pow2 (2 * 32) +  v c14 * pow2 (6 * 32) + v c15 * pow2 (7 * 32)) % S.prime)

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
   bn_make_u64_4 o b0 b1 b2 b3;
   fmod_short o o


inline_for_extraction noextract
val upl_for_buffer: c8: uint32 -> c9: uint32 -> c10: uint32 -> c11: uint32 -> c13: uint32 ->
  c14: uint32 -> c15: uint32-> o: lbuffer uint64 (size 4) ->
  Stack unit
  (requires fun h -> live h o)
  (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\
    as_nat h1 o == (v c9 + v c10 * pow2 32 + v c11 * pow2 (2 * 32) + v c13 * pow2 (3 * 32) + v c14 * pow2 (4 * 32) + v c15 * pow2 (5 * 32) + v c13 * pow2 (6 * 32) +  v c8 * pow2 (7 * 32)) % S.prime)

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
  bn_make_u64_4 o b0 b1 b2 b3;
  fmod_short o o

inline_for_extraction noextract
val upl_fif_buffer: c8: uint32 -> c10: uint32 -> c11: uint32 -> c12: uint32 -> c13: uint32
  -> o: lbuffer uint64 (size 4) ->
  Stack unit
    (requires fun h -> live h o)
    (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\
    as_nat h1 o == (v c11 + v c12 * pow2 32 + v c13 * pow2 (2 * 32) + v c8 * pow2 (6 * 32) + v c10 * pow2 (7 * 32)) % S.prime)

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
    bn_make_u64_4 o b0 b1 b2 b3;
    fmod_short o o

inline_for_extraction noextract
val upl_six_buffer: c9: uint32 -> c11: uint32 -> c12: uint32 -> c13: uint32 -> c14: uint32 -> c15: uint32->
  o: lbuffer uint64 (size 4) ->
  Stack unit
    (requires fun h -> live h o)
    (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\ as_nat h1 o == (
    v c12 + v c13 * pow2 32 + v c14 * pow2 (2 * 32) + v c15 * pow2 (3 * 32) +
          v c9 * pow2 (6 * 32) + v c11 * pow2 (7 * 32)) % S.prime)

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
    bn_make_u64_4 o b0 b1 b2 b3;
    fmod_short o o

inline_for_extraction noextract
val upl_sev_buffer: c8: uint32 -> c9: uint32 -> c10: uint32 -> c12: uint32 -> c13: uint32 ->
  c14: uint32 -> c15: uint32
  -> o: lbuffer uint64 (size 4) ->
  Stack unit
    (requires fun h -> live h o)
      (ensures fun h0 _ h1 -> modifies (loc o)  h0 h1 /\
        as_nat h1 o == (v c13 + v c14 * pow2 32 + v c15 * pow2 (2 * 32) + v c8 * pow2 (3 * 32) +  v c9 * pow2 (4 * 32) + v c10 * pow2 (5 * 32) + v c12 * pow2 (7 * 32)) % S.prime)

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
    bn_make_u64_4 o b0 b1 b2 b3;
    fmod_short o o

inline_for_extraction noextract
val upl_eig_buffer: c9: uint32 -> c10: uint32 -> c11: uint32 -> c12: uint32 -> c13: uint32 ->
  c14: uint32 -> c15: uint32
  -> o: lbuffer uint64 (size 4) ->
  Stack unit
    (requires fun h -> live h o)
    (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\ as_nat h1 o == (v c14 + v c15 * pow2 32 + v c9 * pow2 (3 * 32) + v c10 * pow2 (4 * 32) + v c11 * pow2 (5 * 32) + v c13 * pow2 (7 * 32)) % S.prime)

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
    bn_make_u64_4 o b0 b1 b2 b3;
    fmod_short o o


inline_for_extraction noextract
val solinas_reduction_upload: c0: uint32 -> c1: uint32 -> c2: uint32 -> c3: uint32 -> c4: uint32 -> c5: uint32 -> c6: uint32 -> c7: uint32 -> c8: uint32 -> c9: uint32 -> c10: uint32 -> c11: uint32 -> c12: uint32 -> c13: uint32 -> c14: uint32 -> c15: uint32 -> tempBuffer: lbuffer uint64 (size 36) ->
  Stack unit
    (requires fun h -> live h tempBuffer)
    (ensures fun h0 _ h1 -> modifies1 tempBuffer h0 h1 /\
        (
          let t0 = as_nat h1 (gsub tempBuffer (size 0) (size 4)) in
          let t1 = as_nat h1 (gsub tempBuffer (size 4) (size 4)) in
          let t2 = as_nat h1 (gsub tempBuffer (size 8) (size 4)) in
          let t3 = as_nat h1 (gsub tempBuffer (size 12) (size 4)) in
          let t4 = as_nat h1 (gsub tempBuffer (size 16) (size 4)) in
          let t5 = as_nat h1 (gsub tempBuffer (size 20) (size 4)) in
          let t6 = as_nat h1 (gsub tempBuffer (size 24) (size 4)) in
          let t7 = as_nat h1 (gsub tempBuffer (size 28) (size 4)) in
          let t8 = as_nat h1 (gsub tempBuffer (size 32) (size 4)) in
          t0 == (v c0 + v c1 * pow2 (1 * 32) + v c2 * pow2 (2 * 32) + v c3 * pow2 (3 * 32) + v c4 * pow2 (4 * 32) + v c5 * pow2 (5 * 32) + v  c6 * pow2 (6 * 32) +  v c7 * pow2 (7 * 32)) % S.prime /\
          t1 == (v c11 * pow2 (3 * 32) + v c12 * pow2 (4 * 32) + v c13 * pow2 (5 * 32) +
           v c14 * pow2 (6 * 32) + v c15 * pow2 (7 * 32)) % S.prime /\
          t2 == (v c12 * pow2 (3 * 32) + v c13 * pow2 (4 * 32) +  v c14 * pow2 (5 * 32) + v c15 * pow2 (6 * 32)) % S.prime  /\
          t3 == (v c8 + v c9 * pow2 32 + v c10 * pow2 (2 * 32) + v c14 * pow2 (6 * 32) + v c15 * pow2 (7 * 32)) % S.prime /\
          t4 == (v c9 + v c10 * pow2 32 + v c11 * pow2 (2 * 32) + v c13 * pow2 (3 * 32) + v c14 * pow2 (4 * 32) + v c15 * pow2 (5 * 32) + v c13 * pow2 (6 * 32) + v c8 * pow2 (7 * 32)) % S.prime /\
          t5 == (v c11 + v c12 * pow2 32 + v c13 * pow2 (2 * 32) + v c8 * pow2 (6 * 32) + v c10 * pow2 (7 * 32)) % S.prime /\
          t6 == (v c12 + v c13 * pow2 32 + v c14 * pow2 (2 * 32) + v c15 * pow2 (3 * 32) + v c9 * pow2 (6 * 32) + v c11 * pow2 (7 * 32)) % S.prime /\
          t7 == (v c13 + v c14 * pow2 32 + v c15 * pow2 (2 * 32) +  v c8 * pow2 (3 * 32) +  v c9 * pow2 (4 * 32) + v c10 * pow2 (5 * 32) + v c12 * pow2 (7 * 32)) % S.prime /\
          t8 == (v c14 + v c15 * pow2 32 + v c9 * pow2 (3 * 32) +  v c10 * pow2 (4 * 32) + v c11 * pow2 (5 * 32) + v c13 * pow2 (7 * 32)) % S.prime
    ))


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
val solinas_reduction_operations: tempBuffer: lbuffer uint64 (size 36) ->  o: lbuffer uint64 (size 4) ->
  Stack unit
    (requires fun h -> live h o /\ live h tempBuffer /\ disjoint tempBuffer o /\
      (
          let t0 = as_nat h (gsub tempBuffer (size 0) (size 4)) in
          let t1 = as_nat h (gsub tempBuffer (size 4) (size 4)) in
          let t2 = as_nat h (gsub tempBuffer (size 8) (size 4)) in
          let t3 = as_nat h (gsub tempBuffer (size 12) (size 4)) in
          let t4 = as_nat h (gsub tempBuffer (size 16) (size 4)) in
          let t5 = as_nat h (gsub tempBuffer (size 20) (size 4)) in
          let t6 = as_nat h (gsub tempBuffer (size 24) (size 4)) in
          let t7 = as_nat h (gsub tempBuffer (size 28) (size 4)) in
          let t8 = as_nat h (gsub tempBuffer (size 32) (size 4)) in
          t0 < S.prime /\ t1 < S.prime /\ t2 < S.prime /\ t3 < S.prime /\ t4 < S.prime /\
          t5 < S.prime /\ t6 < S.prime /\ t7 < S.prime /\ t8 < S.prime
      )
    )
    (ensures fun h0 _ h1 -> modifies2 tempBuffer o h0 h1 /\
       (
          let t0 = as_nat h0 (gsub tempBuffer (size 0) (size 4)) in
          let t1 = as_nat h0 (gsub tempBuffer (size 4) (size 4)) in
          let t2 = as_nat h0 (gsub tempBuffer (size 8) (size 4)) in
          let t3 = as_nat h0 (gsub tempBuffer (size 12) (size 4)) in
          let t4 = as_nat h0 (gsub tempBuffer (size 16) (size 4)) in
          let t5 = as_nat h0 (gsub tempBuffer (size 20) (size 4)) in
          let t6 = as_nat h0 (gsub tempBuffer (size 24) (size 4)) in
          let t7 = as_nat h0 (gsub tempBuffer (size 28) (size 4)) in
          let t8 = as_nat h0 (gsub tempBuffer (size 32) (size 4)) in
          as_nat h1 o == (t0 + 2 * t1 + 2 * t2  + t3 + t4 - t5  - t6 - t7 - t8) % S.prime
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

    fdouble t2 t2;
    fdouble t1 t1;
    fadd o t0 t1;
    fadd o t2 o;
    fadd o t3 o;
    fadd o t4 o;
    fsub o o t5;
    fsub o o t6;
    fsub o o t7;
    fsub o o t8;

    SL.reduce_brackets (as_nat h0 t0) (as_nat h0 t1) (as_nat h0 t2) (as_nat h0 t3) (as_nat h0 t4) (as_nat h0 t5) (as_nat h0 t6) (as_nat h0 t7) (as_nat h0 t8)


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

   SB.widefelem_seq_as_nat i =
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

#push-options "--z3rlimit 400"

let lemma_opened i =
  let open FStar.Math.Lemmas in
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
    SB.widefelem_seq_as_nat i;
    == { }
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
    solinas_reduction_upload c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 tempBuffer;
    let h1 = ST.get() in
    solinas_reduction_operations tempBuffer o;
    let h2 = ST.get() in

    SL.solinas_reduction_mod (v c0) (v c1) (v c2) (v c3) (v c4) (v c5) (v c6) (v c7) (v c8) (v c9) (v c10) (v c11) (v c12) (v c13) (v c14) (v c15) (as_nat h1 t0) (as_nat h1 t1) (as_nat h1 t2) (as_nat h1 t3) (as_nat h1 t4) (as_nat h1 t5) (as_nat h1 t6) (as_nat h1 t7) (as_nat h1 t8) (as_nat h2 o);

  FStar.Math.Lemmas.modulo_lemma (as_nat h2 o) S.prime;
  pop_frame()
