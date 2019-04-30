module Hacl.Impl.Ed25519.Pow2_252m2

open FStar.HyperStack.All
module ST = FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum25519

inline_for_extraction noextract
val crecip_1:
    buf:lbuffer uint64 20ul
  -> z:felem ->
  Stack unit
    (requires fun h -> live h buf /\ live h z /\ disjoint buf z)
    (ensures  fun h0 _ h1 -> modifies (loc buf) h0 h1)
let crecip_1 buf z =
  let a  = sub buf 0ul  5ul in
  let t0 = sub buf 5ul  5ul in
  let b  = sub buf 10ul 5ul in
  let c  = sub buf 15ul 5ul in
  fsquare_times a z 1ul;
  fsquare_times t0 a 2ul;
  fmul b t0 z;
  fmul a b a;
  fsquare_times t0 a 1ul;
  fmul b t0 b;
  fsquare_times t0 b 5ul

inline_for_extraction noextract
val crecip_2:
  buf:lbuffer uint64 20ul ->
  Stack unit
  (requires fun h -> live h buf)
  (ensures  fun h0 _ h1 -> modifies (loc buf) h0 h1)
let crecip_2 buf =
  let a  = sub buf 0ul  5ul in
  let t0 = sub buf 5ul  5ul in
  let b  = sub buf 10ul 5ul in
  let c  = sub buf 15ul 5ul in
  fmul b t0 b;
  fsquare_times t0 b 10ul;
  fmul c t0 b;
  fsquare_times t0 c 20ul;
  fmul t0 t0 c;
  fsquare_times_inplace t0 10ul;
  fmul b t0 b;
  fsquare_times t0 b 50ul

inline_for_extraction noextract
val crecip_3':
    out:felem
  -> buf:lbuffer uint64 20ul ->
  Stack unit
  (requires fun h -> live h buf /\ live h out /\ disjoint out buf)
  (ensures  fun h0 _ h1 -> modifies (loc out |+| loc buf) h0 h1)
let crecip_3' out buf =
  let a  = sub buf 0ul  5ul in
  let t0 = sub buf 5ul  5ul in
  let b  = sub buf 10ul 5ul in
  let c  = sub buf 15ul 5ul in
  fmul c t0 b;
  fsquare_times t0 c 100ul;
  fmul t0 t0 c;
  fsquare_times_inplace t0 50ul;
  fmul t0 t0 b;
  fsquare_times_inplace t0 2ul;
  fmul out t0 a

inline_for_extraction noextract
val crecip':
    out:felem
  -> z:felem ->
  Stack unit
    (requires fun h -> live h out /\ live h z /\ disjoint out z)
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1)
let crecip' out z =
  push_frame();
  let buf = create 20ul (u64 0) in
  crecip_1 buf z;
  crecip_2 buf;
  let a  = sub buf 0ul  5ul in
  let t0 = sub buf 5ul  5ul in
  let b  = sub buf 10ul 5ul in
  let c  = sub buf 15ul 5ul in
  fsquare_times a z 1ul;
  crecip_3' out buf;
  pop_frame()

val pow2_252m2:
    out:felem
  -> z:felem ->
  Stack unit
    (requires fun h -> live h out /\ live h z /\ disjoint out z)
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1)
let pow2_252m2 out z = crecip' out z
