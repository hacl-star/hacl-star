module Hacl.Impl.Ed25519.Ladder

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum25519

inline_for_extraction noextract
val make_point_inf:
  b:lbuffer uint64 20ul ->
  Stack unit
    (requires fun h -> live h b)
    (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1)
let make_point_inf b =
  let x = sub b 0ul 5ul in
  let y = sub b 5ul 5ul in
  let z = sub b 10ul 5ul in
  let t = sub b 15ul 5ul in
  make_zero x;
  make_one y;
  make_one z;
  make_zero t

inline_for_extraction noextract
val make_g:
  g:point ->
  Stack unit
    (requires fun h -> live h g)
    (ensures fun h0 _ h1 -> modifies (loc g) h0 h1)
let make_g g =
  let gx = getx g in
  let gy = gety g in
  let gz = getz g in
  let gt = gett g in
  make_u64_5 gx (u64 0x00062d608f25d51a) (u64 0x000412a4b4f6592a) (u64 0x00075b7171a4b31d) (u64 0x0001ff60527118fe) (u64 0x000216936d3cd6e5);
  make_u64_5 gy (u64 0x0006666666666658) (u64 0x0004cccccccccccc) (u64 0x0001999999999999) (u64 0x0003333333333333) (u64 0x0006666666666666);
  make_one gz;
  make_u64_5 gt (u64 0x00068ab3a5b7dda3) (u64 0x00000eea2a5eadbb) (u64 0x0002af8df483c27e) (u64 0x000332b375274732) (u64 0x00067875f0fd78b7)

inline_for_extraction noextract
val ith_bit:
    k:lbuffer uint8 32ul
  -> i:size_t{v i < 256} ->
  Stack uint8
    (requires fun h -> live h k)
    (ensures fun h0 z h1 -> h0 == h1 /\ v z <= 1)
let ith_bit k i =
  let q = i >>. 3ul in
  let r = i &. 7ul in
  mod_mask_lemma i 3ul;
  uintv_extensionality 7ul (mod_mask #U32 3ul);
  assert (v r == v i % 8);
  let kq = k.(q) in
  let z = (kq >>. r) &. u8 1 in
  mod_mask_lemma (kq >>. r) 1ul;
  uintv_extensionality (u8 1) (mod_mask #U8 1ul);
  z


inline_for_extraction noextract
val loop_step:
    b:lbuffer uint64 80ul
  -> k:lbuffer uint8 32ul
  -> ctr:size_t{v ctr < 256} ->
  Stack unit
    (requires fun h -> live h b /\ live h k /\ disjoint k b)
    (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1)
let loop_step b k ctr =
  let nq    = sub b 0ul 20ul in
  let nqpq  = sub b 20ul 20ul in
  let nq2   = sub b 40ul 20ul in
  let nqpq2 = sub b 60ul 20ul in
  let i  = ith_bit k ctr in
  Hacl.Impl.Ed25519.SwapConditional.swap_conditional_inplace nq nqpq (to_u64 i);
  Hacl.Impl.Ed25519.PointDouble.point_double nq2 nq;
  Hacl.Impl.Ed25519.PointAdd.point_add nqpq2 nq nqpq;
  Hacl.Impl.Ed25519.SwapConditional.swap_conditional nq nqpq nq2 nqpq2 (to_u64 i)

inline_for_extraction noextract
val point_mul_:
    b:lbuffer uint64 80ul
  -> k:lbuffer uint8 32ul ->
  Stack unit
    (requires fun h -> live h k /\ live h b /\ disjoint b k)
    (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1)
let point_mul_ b k =
  let h0 = ST.get() in
  let inv h (i:nat{i <= 256}) = modifies (loc b) h0 h in
  Lib.Loops.for 0ul 256ul inv
    (fun i -> loop_step b k (256ul -. i -. 1ul))

val point_mul:
    result:point
  -> scalar:lbuffer uint8 32ul
  -> q:point ->
  Stack unit
    (requires fun h -> live h scalar /\ live h q /\ live h result)
    (ensures  fun h0 _ h1 -> modifies (loc result) h0 h1)
let point_mul result scalar q =
  push_frame();
  let b = create 80ul (u64 0) in
  let nq   = sub b  0ul 20ul in
  let nqpq = sub b 20ul 20ul in
  make_point_inf nq;
  copy nqpq q;
  point_mul_ b scalar;
  copy result nq;
  pop_frame()

val point_mul_g:
    result:point
  -> scalar:lbuffer uint8 32ul ->
  Stack unit
    (requires fun h ->
      live h scalar /\ live h result /\ disjoint result scalar)
    (ensures  fun h0 _ h1 -> modifies (loc result) h0 h1)
let point_mul_g result scalar =
  push_frame();
  let g = create 20ul (u64 0) in
  make_g g;
  point_mul result scalar g;
  pop_frame()
