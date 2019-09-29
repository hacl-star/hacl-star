module Hacl.Impl.Ed25519.Ladder

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum25519

module S = Hacl.Spec.Ed25519.Field56.Definition
module F56 = Hacl.Impl.Ed25519.Field56
module F51 = Hacl.Impl.Ed25519.Field51

#set-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
val make_point_inf:
  b:lbuffer uint64 20ul ->
  Stack unit
    (requires fun h -> live h b)
    (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1 /\
      F51.point_inv_t h1 b /\
      F51.point_eval h1 b == Spec.Curve25519.(zero, one, one, zero)
    )
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
    (ensures fun h0 _ h1 -> modifies (loc g) h0 h1 /\
      F51.point_inv_t h1 g /\
      F51.point_eval h1 g == Spec.Ed25519.g
    )

let make_g g =
  let gx = getx g in
  let gy = gety g in
  let gz = getz g in
  let gt = gett g in
  make_u64_5 gx (u64 0x00062d608f25d51a) (u64 0x000412a4b4f6592a) (u64 0x00075b7171a4b31d) (u64 0x0001ff60527118fe) (u64 0x000216936d3cd6e5);
  make_u64_5 gy (u64 0x0006666666666658) (u64 0x0004cccccccccccc) (u64 0x0001999999999999) (u64 0x0003333333333333) (u64 0x0006666666666666);
  make_one gz;
  make_u64_5 gt (u64 0x00068ab3a5b7dda3) (u64 0x00000eea2a5eadbb) (u64 0x0002af8df483c27e) (u64 0x000332b375274732) (u64 0x00067875f0fd78b7);

  (**) assert_norm (Spec.Ed25519.g_x ==
    Hacl.Spec.Curve25519.Field51.Definition.as_nat5 (u64 0x00062d608f25d51a, u64 0x000412a4b4f6592a, u64 0x00075b7171a4b31d, u64 0x0001ff60527118fe, u64 0x000216936d3cd6e5) % Spec.Curve25519.prime);
  (**) assert_norm (Spec.Ed25519.g_y ==
    Hacl.Spec.Curve25519.Field51.Definition.as_nat5 (u64 0x0006666666666658, u64 0x0004cccccccccccc, u64 0x0001999999999999, u64 0x0003333333333333, u64 0x0006666666666666) %
      Spec.Curve25519.prime);
  (**) assert_norm (Mktuple4?._4 Spec.Ed25519.g ==
    Hacl.Spec.Curve25519.Field51.Definition.as_nat5 (u64 0x00068ab3a5b7dda3, u64 0x00000eea2a5eadbb, u64 0x0002af8df483c27e, u64 0x000332b375274732, u64 0x00067875f0fd78b7) % Spec.Curve25519.prime)

inline_for_extraction noextract
val ith_bit:
    k:lbuffer uint8 32ul
  -> i:size_t{v i < 256} ->
  Stack uint8
    (requires fun h -> live h k)
    (ensures fun h0 z h1 -> h0 == h1 /\ v z <= 1 /\
        z == Spec.Ed25519.ith_bit (as_seq h0 k) (v i)
    )
let ith_bit k i =
  let q = i >>. 3ul in
  let r = i &. 7ul in
  mod_mask_lemma i 3ul;
  Lib.IntTypes.Compatibility.uintv_extensionality 7ul (mod_mask #U32 3ul);
  assert (v r == v i % 8);
  let kq = k.(q) in
  let z = (kq >>. r) &. u8 1 in
  mod_mask_lemma (kq >>. r) 1ul;
  Lib.IntTypes.Compatibility.uintv_extensionality (u8 1) (mod_mask #U8 1ul);
  z

inline_for_extraction noextract
val loop_step:
    b:lbuffer uint64 80ul
  -> k:lbuffer uint8 32ul
  -> ctr:size_t{v ctr < 256} ->
  Stack unit
    (requires fun h -> live h b /\ live h k /\ disjoint k b /\
      F51.point_inv_t h (gsub b 0ul 20ul) /\
      F51.point_inv_t h (gsub b 20ul 20ul)
    )
    (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1 /\
      F51.point_inv_t h1 (gsub b 0ul 20ul) /\
      F51.point_inv_t h1 (gsub b 20ul 20ul) /\

      (F51.point_eval h1 (gsub b 0ul 20ul), F51.point_eval h1 (gsub b 20ul 20ul)) ==
      Spec.Ed25519.ladder_step (as_seq h0 k) (v ctr)
       (F51.point_eval h0 (gsub b 0ul 20ul), F51.point_eval h0 (gsub b 20ul 20ul))
    )

#push-options "--z3rlimit 60"

let lemma_to_u8_to_u64 (i:uint8) : Lemma (to_u8 (to_u64 i) == i)
  = ()

let loop_step b k ctr =
  let nq    = sub b 0ul 20ul in
  let nqpq  = sub b 20ul 20ul in
  let nq2   = sub b 40ul 20ul in
  let nqpq2 = sub b 60ul 20ul in
  let i  = ith_bit k (255ul -. ctr) in
  (**) assert (v (255ul -. ctr) == 255 - v ctr);
  (**) lemma_to_u8_to_u64 i;
  Hacl.Impl.Ed25519.SwapConditional.swap_conditional_inplace nq nqpq (to_u64 i);
  Hacl.Impl.Ed25519.PointDouble.point_double nq2 nq;
  Hacl.Impl.Ed25519.PointAdd.point_add nqpq2 nq nqpq;
  Hacl.Impl.Ed25519.SwapConditional.swap_conditional nq nqpq nq2 nqpq2 (to_u64 i)

#pop-options

inline_for_extraction noextract
val point_mul_:
    b:lbuffer uint64 80ul
  -> k:lbuffer uint8 32ul ->
  Stack unit
    (requires fun h -> live h k /\ live h b /\ disjoint b k /\
      F51.point_inv_t h (gsub b 0ul 20ul) /\ F51.point_inv_t h (gsub b 20ul 20ul) /\
      F51.point_eval h (gsub b 0ul 20ul) == Spec.Curve25519.(zero, one, one, zero)
    )
    (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1 /\
       F51.point_inv_t h1 (gsub b 0ul 20ul) /\ F51.point_inv_t h1 (gsub b 20ul 20ul) /\
       F51.point_eval h1 (gsub b 0ul 20ul) ==
       Spec.Ed25519.point_mul (as_seq h0 k) (F51.point_eval h0 (gsub b 20ul 20ul))
    )

#set-options "--z3rlimit 60 --max_fuel 0 --max_ifuel 0"

let point_mul_ b k =
  let h0 = ST.get() in

  [@inline_let]
  let spec h0 = Spec.Ed25519.ladder_step (as_seq h0 k) in

  [@inline_let]
  let acc h : GTot (Spec.Ed25519.ext_point & Spec.Ed25519.ext_point) =
    F51.point_eval h (gsub b 0ul 20ul), F51.point_eval h (gsub b 20ul 20ul)
  in

  [@inline_let]
  let inv h (i:nat{i <= 256}) = modifies (loc b) h0 h /\
    F51.point_inv_t h (gsub b 0ul 20ul) /\ F51.point_inv_t h (gsub b 20ul 20ul) /\
    acc h == Lib.LoopCombinators.repeati i (spec h0) (acc h0)
  in

  Lib.LoopCombinators.eq_repeati0 256 (spec h0) (acc h0);
  Lib.Loops.for 0ul 256ul inv
    (fun i ->
      Lib.LoopCombinators.unfold_repeati 256 (spec h0) (acc h0) (v i);
      loop_step b k i)

val point_mul:
    result:point
  -> scalar:lbuffer uint8 32ul
  -> q:point ->
  Stack unit
    (requires fun h -> live h scalar /\ live h q /\ live h result /\
      F51.point_inv_t h q
    )
    (ensures  fun h0 _ h1 -> modifies (loc result) h0 h1 /\
      F51.point_inv_t h1 result /\
      F51.point_eval h1 result == Spec.Ed25519.point_mul (as_seq h0 scalar) (F51.point_eval h0 q)
    )

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
    (ensures  fun h0 _ h1 -> modifies (loc result) h0 h1 /\
      F51.point_inv_t h1 result /\
      F51.point_eval h1 result == Spec.Ed25519.point_mul (as_seq h0 scalar) Spec.Ed25519.g
    )
let point_mul_g result scalar =
  push_frame();
  let g = create 20ul (u64 0) in
  make_g g;
  point_mul result scalar g;
  pop_frame()
