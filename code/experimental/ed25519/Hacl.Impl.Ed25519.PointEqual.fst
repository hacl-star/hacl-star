module Hacl.Impl.Ed25519.PointEqual

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum25519

val gte_q:
  s:lbuffer uint64 5ul ->
  Stack bool
    (requires fun h -> live h s)
    (ensures  fun h0 b h1 -> h0 == h1)
let gte_q s =
  let s0 = s.(0ul) in
  let s1 = s.(1ul) in
  let s2 = s.(2ul) in
  let s3 = s.(3ul) in
  let s4 = s.(4ul) in
  let open FStar.UInt64 in
  let open Lib.RawIntTypes in
       if u64_to_UInt64 s4 >^ 0x00000010000000uL then true
  else if u64_to_UInt64 s4 <^ 0x00000010000000uL then false
  else if u64_to_UInt64 s3 >^ 0x00000000000000uL then true
  else if u64_to_UInt64 s2 >^ 0x000000000014deuL then true
  else if u64_to_UInt64 s2 <^ 0x000000000014deuL then false
  else if u64_to_UInt64 s1 >^ 0xf9dea2f79cd658uL then true
  else if u64_to_UInt64 s1 <^ 0xf9dea2f79cd658uL then false
  else if u64_to_UInt64 s0 >=^ 0x12631a5cf5d3eduL then true
  else false

val eq:
    a:felem
  -> b:felem ->
  Stack bool
    (requires fun h -> live h a /\ live h b)
    (ensures  fun h0 r h1 -> h0 == h1)
let eq a b =
  let a0 = a.(0ul) in
  let a1 = a.(1ul) in
  let a2 = a.(2ul) in
  let a3 = a.(3ul) in
  let a4 = a.(4ul) in
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let b4 = b.(4ul) in
  let open Lib.RawIntTypes in
  let open FStar.UInt64 in
  (u64_to_UInt64 a0 =^ u64_to_UInt64 b0 &&
   u64_to_UInt64 a1 =^ u64_to_UInt64 b1 &&
   u64_to_UInt64 a2 =^ u64_to_UInt64 b2 &&
   u64_to_UInt64 a3 =^ u64_to_UInt64 b3 &&
   u64_to_UInt64 a4 =^ u64_to_UInt64 b4)

val point_equal_1:
    p:point
  -> q:point
  -> tmp:lbuffer uint64 20ul ->
  Stack bool
    (requires fun h ->
      live h p /\ live h q /\ live h tmp /\
      disjoint tmp p /\ disjoint tmp q)
    (ensures  fun h0 z h1 -> modifies (loc tmp) h0 h1)
let point_equal_1 p q tmp =
  let pxqz = sub tmp 0ul 5ul in
  let qxpz = sub tmp 5ul 5ul in
  let pyqz = sub tmp 10ul 5ul in
  let qypz = sub tmp 15ul 5ul in
  fmul pxqz (getx p) (getz q);
  reduce pxqz;
  fmul qxpz (getx q) (getz p);
  reduce qxpz;
  eq pxqz qxpz

val point_equal_2:
    p:point
  -> q:point
  -> tmp:lbuffer uint64 20ul ->
  Stack bool
    (requires fun h ->
      live h p /\ live h q /\live h tmp /\
      disjoint tmp p /\ disjoint tmp q)
    (ensures  fun h0 z h1 -> modifies (loc tmp) h0 h1)
let point_equal_2 p q tmp =
  let pxqz = sub tmp 0ul 5ul in
  let qxpz = sub tmp 5ul 5ul in
  let pyqz = sub tmp 10ul 5ul in
  let qypz = sub tmp 15ul 5ul in
  fmul pyqz (gety p) (getz q);
  reduce pyqz;
  fmul qypz (gety q) (getz p);
  reduce qypz;
  eq pyqz qypz

val point_equal:
    p:point
  -> q:point ->
  Stack bool
    (requires fun h -> live h p /\ live h q)
    (ensures  fun h0 z h1 -> modifies0 h0 h1)
let point_equal p q =
  push_frame();
  let tmp = create 20ul (u64 0) in
  let b = point_equal_1 p q tmp in
  let res = if b then point_equal_2 p q tmp else false in
  pop_frame();
  res
