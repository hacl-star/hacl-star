module Hacl.Impl.Ed25519.PointAdd

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum25519

module F51 = Hacl.Impl.Ed25519.Field51
module F56 = Hacl.Impl.Ed25519.Field56

module SC = Spec.Curve25519

#set-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
val point_add_step_1:
    p:point
  -> q:point
  -> tmp:lbuffer uint64 30ul ->
  Stack unit
    (requires fun h ->
      live h p /\ live h q /\ live h tmp /\
      disjoint tmp p /\ disjoint tmp q /\
      F51.point_inv_t h p /\
      F51.point_inv_t h q
      )
    (ensures fun h0 _ h1 -> modifies (loc tmp) h0 h1 /\
      (let x1 = F51.fevalh h0 (gsub p 0ul 5ul) in
       let y1 = F51.fevalh h0 (gsub p 5ul 5ul) in
       let x2 = F51.fevalh h0 (gsub q 0ul 5ul) in
       let y2 = F51.fevalh h0 (gsub q 5ul 5ul) in
       let a = (y1 `SC.fsub` x1) `SC.fmul` (y2 `SC.fsub` x2) in
       let b = (y1 `SC.fadd` x1) `SC.fmul` (y2 `SC.fadd` x2) in
       F51.mul_inv_t h1 (gsub tmp 10ul 5ul) /\
       F51.mul_inv_t h1 (gsub tmp 15ul 5ul) /\
       F51.fevalh h1 (gsub tmp 10ul 5ul) == a /\
       F51.fevalh h1 (gsub tmp 15ul 5ul) == b)
    )
let point_add_step_1 p q tmp =
  let tmp1 = sub tmp 0ul 5ul in
  let tmp2 = sub tmp 5ul 5ul in
  let tmp3 = sub tmp 10ul 5ul in
  let tmp4 = sub tmp 15ul 5ul in
  //let tmp5 = sub tmp 20ul 5ul in
  //let tmp6 = sub tmp 25ul 5ul in
  let x1 = getx p in
  let y1 = gety p in
  let x2 = getx q in
  let y2 = gety q in
  copy tmp1 x1; // tmp1 = x1
  copy tmp2 x2; // tmp2 = x2
  fdifference tmp1 y1;    // tmp1 = y1 - x1
  fdifference tmp2 y2;    // tmp2 = y2 - x2
  fmul tmp3 tmp1 tmp2;    // tmp3 = a
  copy tmp1 y1; // tmp1 = y1
  copy tmp2 y2; // tmp2 = y2
  fsum tmp1 x1;             // tmp1 = y1 + x1
  fsum tmp2 x2;             // tmp2 = y2 + x2
  fmul tmp4 tmp1 tmp2

inline_for_extraction noextract
val point_add_step_2:
    p:point
  -> q:point
  -> tmp:lbuffer uint64 30ul ->
  Stack unit
    (requires fun h ->
      live h p /\ live h q /\ live h tmp /\
      disjoint tmp p /\ disjoint tmp q /\
      F51.point_inv_t h p /\
      F51.point_inv_t h q /\
      F51.mul_inv_t h (gsub tmp 10ul 5ul) /\
      F51.mul_inv_t h (gsub tmp 15ul 5ul)
    )
    (ensures fun h0 _ h1 -> modifies (loc tmp) h0 h1 /\
      (let z1 = F51.fevalh h0 (gsub p 10ul 5ul) in
       let t1 = F51.fevalh h0 (gsub p 15ul 5ul) in
       let z2 = F51.fevalh h0 (gsub q 10ul 5ul) in
       let t2 = F51.fevalh h0 (gsub q 15ul 5ul) in
       let a = F51.fevalh h0 (gsub tmp 10ul 5ul) in
       let b = F51.fevalh h0 (gsub tmp 15ul 5ul) in
       let c = (2 `SC.fmul` Spec.Ed25519.d `SC.fmul` t1) `SC.fmul` t2 in
       let d = (2 `SC.fmul` z1) `SC.fmul` z2 in
       let e = b `SC.fsub` a in
       let f = d `SC.fsub` c in
       let g = d `SC.fadd` c in
       let h = b `SC.fadd` a in
       F51.felem_fits h1 (gsub tmp 0ul 5ul) (9, 10, 9, 9, 9) /\
       F51.felem_fits h1 (gsub tmp 25ul 5ul) (9, 10, 9, 9, 9) /\
       F51.felem_fits h1 (gsub tmp 20ul 5ul) (9, 10, 9, 9, 9) /\
       F51.felem_fits h1 (gsub tmp 15ul 5ul) (9, 10, 9, 9, 9) /\
       F51.fevalh h1 (gsub tmp 0ul 5ul) == e /\
       F51.fevalh h1 (gsub tmp 25ul 5ul) == f /\
       F51.fevalh h1 (gsub tmp 20ul 5ul) == g /\
       F51.fevalh h1 (gsub tmp 15ul 5ul) == h)
    )

#push-options "--z3rlimit 50"

let point_add_step_2 p q tmp =
  let tmp1 = sub tmp 0ul 5ul in
  let tmp2 = sub tmp 5ul 5ul in
  let tmp3 = sub tmp 10ul 5ul in
  let tmp4 = sub tmp 15ul 5ul in
  let tmp5 = sub tmp 20ul 5ul in
  let tmp6 = sub tmp 25ul 5ul in
  let z1 = getz p in
  let t1 = gett p in
  let z2 = getz q in
  let t2 = gett q in
  times_2d tmp1 t1;
  fmul tmp2 tmp1 t2;        // tmp2 = c
  times_2 tmp1 z1;
  fmul tmp5 tmp1 z2;        // tmp5 = d
  copy tmp1 tmp3; // tmp1 = a
  copy tmp6 tmp2; // tmp6 = c
  fdifference tmp1 tmp4; // tmp1 = e
  fdifference tmp6 tmp5; // tmp6 = f
  fsum tmp5 tmp2;                // tmp5 = g
  fsum tmp4 tmp3                // tmp4 = h

#pop-options

inline_for_extraction noextract
val point_add_:
    out:point
  -> p:point
  -> q:point
  -> tmp:lbuffer uint64 30ul ->
  Stack unit
    (requires fun h ->
      live h out /\ live h p /\ live h q /\ live h tmp /\
      disjoint tmp p /\ disjoint tmp q /\ disjoint tmp out /\
      disjoint p out /\ disjoint q out /\
      F51.point_inv_t h p /\
      F51.point_inv_t h q
    )
    (ensures fun h0 _ h1 -> modifies (loc out |+| loc tmp) h0 h1 /\
      F51.point_inv_t h1 out /\
      F51.point_eval h1 out == Spec.Ed25519.point_add (F51.point_eval h0 p) (F51.point_eval h0 q)
    )
let point_add_ out p q tmp =
  point_add_step_1 p q tmp;
  point_add_step_2 p q tmp;
  let tmp1 = sub tmp 0ul 5ul in
  //let tmp2 = sub tmp 5ul 5ul in
  //let tmp3 = sub tmp 10ul 5ul in
  let tmp4 = sub tmp 15ul 5ul in
  let tmp5 = sub tmp 20ul 5ul in
  let tmp6 = sub tmp 25ul 5ul in
  let x3 = getx out in
  let y3 = gety out in
  let z3 = getz out in
  let t3 = gett out in
  fmul x3 tmp1 tmp6;
  fmul y3 tmp5 tmp4;
  fmul t3 tmp1 tmp4;
  fmul z3 tmp6 tmp5

val point_add:
    out:point
  -> p:point
  -> q:point ->
  Stack unit
    (requires fun h ->
      live h out /\ live h p /\ live h q /\
      disjoint p out /\ disjoint q out /\
      F51.point_inv_t h p /\
      F51.point_inv_t h q
      )
    (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\
      F51.point_inv_t h1 out /\
      F51.point_eval h1 out == Spec.Ed25519.point_add (F51.point_eval h0 p) (F51.point_eval h0 q)
    )
let point_add out p q =
  push_frame();
  let tmp = create 30ul (u64 0) in
  point_add_ out p q tmp;
  pop_frame()
