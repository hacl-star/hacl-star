module Hacl.Impl.Ed25519.PointAdd

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Buffer
open Hacl.Bignum25519
open Hacl.Impl.Ed25519.ExtPoint


#reset-options "--max_fuel 0 --z3rlimit 100"

(* Specification:

let point_add (p:ext_point) (q:ext_point) : Tot ext_point =
  let x1, y1, z1, t1 = p in
  let x2, y2, z2, t2 = q in
  let a = (y1 `fsub` x1) `fmul` (y2 `fsub` x2) in
  let b = (y1 `fadd` x1) `fmul` (y2 `fadd` x2) in
  let c = t1 `fmul` 2 `fmul` d `fmul` t2 in
  let d = z1 `fmul` 2 `fmul` z2 in
  let e = b `fsub` a in
  let f = d `fsub` c in
  let g = d `fadd` c in
  let h = b `fadd` a in
  let x3 = e `fmul` f in
  let y3 = g `fmul` h in
  let t3 = e `fmul` h in
  let z3 = f `fmul` g in
  (x3, y3, z3, t3)

*)

inline_for_extraction
private
val copy:
  a:buffer Hacl.UInt64.t{length a = 5} ->
  b:buffer Hacl.UInt64.t{length b = 5 /\ disjoint a b} ->
  Stack unit
    (requires (fun h -> live h a /\ live h b))
    (ensures (fun h0 _ h1 -> live h0 a /\ live h1 b /\ modifies_1 b h0 h1
      /\ as_seq h0 a == as_seq h1 b))

let copy a b =
  let h = ST.get() in
  blit a 0ul b 0ul 5ul;
  let h' = ST.get() in
  Seq.lemma_eq_intro (as_seq h a) (Seq.slice (as_seq h a) 0 5);
  Seq.lemma_eq_intro (as_seq h' b) (Seq.slice (as_seq h' b) 0 5)


#reset-options "--max_fuel 0 --z3rlimit 100"

inline_for_extraction
private
val point_add_step_1:
  p:point ->
  q:point ->
  tmp:buffer Hacl.UInt64.t{length tmp = 30 /\ disjoint tmp p /\ disjoint tmp q} ->
  Stack unit
    (requires (fun h -> live h p /\ live h q /\ live h tmp /\
      (
        let x1 = as_seq h (getx p) in
        let y1 = as_seq h (gety p) in
        let z1 = as_seq h (getz p) in
        let t1 = as_seq h (gett p) in
        let x2 = as_seq h (getx q) in
        let y2 = as_seq h (gety q) in
        let z2 = as_seq h (getz q) in
        let t2 = as_seq h (gett q) in
        red_513 x1 /\ red_513 y1 /\ red_513 z1 /\ red_513 t1 /\
        red_513 x2 /\ red_513 y2 /\ red_513 z2 /\ red_513 t2)
      ))
    (ensures (fun h0 _ h1 -> live h0 p /\ live h0 q /\ modifies_1 tmp h0 h1 /\ live h1 tmp /\
      (
        let x1 = as_seq h0 (getx p) in
        let y1 = as_seq h0 (gety p) in
        let z1 = as_seq h0 (getz p) in
        let t1 = as_seq h0 (gett p) in
        let x2 = as_seq h0 (getx q) in
        let y2 = as_seq h0 (gety q) in
        let z2 = as_seq h0 (getz q) in
        let t2 = as_seq h0 (gett q) in
        let tmp1 = as_seq h1 (sub tmp 0ul 5ul) in
        let tmp2 = as_seq h1 (sub tmp 5ul 5ul) in
        let tmp3 = as_seq h1 (sub tmp 10ul 5ul) in
        let tmp4 = as_seq h1 (sub tmp 15ul 5ul) in
        let tmp5 = as_seq h1 (sub tmp 20ul 5ul) in
        let tmp6 = as_seq h1 (sub tmp 25ul 5ul) in
        seval tmp3 == Spec.Curve25519.((seval y1 `fsub` seval x1) `fmul` (seval y2 `fsub` seval x2)) /\
        seval tmp4 == Spec.Curve25519.((seval y1 `fadd` seval x1) `fmul` (seval y2 `fadd` seval x2)) /\
        red_513 tmp3 /\ red_513 tmp4
        )
  ))

#reset-options "--max_fuel 0 --z3rlimit 200"

inline_for_extraction
private
let point_add_step_1 p q tmp =
  let tmp1 = sub tmp 0ul 5ul in
  let tmp2 = sub tmp 5ul 5ul in
  let tmp3 = sub tmp 10ul 5ul in
  let tmp4 = sub tmp 15ul 5ul in
  let tmp5 = sub tmp 20ul 5ul in
  let tmp6 = sub tmp 25ul 5ul in
  let x1 = getx p in
  let y1 = gety p in
//  let z1 = getz p in
//  let t1 = gett p in
  let x2 = getx q in
  let y2 = gety q in
//  let z2 = getz q in
//  let t2 = gett q in
  copy x1 tmp1; // tmp1 = x1
  copy x2 tmp2; // tmp2 = x2
  fdifference_reduced tmp1 y1;    // tmp1 = y1 - x1
  let h = ST.get() in
  lemma_red_513_is_red_53 (as_seq h tmp1);
  fdifference tmp2 y2;    // tmp2 = y2 - x2
  fmul tmp3 tmp1 tmp2;    // tmp3 = a
  copy y1 tmp1; // tmp1 = y1
  copy y2 tmp2; // tmp2 = y2
  fsum tmp1 x1;             // tmp1 = y1 + x1
  fsum tmp2 x2;             // tmp2 = y2 + x2
  let h = ST.get() in
  lemma_red_53_is_red_5413 (as_seq h tmp2);
  fmul tmp4 tmp1 tmp2


inline_for_extraction
private
val point_add_step_2:
  p:point ->
  q:point ->
  tmp:buffer Hacl.UInt64.t{length tmp = 30 /\ disjoint tmp p /\ disjoint tmp q} ->
  Stack unit
    (requires (fun h -> live h p /\ live h q /\ live h tmp /\
      (
        let x1 = as_seq h (getx p) in
        let y1 = as_seq h (gety p) in
        let z1 = as_seq h (getz p) in
        let t1 = as_seq h (gett p) in
        let x2 = as_seq h (getx q) in
        let y2 = as_seq h (gety q) in
        let z2 = as_seq h (getz q) in
        let t2 = as_seq h (gett q) in
        let tmp3 = as_seq h (sub tmp 10ul 5ul) in
        let tmp4 = as_seq h (sub tmp 15ul 5ul) in
        red_513 x1 /\ red_513 y1 /\ red_513 z1 /\ red_513 t1 /\
        red_513 x2 /\ red_513 y2 /\ red_513 z2 /\ red_513 t2 /\
        red_513 tmp3 /\ red_513 tmp4)
      ))
    (ensures (fun h0 _ h1 -> live h0 p /\ live h0 q /\ modifies_1 tmp h0 h1 /\ live h1 tmp /\ live h0 tmp /\
      (
        let x1 = as_seq h0 (getx p) in
        let y1 = as_seq h0 (gety p) in
        let z1 = as_seq h0 (getz p) in
        let t1 = as_seq h0 (gett p) in
        let x2 = as_seq h0 (getx q) in
        let y2 = as_seq h0 (gety q) in
        let z2 = as_seq h0 (getz q) in
        let t2 = as_seq h0 (gett q) in
        let tmp1 = as_seq h1 (sub tmp 0ul 5ul) in
        let tmp2 = as_seq h1 (sub tmp 5ul 5ul) in
        let tmp3 = as_seq h0 (sub tmp 10ul 5ul) in
        let tmp4 = as_seq h0 (sub tmp 15ul 5ul) in
        let tmp3' = as_seq h1 (sub tmp 10ul 5ul) in
        let tmp4' = as_seq h1 (sub tmp 15ul 5ul) in
        let tmp5 = as_seq h1 (sub tmp 20ul 5ul) in
        let tmp6 = as_seq h1 (sub tmp 25ul 5ul) in
        tmp4' == tmp4 /\
        tmp3' == tmp3 /\
        tmp1 == tmp3 /\
        tmp6 == tmp2 /\
        seval tmp2 == Spec.Curve25519.((2 `fmul` Spec.Ed25519.d `fmul` seval t1) `fmul` seval t2) /\
        seval tmp5 == Spec.Curve25519.((2 `fmul` seval z1) `fmul` seval z2) /\
        red_513 tmp1 /\ red_513 tmp2 /\ red_513 tmp3' /\ red_513 tmp4' /\ red_513 tmp5 /\ red_513 tmp6)
  ))

#reset-options "--max_fuel 0 --z3rlimit 200"

inline_for_extraction
private
let point_add_step_2 p q tmp =
  let tmp1 = sub tmp 0ul 5ul in
  let tmp2 = sub tmp 5ul 5ul in
  let tmp3 = sub tmp 10ul 5ul in
  let tmp4 = sub tmp 15ul 5ul in
  let tmp5 = sub tmp 20ul 5ul in
  let tmp6 = sub tmp 25ul 5ul in
//  let x1 = getx p in
//  let y1 = gety p in
  let z1 = getz p in
  let t1 = gett p in
//  let x2 = getx q in
//  let y2 = gety q in
  let z2 = getz q in
  let t2 = gett q in
  let h0 = ST.get() in
  times_2d tmp1 t1;
  let h = ST.get() in
  lemma_red_513_is_red_53 (as_seq h tmp1);
  lemma_red_513_is_red_5413 (as_seq h t2);
  let h1 = ST.get() in
  no_upd_lemma_1 h0 h1 tmp1 tmp2;
  no_upd_lemma_1 h0 h1 tmp1 tmp3;
  no_upd_lemma_1 h0 h1 tmp1 tmp4;
  no_upd_lemma_1 h0 h1 tmp1 tmp5;
  no_upd_lemma_1 h0 h1 tmp1 tmp6;
  no_upd_lemma_1 h0 h1 tmp1 t2;
  no_upd_lemma_1 h0 h1 tmp1 z1;
  no_upd_lemma_1 h0 h1 tmp1 z2;
  fmul tmp2 tmp1 t2;        // tmp2 = c
  let h2 = ST.get() in
  no_upd_lemma_1 h1 h2 tmp2 tmp1;
  no_upd_lemma_1 h1 h2 tmp2 tmp3;
  no_upd_lemma_1 h1 h2 tmp2 tmp4;
  no_upd_lemma_1 h1 h2 tmp2 tmp5;
  no_upd_lemma_1 h1 h2 tmp2 tmp6;
  no_upd_lemma_1 h1 h2 tmp2 z1;
  no_upd_lemma_1 h1 h2 tmp2 z2;
  times_2 tmp1 z1;
  let h = ST.get() in
  lemma_red_513_is_red_5413 (as_seq h z2);
  let h3 = ST.get() in
  no_upd_lemma_1 h2 h3 tmp1 tmp2;
  no_upd_lemma_1 h2 h3 tmp1 tmp3;
  no_upd_lemma_1 h2 h3 tmp1 tmp4;
  no_upd_lemma_1 h2 h3 tmp1 tmp5;
  no_upd_lemma_1 h2 h3 tmp1 tmp6;
  no_upd_lemma_1 h2 h3 tmp1 z2;
  fmul tmp5 tmp1 z2;        // tmp5 = d
  let h4 = ST.get() in
  no_upd_lemma_1 h3 h4 tmp5 tmp2;
  no_upd_lemma_1 h3 h4 tmp5 tmp3;
  no_upd_lemma_1 h3 h4 tmp5 tmp4;
  no_upd_lemma_1 h3 h4 tmp5 tmp1;
  no_upd_lemma_1 h3 h4 tmp5 tmp6;
  copy tmp3 tmp1; // tmp1 = a
  let h5 = ST.get() in
  no_upd_lemma_1 h4 h5 tmp1 tmp2;
  no_upd_lemma_1 h4 h5 tmp1 tmp3;
  no_upd_lemma_1 h4 h5 tmp1 tmp4;
  no_upd_lemma_1 h4 h5 tmp1 tmp5;
  no_upd_lemma_1 h4 h5 tmp1 tmp6;
  copy tmp2 tmp6; // tmp6 = c
  let h6 = ST.get() in
  no_upd_lemma_1 h5 h6 tmp6 tmp2;
  no_upd_lemma_1 h5 h6 tmp6 tmp3;
  no_upd_lemma_1 h5 h6 tmp6 tmp4;
  no_upd_lemma_1 h5 h6 tmp6 tmp5;
  no_upd_lemma_1 h5 h6 tmp6 tmp1;
  ()


inline_for_extraction
private
val point_add_step_3:
  p:point ->
  q:point ->
  tmp:buffer Hacl.UInt64.t{length tmp = 30 /\ disjoint tmp p /\ disjoint tmp q} ->
  Stack unit
    (requires (fun h -> live h p /\ live h q /\ live h tmp /\
      (
        let x1 = as_seq h (getx p) in
        let y1 = as_seq h (gety p) in
        let z1 = as_seq h (getz p) in
        let t1 = as_seq h (gett p) in
        let x2 = as_seq h (getx q) in
        let y2 = as_seq h (gety q) in
        let z2 = as_seq h (getz q) in
        let t2 = as_seq h (gett q) in
        let tmp1 = as_seq h (sub tmp 0ul 5ul) in
        let tmp2 = as_seq h (sub tmp 5ul 5ul) in
        let tmp3 = as_seq h (sub tmp 10ul 5ul) in
        let tmp4 = as_seq h (sub tmp 15ul 5ul) in
        let tmp5 = as_seq h (sub tmp 20ul 5ul) in
        let tmp6 = as_seq h (sub tmp 25ul 5ul) in
        red_513 x1 /\ red_513 y1 /\ red_513 z1 /\ red_513 t1 /\
        red_513 x2 /\ red_513 y2 /\ red_513 z2 /\ red_513 t2 /\
        red_513 tmp1 /\ red_513 tmp2 /\ red_513 tmp3 /\ red_513 tmp4 /\ red_513 tmp5 /\ red_513 tmp6)
     ))
    (ensures (fun h0 _ h1 -> live h0 p /\ live h0 q /\ modifies_1 tmp h0 h1 /\ live h1 tmp /\ live h0 tmp /\
      (
        let x1 = as_seq h0 (getx p) in
        let y1 = as_seq h0 (gety p) in
        let z1 = as_seq h0 (getz p) in
        let t1 = as_seq h0 (gett p) in
        let x2 = as_seq h0 (getx q) in
        let y2 = as_seq h0 (gety q) in
        let z2 = as_seq h0 (getz q) in
        let t2 = as_seq h0 (gett q) in
        let tmp1 = as_seq h0 (sub tmp 0ul 5ul) in
        let tmp2 = as_seq h0 (sub tmp 5ul 5ul) in
        let tmp1' = as_seq h1 (sub tmp 0ul 5ul) in
        let tmp2' = as_seq h1 (sub tmp 5ul 5ul) in
        let tmp3 = as_seq h0 (sub tmp 10ul 5ul) in
        let tmp4 = as_seq h0 (sub tmp 15ul 5ul) in
        let tmp3' = as_seq h1 (sub tmp 10ul 5ul) in
        let tmp4' = as_seq h1 (sub tmp 15ul 5ul) in
        let tmp5 = as_seq h0 (sub tmp 20ul 5ul) in
        let tmp6 = as_seq h0 (sub tmp 25ul 5ul) in
        let tmp5' = as_seq h1 (sub tmp 20ul 5ul) in
        let tmp6' = as_seq h1 (sub tmp 25ul 5ul) in
        seval tmp1' = Spec.Curve25519.(seval tmp4 `fsub` seval tmp1) /\
        seval tmp6' = Spec.Curve25519.(seval tmp5 `fsub` seval tmp6) /\
        seval tmp5' = Spec.Curve25519.(seval tmp5 `fadd` seval tmp2) /\
        seval tmp4' = Spec.Curve25519.(seval tmp4 `fadd` seval tmp3) /\
        red_513 tmp1' /\ red_53 tmp4' /\ red_53 tmp5' /\ red_5413 tmp6')
  ))

#reset-options "--max_fuel 0 --z3rlimit 200"

inline_for_extraction
private
let point_add_step_3 p q tmp =
  let tmp1 = sub tmp 0ul 5ul in
  let tmp2 = sub tmp 5ul 5ul in
  let tmp3 = sub tmp 10ul 5ul in
  let tmp4 = sub tmp 15ul 5ul in
  let tmp5 = sub tmp 20ul 5ul in
  let tmp6 = sub tmp 25ul 5ul in
//  let x1 = getx p in
//  let y1 = gety p in
//  let z1 = getz p in
//  let t1 = gett p in
//  let x2 = getx q in
//  let y2 = gety q in
//  let z2 = getz q in
//  let t2 = gett q in
  let h0 = ST.get() in
  (* assert(red_513 (as_seq h0 tmp5)); *)
  (* lemma_red_53_is_red_5413 (as_seq h0 tmp1); *)
  (* reduce_513 tmp1; *)
  (* let h0' = ST.get() in *)
  (* no_upd_lemma_1 h0 h0' tmp1 tmp4; *)
  (* assert(red_513 (as_seq h0' tmp1)); *)
  (* assert(red_513 (as_seq h0' tmp4)); *)
  fdifference_reduced tmp1 tmp4; // tmp1 = e
  let h1 = ST.get() in
  no_upd_lemma_1 h0 h1 tmp1 tmp5;
  no_upd_lemma_1 h0 h1 tmp1 tmp6;
  no_upd_lemma_1 h0 h1 tmp1 tmp3;
  no_upd_lemma_1 h0 h1 tmp1 tmp4;
  no_upd_lemma_1 h0 h1 tmp1 tmp2;
  fdifference tmp6 tmp5; // tmp6 = f
  let h2 = ST.get() in
  no_upd_lemma_1 h1 h2 tmp6 tmp1;
  no_upd_lemma_1 h1 h2 tmp6 tmp2;
  no_upd_lemma_1 h1 h2 tmp6 tmp3;
  no_upd_lemma_1 h1 h2 tmp6 tmp4;
  no_upd_lemma_1 h1 h2 tmp6 tmp5;
  fsum tmp5 tmp2;                // tmp5 = g
  let h3 = ST.get() in
  no_upd_lemma_1 h2 h3 tmp5 tmp1;
  no_upd_lemma_1 h2 h3 tmp5 tmp2;
  no_upd_lemma_1 h2 h3 tmp5 tmp3;
  no_upd_lemma_1 h2 h3 tmp5 tmp4;
  no_upd_lemma_1 h2 h3 tmp5 tmp6;
  fsum tmp4 tmp3;                // tmp4 = h
  ()


inline_for_extraction
private
val point_add_:
  out:point ->
  p:point{disjoint p out} ->
  q:point{disjoint q out} ->
  tmp:buffer Hacl.UInt64.t{length tmp = 30 /\ disjoint tmp p /\ disjoint tmp q /\ disjoint tmp out} ->
  Stack unit
    (requires (fun h -> live h out /\ live h p /\ live h q /\ live h tmp /\
      (
        let x1 = as_seq h (getx p) in
        let y1 = as_seq h (gety p) in
        let z1 = as_seq h (getz p) in
        let t1 = as_seq h (gett p) in
        let x2 = as_seq h (getx q) in
        let y2 = as_seq h (gety q) in
        let z2 = as_seq h (getz q) in
        let t2 = as_seq h (gett q) in
        red_513 x1 /\ red_513 y1 /\ red_513 z1 /\ red_513 t1 /\
        red_513 x2 /\ red_513 y2 /\ red_513 z2 /\ red_513 t2)
      ))
    (ensures (fun h0 _ h1 -> live h1 out /\ live h0 p /\ live h0 q /\ modifies_2 out tmp h0 h1 /\
      (
        let x1 = as_seq h0 (getx p) in
        let y1 = as_seq h0 (gety p) in
        let z1 = as_seq h0 (getz p) in
        let t1 = as_seq h0 (gett p) in
        let x2 = as_seq h0 (getx q) in
        let y2 = as_seq h0 (gety q) in
        let z2 = as_seq h0 (getz q) in
        let t2 = as_seq h0 (gett q) in
        let x3 = as_seq h1 (getx out) in
        let y3 = as_seq h1 (gety out) in
        let z3 = as_seq h1 (getz out) in
        let t3 = as_seq h1 (gett out) in
        (seval x3, seval y3, seval z3, seval t3) ==
          Spec.Ed25519.point_add (seval x1, seval y1, seval z1, seval t1)
                                 (seval x2, seval y2, seval z2, seval t2)
        /\ red_513 x3 /\ red_513 y3 /\ red_513 z3 /\ red_513 t3)
  ))

#reset-options "--max_fuel 0 --z3rlimit 500"
inline_for_extraction
private
let point_add_ out p q tmp =
  point_add_step_1 p q tmp;
  point_add_step_2 p q tmp;
  point_add_step_3 p q tmp;
  let tmp1 = sub tmp 0ul 5ul in
  let tmp2 = sub tmp 5ul 5ul in
  let tmp3 = sub tmp 10ul 5ul in
  let tmp4 = sub tmp 15ul 5ul in
  let tmp5 = sub tmp 20ul 5ul in
  let tmp6 = sub tmp 25ul 5ul in
  let x3 = getx out in
  let y3 = gety out in
  let z3 = getz out in
  let t3 = gett out in
  let h = ST.get() in
  lemma_red_513_is_red_53 (as_seq h tmp1);
  lemma_red_53_is_red_5413 (as_seq h tmp4);
  fmul x3 tmp1 tmp6;
  let h1 = ST.get() in
  no_upd_lemma_1 h h1 x3 tmp4;
  no_upd_lemma_1 h h1 x3 tmp5;
  no_upd_lemma_1 h h1 x3 tmp1;
  no_upd_lemma_1 h h1 x3 tmp6;
  fmul y3 tmp5 tmp4;
  let h2 = ST.get() in
  no_upd_lemma_1 h1 h2 y3 tmp5;
  no_upd_lemma_1 h1 h2 y3 tmp1;
  no_upd_lemma_1 h1 h2 y3 tmp6;
  no_upd_lemma_1 h1 h2 y3 tmp4;
  no_upd_lemma_1 h1 h2 y3 x3;
  fmul t3 tmp1 tmp4;
  let h3 = ST.get() in
  no_upd_lemma_1 h2 h3 t3 tmp5;
  no_upd_lemma_1 h2 h3 t3 tmp1;
  no_upd_lemma_1 h2 h3 t3 tmp6;
  no_upd_lemma_1 h2 h3 t3 y3;
  no_upd_lemma_1 h2 h3 t3 x3;
  fmul z3 tmp5 tmp6;
  let h4 = ST.get() in
  no_upd_lemma_1 h3 h4 z3 x3;
  no_upd_lemma_1 h3 h4 z3 y3;
  no_upd_lemma_1 h3 h4 z3 t3

inline_for_extraction
let point_add out p q =
  push_frame();
  let tmp = create (Hacl.Cast.uint64_to_sint64 0uL) 30ul in
  point_add_ out p q tmp;
  pop_frame()
