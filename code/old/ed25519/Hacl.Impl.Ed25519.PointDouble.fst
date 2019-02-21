module Hacl.Impl.Ed25519.PointDouble

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Buffer
open Hacl.Bignum25519
open Hacl.Impl.Ed25519.ExtPoint


#reset-options "--max_fuel 0 --z3rlimit 10"

(* Specification

let point_double (p:ext_point) : Tot ext_point =
  let x1, y1, z1, t1 = p in
  let a = x1 ** 2 in
  let b = y1 ** 2 in
  let c = 2 `fmul` (z1 ** 2) in
  let h = a `fadd` b in
  let e = h `fsub` ((x1 `fadd` y1) ** 2) in
  let g = a `fsub` b in
  let f = c `fadd` g in
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


val point_double_step_1:
  p:point ->
  tmp:buffer Hacl.UInt64.t{length tmp = 30 /\ disjoint p tmp} ->
  Stack unit
    (requires (fun h -> live h p /\ live h tmp /\
      (let x1 = as_seq h (getx p) in
       let y1 = as_seq h (gety p) in
       let z1 = as_seq h (getz p) in
       let t1 = as_seq h (gett p) in
       red_513 x1 /\ red_513 y1 /\ red_513 z1 /\ red_513 t1)))
     (ensures (fun h0 _ h1 -> live h0 p /\ live h1 tmp /\ modifies_1 tmp h0 h1 /\
       (let x1 = as_seq h0 (getx p) in
        let y1 = as_seq h0 (gety p) in
        let z1 = as_seq h0 (getz p) in
        let t1 = as_seq h0 (gett p) in
        let tmp1 = as_seq h1 (sub tmp 0ul 5ul) in
        let tmp2 = as_seq h1 (sub tmp 5ul 5ul) in
        let tmp3 = as_seq h1 (sub tmp 10ul 5ul) in
        let tmp4 = as_seq h1 (sub tmp 15ul 5ul) in
        let tmp5 = as_seq h1 (sub tmp 20ul 5ul) in
        let tmp6 = as_seq h1 (sub tmp 25ul 5ul) in
        seval tmp1 == Spec.Curve25519.(seval x1 `fmul` seval x1) /\
        seval tmp2 == Spec.Curve25519.(seval y1 `fmul` seval y1) /\
        seval tmp4 == Spec.Curve25519.(2 `fmul` (seval z1 `fmul` seval z1)) /\
        seval tmp3 == Spec.Curve25519.((seval x1 `fmul` seval x1) `fadd` (seval y1 `fmul` seval y1)) /\
        red_513 tmp3 /\ red_513 tmp1 /\ red_513 tmp2 /\ red_53 tmp4)
     ))

#reset-options "--max_fuel 0 --z3rlimit 100"

let point_double_step_1 p tmp =
  let tmp1 = sub tmp 0ul 5ul in
  let tmp2 = sub tmp 5ul 5ul in
  let tmp3 = sub tmp 10ul 5ul in
  let tmp4 = sub tmp 15ul 5ul in
  let tmp5 = sub tmp 20ul 5ul in
  let tmp6 = sub tmp 25ul 5ul in
  let x1 = getx p in
  let y1 = gety p in
  let z1 = getz p in
//  let t1 = gett p in
  let h0 = ST.get() in
  lemma_red_513_is_red_5413 (as_seq h0 x1);
  fsquare tmp1 x1; // tmp1 = a
  let h1 = ST.get() in
  no_upd_lemma_1 h0 h1 tmp1 x1;
  no_upd_lemma_1 h0 h1 tmp1 y1;
  no_upd_lemma_1 h0 h1 tmp1 z1;
//  no_upd_lemma_1 h0 h1 tmp1 t1;
  lemma_red_513_is_red_5413 (as_seq h1 y1);
  fsquare tmp2 y1; // tmp2 = b
  let h2 = ST.get() in
  no_upd_lemma_1 h1 h2 tmp2 x1;
  no_upd_lemma_1 h1 h2 tmp2 y1;
  no_upd_lemma_1 h1 h2 tmp2 z1;
//  no_upd_lemma_1 h1 h2 tmp2 t1;
  no_upd_lemma_1 h1 h2 tmp2 tmp1;
  lemma_red_513_is_red_5413 (as_seq h2 z1);
  fsquare tmp3 z1;
  let h3 = ST.get() in
  no_upd_lemma_1 h2 h3 tmp3 x1;
  no_upd_lemma_1 h2 h3 tmp3 y1;
  no_upd_lemma_1 h2 h3 tmp3 z1;
//  no_upd_lemma_1 h2 h3 tmp3 t1;
  no_upd_lemma_1 h2 h3 tmp3 tmp1;
  no_upd_lemma_1 h2 h3 tmp3 tmp2;
  times_2 tmp4 tmp3; // tmp4 = c
  let h4 = ST.get() in
  no_upd_lemma_1 h3 h4 tmp4 x1;
  no_upd_lemma_1 h3 h4 tmp4 y1;
  no_upd_lemma_1 h3 h4 tmp4 z1;
//  no_upd_lemma_1 h3 h4 tmp4 t1;
  no_upd_lemma_1 h3 h4 tmp4 tmp1;
  no_upd_lemma_1 h3 h4 tmp4 tmp2;
  no_upd_lemma_1 h3 h4 tmp4 tmp3;
  copy tmp1 tmp3; // tmp3 = a
  let h5 = ST.get() in
  no_upd_lemma_1 h4 h5 tmp3 x1;
  no_upd_lemma_1 h4 h5 tmp3 y1;
  no_upd_lemma_1 h4 h5 tmp3 z1;
//  no_upd_lemma_1 h4 h5 tmp3 t1;
  no_upd_lemma_1 h4 h5 tmp3 tmp1;
  no_upd_lemma_1 h4 h5 tmp3 tmp2;
  no_upd_lemma_1 h4 h5 tmp3 tmp4;
  fsum tmp3 tmp2; // tmp3 = h
  let h5' = ST.get() in
  lemma_red_53_is_red_5413 (as_seq h5' tmp3);
  reduce_513 tmp3;
  let h6 = ST.get() in
  no_upd_lemma_1 h5 h6 tmp3 x1;
  no_upd_lemma_1 h5 h6 tmp3 y1;
  no_upd_lemma_1 h5 h6 tmp3 z1;
//  no_upd_lemma_1 h5 h6 tmp3 t1;
  no_upd_lemma_1 h5 h6 tmp3 tmp1;
  no_upd_lemma_1 h5 h6 tmp3 tmp2;
  no_upd_lemma_1 h5 h6 tmp3 tmp4;
  ()


inline_for_extraction
private
val point_double_step_2:
  p:point ->
  tmp:buffer Hacl.UInt64.t{length tmp = 30 /\ disjoint p tmp} ->
  Stack unit
    (requires (fun h -> live h p /\ live h tmp /\
      (let x1 = as_seq h (getx p) in
       let y1 = as_seq h (gety p) in
       let z1 = as_seq h (getz p) in
       let t1 = as_seq h (gett p) in
        let tmp1 = as_seq h (sub tmp 0ul 5ul) in
        let tmp2 = as_seq h (sub tmp 5ul 5ul) in
        let tmp3 = as_seq h (sub tmp 10ul 5ul) in
        let tmp4 = as_seq h (sub tmp 15ul 5ul) in
       red_513 x1 /\ red_513 y1 /\ red_513 z1 /\ red_513 t1 /\
       red_513 tmp3 /\ red_513 tmp1 /\ red_513 tmp2 /\ red_53 tmp4
       )))
     (ensures (fun h0 _ h1 -> live h0 p /\ live h1 tmp /\ modifies_1 tmp h0 h1 /\ live h0 tmp /\
       (let x1 = as_seq h0 (getx p) in
        let y1 = as_seq h0 (gety p) in
        let z1 = as_seq h0 (getz p) in
        let t1 = as_seq h0 (gett p) in
        let tmp1 = as_seq h0 (sub tmp 0ul 5ul) in
        let tmp2 = as_seq h0 (sub tmp 5ul 5ul) in
        let tmp3 = as_seq h0 (sub tmp 10ul 5ul) in
        let tmp4 = as_seq h0 (sub tmp 15ul 5ul) in
        let tmp1' = as_seq h1 (sub tmp 0ul 5ul) in
        let tmp2' = as_seq h1 (sub tmp 5ul 5ul) in
        let tmp3' = as_seq h1 (sub tmp 10ul 5ul) in
        let tmp4' = as_seq h1 (sub tmp 15ul 5ul) in
        let tmp5' = as_seq h1 (sub tmp 20ul 5ul) in
        let tmp6' = as_seq h1 (sub tmp 25ul 5ul) in
        tmp5' == tmp3 /\
        tmp1' == tmp1 /\
        tmp3' == tmp3 /\
        seval tmp6' == Spec.Curve25519.(seval tmp3 `fsub` ((seval x1 `fadd` seval y1) `fmul` (seval x1 `fadd` seval y1))) /\
        seval tmp2' == Spec.Curve25519.(seval tmp1 `fsub` seval tmp2) /\
        seval tmp4' == Spec.Curve25519.(seval tmp4 `fadd` seval tmp2') /\
        red_513 tmp3' /\ red_513 tmp1' /\ red_513 tmp2' /\ red_53 tmp4' /\ red_513 tmp5' /\ red_5413 tmp6')
     ))

#reset-options "--max_fuel 0 --z3rlimit 100"

let point_double_step_2 p tmp =
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
  let h0 = ST.get() in
  copy x1 tmp5; // tmp5 = x1
  let h1 = ST.get() in
  no_upd_lemma_1 h0 h1 tmp5 tmp1;
  no_upd_lemma_1 h0 h1 tmp5 tmp2;
  no_upd_lemma_1 h0 h1 tmp5 tmp3;
  no_upd_lemma_1 h0 h1 tmp5 tmp4;
  no_upd_lemma_1 h0 h1 tmp5 tmp6;
  no_upd_lemma_1 h0 h1 tmp5 y1;
  fsum tmp5 y1;             // tmp5 = x1 + y1
  (* let h1' = ST.get() in *)
  (* lemma_red_53_is_red_5413 (as_seq h1' tmp5); *)
  (* reduce_513 tmp5; *)
  let h2 = ST.get() in
  no_upd_lemma_1 h1 h2 tmp5 tmp1;
  no_upd_lemma_1 h1 h2 tmp5 tmp2;
  no_upd_lemma_1 h1 h2 tmp5 tmp3;
  no_upd_lemma_1 h1 h2 tmp5 tmp4;
  no_upd_lemma_1 h1 h2 tmp5 tmp6;
  lemma_red_53_is_red_5413 (as_seq h2 tmp5);
  fsquare tmp6 tmp5;        // tmp6 = (x1 + y1) ** 2
  let h3 = ST.get() in
  no_upd_lemma_1 h2 h3 tmp6 tmp1;
  no_upd_lemma_1 h2 h3 tmp6 tmp2;
  no_upd_lemma_1 h2 h3 tmp6 tmp3;
  no_upd_lemma_1 h2 h3 tmp6 tmp4;
  no_upd_lemma_1 h2 h3 tmp6 tmp5;
  copy tmp3 tmp5; // tmp5 = h
  let h4 = ST.get() in
  no_upd_lemma_1 h3 h4 tmp5 tmp1;
  no_upd_lemma_1 h3 h4 tmp5 tmp2;
  no_upd_lemma_1 h3 h4 tmp5 tmp3;
  no_upd_lemma_1 h3 h4 tmp5 tmp4;
  no_upd_lemma_1 h3 h4 tmp5 tmp6;
  no_upd_lemma_1 h3 h4 tmp5 y1;
  fdifference tmp6 tmp5;      // tmp6 = e
  let h5 = ST.get() in
  no_upd_lemma_1 h4 h5 tmp6 tmp1;
  no_upd_lemma_1 h4 h5 tmp6 tmp2;
  no_upd_lemma_1 h4 h5 tmp6 tmp3;
  no_upd_lemma_1 h4 h5 tmp6 tmp4;
  no_upd_lemma_1 h4 h5 tmp6 tmp5;
  no_upd_lemma_1 h4 h5 tmp6 y1;
  fdifference_reduced tmp2 tmp1;      // tmp2 = g
  let h6 = ST.get() in
  no_upd_lemma_1 h5 h6 tmp2 tmp1;
  no_upd_lemma_1 h5 h6 tmp2 tmp3;
  no_upd_lemma_1 h5 h6 tmp2 tmp4;
  no_upd_lemma_1 h5 h6 tmp2 tmp5;
  no_upd_lemma_1 h5 h6 tmp2 tmp6;
  no_upd_lemma_1 h5 h6 tmp2 y1;
  lemma_red_53_is_red_5413 (as_seq h6 tmp4);
  reduce_513 tmp4;
  let h6' = ST.get() in
  no_upd_lemma_1 h6 h6' tmp4 tmp2;
  fsum tmp4 tmp2;             // tmp4 = f
  let h7 = ST.get() in
  no_upd_lemma_1 h6 h7 tmp4 tmp1;
  no_upd_lemma_1 h6 h7 tmp4 tmp2;
  no_upd_lemma_1 h6 h7 tmp4 tmp3;
  no_upd_lemma_1 h6 h7 tmp4 tmp5;
  no_upd_lemma_1 h6 h7 tmp4 tmp6;
  no_upd_lemma_1 h6 h7 tmp4 y1;
  ()


val point_double_:
  out:point ->
  p:point{disjoint out p} ->
  tmp:buffer Hacl.UInt64.t{length tmp = 30 /\ disjoint tmp p /\ disjoint tmp out} ->
  Stack unit
    (requires (fun h -> live h out /\ live h p /\ live h tmp /\
      (
        let x1 = as_seq h (getx p) in
        let y1 = as_seq h (gety p) in
        let z1 = as_seq h (getz p) in
        let t1 = as_seq h (gett p) in
        red_513 x1 /\ red_513 y1 /\ red_513 z1 /\ red_513 t1)))
    (ensures (fun h0 _ h1 -> live h1 out /\ live h0 p /\ modifies_2 out tmp h0 h1 /\
      ( let x1 = as_seq h0 (getx p) in
        let y1 = as_seq h0 (gety p) in
        let z1 = as_seq h0 (getz p) in
        let t1 = as_seq h0 (gett p) in
        let x3 = as_seq h1 (getx out) in
        let y3 = as_seq h1 (gety out) in
        let z3 = as_seq h1 (getz out) in
        let t3 = as_seq h1 (gett out) in
        (seval x3, seval y3, seval z3, seval t3) ==
          Spec.Ed25519.point_double (seval x1, seval y1, seval z1, seval t1)
        /\ red_513 x3 /\ red_513 y3 /\ red_513 z3 /\ red_513 t3)
   ))

#reset-options "--max_fuel 0 --z3rlimit 200"

let point_double_ out p tmp =
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
  point_double_step_1 p tmp;
  point_double_step_2 p tmp;
  let h0 = ST.get() in
  lemma_red_513_is_red_53 (as_seq h0 tmp2);
  lemma_red_513_is_red_5413 (as_seq h0 tmp2);
  lemma_red_513_is_red_53 (as_seq h0 tmp3);
  lemma_red_513_is_red_5413 (as_seq h0 tmp3);
  fmul x3 tmp4 tmp6;
  let h1 = ST.get() in
  no_upd_lemma_1 h0 h1 x3 tmp2;
  no_upd_lemma_1 h0 h1 x3 tmp3;
  no_upd_lemma_1 h0 h1 x3 tmp4;
  no_upd_lemma_1 h0 h1 x3 tmp6;
  fmul y3 tmp2 tmp3;
  let h2 = ST.get() in
  no_upd_lemma_1 h1 h2 y3 tmp2;
  no_upd_lemma_1 h1 h2 y3 tmp3;
  no_upd_lemma_1 h1 h2 y3 tmp4;
  no_upd_lemma_1 h1 h2 y3 tmp6;
  no_upd_lemma_1 h1 h2 y3 x3;
  fmul t3 tmp3 tmp6;
  let h3 = ST.get() in
  no_upd_lemma_1 h2 h3 t3 tmp2;
  no_upd_lemma_1 h2 h3 t3 tmp4;
  no_upd_lemma_1 h2 h3 t3 x3;
  no_upd_lemma_1 h2 h3 t3 y3;
  fmul z3 tmp4 tmp2;
  let h4 = ST.get() in
  no_upd_lemma_1 h3 h4 z3 x3;
  no_upd_lemma_1 h3 h4 z3 y3;
  no_upd_lemma_1 h3 h4 z3 t3;
  ()


#reset-options "--max_fuel 0 --z3rlimit 200"

let point_double out p =
  push_frame();
  let tmp = create (Hacl.Cast.uint64_to_sint64 0uL) 30ul in
  point_double_ out p tmp;
  pop_frame()
