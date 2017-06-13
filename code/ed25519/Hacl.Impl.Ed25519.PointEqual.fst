module Hacl.Impl.Ed25519.PointEqual

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.Buffer
open FStar.UInt32


#reset-options "--max_fuel 0 --z3rlimit 100"

val lemma_pos:
  a:nat -> b:pos -> c:nat -> d:pos -> e:nat -> f:pos -> g:nat -> h:pos -> i:nat -> 
  Lemma (a + b * c + d * e + f * g + h * i >= 0)
let lemma_pos a b c d e f g h i = ()

open Hacl.UInt64

val lemma_pos':
  s:Seq.seq Hacl.UInt64.t{Seq.length s = 5} ->
  Lemma (v (Seq.index s 0) + pow2 51 * v (Seq.index s 1) + pow2 102 * v (Seq.index s 2) + pow2 153 * v (Seq.index s 3) + pow2 204 * v (Seq.index s 4) >= 0)
let lemma_pos' s =
  lemma_pos (v (Seq.index s 0)) (pow2 51) (v (Seq.index s 1)) (pow2 102) (v (Seq.index s 2)) (pow2 153) (v (Seq.index s 3)) (pow2 204) (v (Seq.index s 4))


let uint8_p = buffer UInt8.t
let felem   = b:buffer UInt64.t{length b = 5}

#reset-options "--max_fuel 0 --z3rlimit 200"

let gte_q s =
  let h0 = ST.get() in
  assert_norm(pow2 64 = 0x10000000000000000);
  let s0 = s.(0ul) in
  let s1 = s.(1ul) in
  let s2 = s.(2ul) in
  let s3 = s.(3ul) in
  let s4 = s.(4ul) in
  let open FStar.UInt64 in
       if s4 >^ 0x00000010000000uL then true
  else if s4 <^ 0x00000010000000uL then false
  else if s3 >^ 0x00000000000000uL then true
  else if s2 >^ 0x000000000014deuL then true
  else if s2 <^ 0x000000000014deuL then false
  else if s1 >^ 0xf9dea2f79cd658uL then true
  else if s1 <^ 0xf9dea2f79cd658uL then false
  else if s0 >=^ 0x12631a5cf5d3eduL then true
  else false

#reset-options "--max_fuel 0 --z3rlimit 20"

val eq:
  a:felem ->
  b:felem ->
  Stack bool
    (requires (fun h -> live h a /\ live h b /\ Hacl.Bignum25519.red_51 (as_seq h a) /\ Hacl.Bignum25519.red_51 (as_seq h b) /\
      (let a = as_seq h a in let b = as_seq h b in
       (Hacl.UInt64.(v (Seq.index a 0)+ pow2 51 * v (Seq.index a 1) + pow2 102 * v (Seq.index a 2)
                     + pow2 153 * v (Seq.index a 3) + pow2 204 * v (Seq.index a 4)
                     < Spec.Curve25519.prime)) /\
      (Hacl.UInt64.(v (Seq.index b 0) + pow2 51 * v (Seq.index b 1) + pow2 102 * v (Seq.index b 2)
                     + pow2 153 * v (Seq.index b 3) + pow2 204 * v (Seq.index b 4) < Spec.Curve25519.prime)))))
    (ensures (fun h0 r h1 -> live h0 a /\ live h0 b /\ h0 == h1 /\
      (r <==> Hacl.Bignum25519.seval (as_seq h0 b) == Hacl.Bignum25519.seval (as_seq h0 a))))

#reset-options "--max_fuel 0 --z3rlimit 500"

open Hacl.UInt64

let eq a b =
  assert_norm(pow2 51 = 0x8000000000000);
  assert_norm(pow2 102 = 0x40000000000000000000000000);
  assert_norm(pow2 153 = 0x200000000000000000000000000000000000000);
  assert_norm(pow2 204 = 0x1000000000000000000000000000000000000000000000000000);
  assert_norm(pow2 255 - 19 = 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed);
  let h = ST.get() in
  Hacl.Bignum25519.lemma_reveal_red_51 (as_seq h a);
  Hacl.Bignum25519.lemma_reveal_red_51 (as_seq h b);
  Hacl.Bignum25519.lemma_reveal_seval (as_seq h a);
  Hacl.Bignum25519.lemma_reveal_seval (as_seq h b);
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
  Hacl.Impl.Ed25519.Verify.Lemmas.lemma_equality (v a0) (v a1) (v a2) (v a3) (v a4) (v b0) (v b1) (v b2) (v b3) (v b4);
  let z = FStar.UInt64.(a0 =^ b0 && a1 =^ b1 && a2 =^ b2 && a3 =^ b3 && a4 =^ b4) in
  let h = ST.get() in
  Seq.lemma_eq_intro (as_seq h a) (if z then as_seq h b else as_seq h a);
  z


open Hacl.Impl.Ed25519.ExtPoint
open Hacl.Impl.Ed25519.Ladder.Step


val point_equal_1:
  p:Hacl.Impl.Ed25519.ExtPoint.point ->
  q:Hacl.Impl.Ed25519.ExtPoint.point ->
  tmp:buffer Hacl.UInt64.t{length tmp = 20 /\ disjoint tmp p /\ disjoint tmp q} ->
  Stack bool
    (requires (fun h -> live h p /\ live h q /\ point_inv h p /\ point_inv h q /\ live h tmp))
    (ensures (fun h0 z h1 -> live h0 p /\ live h0 q /\ live h1 tmp /\ modifies_1 tmp h0 h1 /\ (
      let px, py, pz, pt = as_point h0 p in
      let qx, qy, qz, qt = as_point h0 q in
      z == Spec.Curve25519.(if ((px `fmul` qz) <> (qx `fmul` pz)) then false else true)) ))

let point_equal_1 p q tmp =
  assert_norm(pow2 51 = 0x8000000000000);
  let pxqz = Buffer.sub tmp 0ul 5ul in
  let qxpz = Buffer.sub tmp 5ul 5ul in
  let pyqz = Buffer.sub tmp 10ul 5ul in
  let qypz = Buffer.sub tmp 15ul 5ul in
  let h0 = ST.get() in
  Hacl.Bignum25519.lemma_red_513_is_red_53 (as_seq h0 (getx p));
  Hacl.Bignum25519.lemma_red_513_is_red_53 (as_seq h0 (gety p));
  Hacl.Bignum25519.lemma_red_513_is_red_5413 (as_seq h0 (getz p));
  Hacl.Bignum25519.lemma_red_513_is_red_53 (as_seq h0 (getx q));
  Hacl.Bignum25519.lemma_red_513_is_red_53 (as_seq h0 (gety q));
  Hacl.Bignum25519.lemma_red_513_is_red_5413 (as_seq h0 (getz q));
  Hacl.Bignum25519.fmul pxqz (Hacl.Impl.Ed25519.ExtPoint.getx p) (Hacl.Impl.Ed25519.ExtPoint.getz q);
  let h0'  = ST.get() in
  assert(Hacl.Bignum25519.seval (as_seq h0' pxqz) == Spec.Curve25519.(Hacl.Bignum25519.seval (as_seq h0 (getx p)) `fmul` Hacl.Bignum25519.seval (as_seq h0 (getz q))));
  Hacl.Bignum25519.reduce pxqz;
  let h1 = ST.get() in
  Hacl.Bignum25519.lemma_reveal_seval (as_seq h1 pxqz);
  lemma_pos' (as_seq h1 pxqz);
  Math.Lemmas.modulo_lemma (let s = as_seq h1 pxqz in Hacl.UInt64.(v (Seq.index s 0)
                               + pow2 51 * v (Seq.index s 1)
                               + pow2 102 * v (Seq.index s 2)
                               + pow2 153 * v (Seq.index s 3)
                               + pow2 204 * v (Seq.index s 4))) Spec.Curve25519.prime;
  no_upd_lemma_1 h0 h1 pxqz (getx p);
  no_upd_lemma_1 h0 h1 pxqz (gety p);
  no_upd_lemma_1 h0 h1 pxqz (getz p);
  no_upd_lemma_1 h0 h1 pxqz (getx q);
  no_upd_lemma_1 h0 h1 pxqz (gety q);
  no_upd_lemma_1 h0 h1 pxqz (getz q);
  Hacl.Bignum25519.fmul qxpz (Hacl.Impl.Ed25519.ExtPoint.getx q) (Hacl.Impl.Ed25519.ExtPoint.getz p);
  let h1' = ST.get() in
  Hacl.Bignum25519.lemma_reveal_seval (as_seq h1' qxpz);  
  Hacl.Bignum25519.reduce qxpz;
  let h2 = ST.get() in
  Hacl.Bignum25519.lemma_reveal_seval (as_seq h2 qxpz);
  lemma_pos' (as_seq h2 qxpz);
  Math.Lemmas.modulo_lemma (let s = as_seq h2 qxpz in Hacl.UInt64.(v (Seq.index s 0)
                               + pow2 51 * v (Seq.index s 1)
                               + pow2 102 * v (Seq.index s 2)
                               + pow2 153 * v (Seq.index s 3)
                               + pow2 204 * v (Seq.index s 4))) Spec.Curve25519.prime;
  no_upd_lemma_1 h1 h2 qxpz (getx p);
  no_upd_lemma_1 h1 h2 qxpz (gety p);
  no_upd_lemma_1 h1 h2 qxpz (getz p);
  no_upd_lemma_1 h1 h2 qxpz (getx q);
  no_upd_lemma_1 h1 h2 qxpz (gety q);
  no_upd_lemma_1 h1 h2 qxpz (getz q);
  no_upd_lemma_1 h1 h2 qxpz pxqz;
  let b = eq pxqz qxpz in
  b


val point_equal_2:
  p:Hacl.Impl.Ed25519.ExtPoint.point ->
  q:Hacl.Impl.Ed25519.ExtPoint.point ->
  tmp:buffer Hacl.UInt64.t{length tmp = 20 /\ disjoint tmp p /\ disjoint tmp q} ->
  Stack bool
    (requires (fun h -> live h p /\ live h q /\ point_inv h p /\ point_inv h q /\ live h tmp))
    (ensures (fun h0 z h1 -> live h0 p /\ live h0 q /\ live h1 tmp /\ modifies_1 tmp h0 h1 /\ (
      let px, py, pz, pt = as_point h0 p in
      let qx, qy, qz, qt = as_point h0 q in
      z == Spec.Curve25519.(if ((py `fmul` qz) <> (qy `fmul` pz)) then false else true)) ))

let point_equal_2 p q tmp =
  assert_norm(pow2 51 = 0x8000000000000);
  let pxqz = Buffer.sub tmp 0ul 5ul in
  let qxpz = Buffer.sub tmp 5ul 5ul in
  let pyqz = Buffer.sub tmp 10ul 5ul in
  let qypz = Buffer.sub tmp 15ul 5ul in
  let h0 = ST.get() in
  Hacl.Bignum25519.lemma_red_513_is_red_53 (as_seq h0 (getx p));
  Hacl.Bignum25519.lemma_red_513_is_red_53 (as_seq h0 (gety p));
  Hacl.Bignum25519.lemma_red_513_is_red_5413 (as_seq h0 (getz p));
  Hacl.Bignum25519.lemma_red_513_is_red_53 (as_seq h0 (getx q));
  Hacl.Bignum25519.lemma_red_513_is_red_53 (as_seq h0 (gety q));
  Hacl.Bignum25519.lemma_red_513_is_red_5413 (as_seq h0 (getz q));
  Hacl.Bignum25519.fmul pyqz (Hacl.Impl.Ed25519.ExtPoint.gety p) (Hacl.Impl.Ed25519.ExtPoint.getz q);
  let h0'  = ST.get() in
  assert(Hacl.Bignum25519.seval (as_seq h0' pyqz) == Spec.Curve25519.(Hacl.Bignum25519.seval (as_seq h0 (gety p)) `fmul` Hacl.Bignum25519.seval (as_seq h0 (getz q))));
  Hacl.Bignum25519.reduce pyqz;
  let h1 = ST.get() in
  Hacl.Bignum25519.lemma_reveal_seval (as_seq h1 pyqz);
  lemma_pos' (as_seq h1 pyqz);  
  Math.Lemmas.modulo_lemma (let s = as_seq h1 pyqz in Hacl.UInt64.(v (Seq.index s 0)
                               + pow2 51 * v (Seq.index s 1)
                               + pow2 102 * v (Seq.index s 2)
                               + pow2 153 * v (Seq.index s 3)
                               + pow2 204 * v (Seq.index s 4))) Spec.Curve25519.prime;
  no_upd_lemma_1 h0 h1 pyqz (getx p);
  no_upd_lemma_1 h0 h1 pyqz (gety p);
  no_upd_lemma_1 h0 h1 pyqz (getz p);
  no_upd_lemma_1 h0 h1 pyqz (getx q);
  no_upd_lemma_1 h0 h1 pyqz (gety q);
  no_upd_lemma_1 h0 h1 pyqz (getz q);
  Hacl.Bignum25519.fmul qypz (Hacl.Impl.Ed25519.ExtPoint.gety q) (Hacl.Impl.Ed25519.ExtPoint.getz p);
  let h1' = ST.get() in
  Hacl.Bignum25519.lemma_reveal_seval (as_seq h1' qypz);  
  Hacl.Bignum25519.reduce qypz;
  let h2 = ST.get() in
  Hacl.Bignum25519.lemma_reveal_seval (as_seq h2 qypz);
  lemma_pos' (as_seq h2 qypz);  
  Math.Lemmas.modulo_lemma (let s = as_seq h2 qypz in Hacl.UInt64.(v (Seq.index s 0)
                               + pow2 51 * v (Seq.index s 1)
                               + pow2 102 * v (Seq.index s 2)
                               + pow2 153 * v (Seq.index s 3)
                               + pow2 204 * v (Seq.index s 4))) Spec.Curve25519.prime;
  no_upd_lemma_1 h1 h2 qypz (getx p);
  no_upd_lemma_1 h1 h2 qypz (gety p);
  no_upd_lemma_1 h1 h2 qypz (getz p);
  no_upd_lemma_1 h1 h2 qypz (getx q);
  no_upd_lemma_1 h1 h2 qypz (gety q);
  no_upd_lemma_1 h1 h2 qypz (getz q);
  no_upd_lemma_1 h1 h2 qypz pxqz;
  let b = eq pyqz qypz in
  b


val point_equal_:
  p:Hacl.Impl.Ed25519.ExtPoint.point ->
  q:Hacl.Impl.Ed25519.ExtPoint.point ->
  tmp:buffer Hacl.UInt64.t{length tmp = 20 /\ disjoint tmp p /\ disjoint tmp q} ->
  Stack bool
    (requires (fun h -> live h p /\ live h q /\ point_inv h p /\ point_inv h q /\ live h tmp))
    (ensures (fun h0 z h1 -> live h0 p /\ live h0 q /\ modifies_1 tmp h0 h1 /\ live h1 tmp /\
      z == Spec.Ed25519.point_equal (as_point h0 p) (as_point h0 q) ))

#reset-options "--max_fuel 0 --z3rlimit 200"

val lemma_point_inv:
  h:HyperStack.mem -> p:point{live h p} -> h':HyperStack.mem -> p':point{live h' p'} ->
  Lemma (requires (as_seq h p == as_seq h' p' /\ point_inv h p))
        (ensures (point_inv h' p'))
let lemma_point_inv h p h' p' = ()

#reset-options "--max_fuel 0 --z3rlimit 100"

let point_equal_ p q tmp =
  let h0 = ST.get() in
  let b = point_equal_1 p q tmp in
  let h1 = ST.get() in
  no_upd_lemma_1 h0 h1 tmp p;
  no_upd_lemma_1 h0 h1 tmp q;
  lemma_point_inv h0 p h1 p;
  lemma_point_inv h0 q h1 q;
  if b = true then
    point_equal_2 p q tmp
  else false


let point_equal p q =
  push_frame();
  let tmp = create 0uL 20ul in
  let res = point_equal_ p q tmp in
  pop_frame();
  res
