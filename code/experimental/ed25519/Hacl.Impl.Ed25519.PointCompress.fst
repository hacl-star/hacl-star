module Hacl.Impl.Ed25519.PointCompress

open FStar.Buffer
open Hacl.UInt64
open Hacl.Bignum25519


#reset-options "--max_fuel 0 --z3rlimit 20"

let hint8_p = buffer Hacl.UInt8.t
let hint64_p = buffer Hacl.UInt64.t
let op_String_Access h b = Hacl.Spec.Endianness.reveal_sbytes (as_seq h b)

open FStar.Mul

private let lemma_distr_4 a b c d e : Lemma (a * (b + c + d + e) == a * b + a * c + a * d + a * e)
  = ()


#reset-options "--max_fuel 0 --z3rlimit 20"

private let lemma_x_mod_2 (a:nat) (b:nat) (c:nat) (d:nat) (e:nat) : 
  Lemma ((a + pow2 51 * b + pow2 102 * c + pow2 153 * d + pow2 204 * e) % 2 = a % 2)
  = assert_norm(pow2 51 = 2 * pow2 50);
    assert_norm(pow2 102 = 2 * pow2 101);
    assert_norm(pow2 153 = 2 * pow2 152);
    assert_norm(pow2 204 = 2 * pow2 203);
    lemma_distr_4 2 (pow2 50 * b) (pow2 101 * c) (pow2 152 * d) (pow2 203 * e);
    Math.Lemmas.paren_mul_right 2 (pow2 50) b;
    Math.Lemmas.paren_mul_right 2 (pow2 101) c;
    Math.Lemmas.paren_mul_right 2 (pow2 152) d;
    Math.Lemmas.paren_mul_right 2 (pow2 203) e;
    Math.Lemmas.modulo_addition_lemma a 2 ((pow2 50 * b)+(pow2 101 * c)+(pow2 152 * d)+(pow2 203 * e))

private val x_mod_2:
  x:felem ->
  Stack Hacl.UInt64.t
    (requires (fun h -> live h x /\ red_51 (as_seq h x) /\
      (let s = as_seq h x in
       FStar.Mul.(Hacl.UInt64.(v (Seq.index s 0)
                               + pow2 51 * v (Seq.index s 1)
                               + pow2 102 * v (Seq.index s 2)
                               + pow2 153 * v (Seq.index s 3)
                               + pow2 204 * v (Seq.index s 4) == seval (as_seq h x))))))
    (ensures (fun h0 z h1 -> h0 == h1 /\ live h0 x /\
      v z = seval (as_seq h0 x) % 2))
let x_mod_2 x =
  let h = ST.get() in
  lemma_x_mod_2 (v (get h x 0)) (v (get h x 1)) (v (get h x 2)) (v (get h x 3)) (v (get h x 4));
  let x0 = x.(0ul) in
  let z  = x0 &^ 1uL in
  assert_norm(pow2 1 = 2);
  UInt.logand_mask (v x0) 1;
  z


val point_compress:
  out:hint8_p{length out = 32} ->
  p:Hacl.Impl.Ed25519.ExtPoint.point ->
  Stack unit
    (requires (fun h -> live h out /\ live h p))
    (ensures (fun h0 _ h1 -> live h0 out /\ live h0 p /\ 
      live h1 out /\ modifies_1 out h0 h1 /\
      h1.[out] == Spec.point_compress (Hacl.Impl.Ed25519.ExtPoint.as_point h0 p)
    ))
let point_compress out p =
  push_frame();
  let tmp  = create (Hacl.Cast.uint64_to_sint64 0uL) 15ul in
  let zinv = Buffer.sub tmp 0ul  5ul in
  let x    = Buffer.sub tmp 5ul  5ul in
  let out  = Buffer.sub tmp 10ul 5ul in
  let px   = Hacl.Impl.Ed25519.ExtPoint.getx p in
  let py   = Hacl.Impl.Ed25519.ExtPoint.gety p in
  let pz   = Hacl.Impl.Ed25519.ExtPoint.getz p in
  Hacl.Bignum25519.inverse  zinv pz;
  Hacl.Bignum25519.fmul x   px zinv;
  Hacl.Bignum25519.reduce x;
  Hacl.Bignum25519.fmul out py zinv;
  Hacl.Bignum25519.reduce out;
  let b = x.(0ul) &^ 1uL in
  let out4 = out.(4ul) in
  out.(4ul) <- out4 +^ (b <<^ 51ul);
  pop_frame()
