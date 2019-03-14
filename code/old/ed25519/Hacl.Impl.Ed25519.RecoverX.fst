module Hacl.Impl.Ed25519.RecoverX

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Buffer
open FStar.UInt64
open Hacl.Bignum25519

#reset-options "--max_fuel 0 --z3rlimit 20"


open FStar.Mul

private
let norm h (x:elemB{live h x}) : GTot Type0 =
  live h x /\ red_51 (as_seq h x) /\ (let s = as_seq h x in
  v (Seq.index s 0) + pow2 51 * v (Seq.index s 1) + pow2 102 * v (Seq.index s 2) + pow2 153 * v (Seq.index s 3) + pow2 204 * v (Seq.index s 4) < Spec.Curve25519.prime)


inline_for_extraction
private
val make_zero:
  b:elemB ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1 /\ seval (as_seq h1 b) == 0
      /\ norm h1 b
      /\ Hacl.Bignum25519.red_513 (as_seq h1 b)))
let make_zero b =
  let zero = Hacl.Cast.uint64_to_sint64 0uL in
  Hacl.Lib.Create64.make_h64_5 b zero zero zero zero zero;
  let h = ST.get() in
  lemma_reveal_seval (as_seq h b);
  assert_norm(pow2 51 = 0x8000000000000);
  lemma_intro_red_51 (as_seq h b);
  lemma_red_51_is_red_513 (as_seq h b)


inline_for_extraction
private
val make_one:
  b:elemB ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1 /\ seval (as_seq h1 b) == 1
      /\ Hacl.Bignum25519.red_513 (as_seq h1 b)))
let make_one b =
  let zero = Hacl.Cast.uint64_to_sint64 0uL in
  let one  = Hacl.Cast.uint64_to_sint64 1uL in
  Hacl.Lib.Create64.make_h64_5 b one zero zero zero zero;
  let h = ST.get() in
  lemma_reveal_seval (as_seq h b);
  assert_norm(pow2 51 = 0x8000000000000);
  lemma_intro_red_51 (as_seq h b);
  lemma_red_51_is_red_513 (as_seq h b)


#reset-options "--max_fuel 0 --z3rlimit 20"

inline_for_extraction
private
val recover_x_step_1:
  x2:elemB ->
  y:elemB{disjoint x2 y} ->
  Stack unit
    (requires (fun h -> live h x2 /\ live h y /\ red_51 (as_seq h y)))
    (ensures (fun h0 _ h1 -> live h1 x2 /\ live h0 y /\ modifies_1 x2 h0 h1 /\
      (let s = as_seq h1 x2 in
       red_51 s /\
       FStar.Mul.(Hacl.UInt64.(v (Seq.index s 0)
                               + pow2 51 * v (Seq.index s 1)
                               + pow2 102 * v (Seq.index s 2)
                               + pow2 153 * v (Seq.index s 3)
                               + pow2 204 * v (Seq.index s 4) < Spec.Curve25519.prime))) /\
      (let y = seval (as_seq h0 y) in
       let x2 = seval (as_seq h1 x2) in
       Spec.Ed25519.(Spec.Curve25519.(
         x2 == ((y `fmul` y) `fsub` 1) `fmul` (modp_inv ((d `fmul` (y `fmul` y)) `fadd` one)))))))
#reset-options "--max_fuel 0 --z3rlimit 200"
let recover_x_step_1 x2 y =
  (**) let hinit = ST.get() in
  push_frame();
  (**) let h = ST.get() in
  let tmp = create (Hacl.Cast.uint64_to_sint64 0uL) 25ul in
  (**) let h' = ST.get() in
  let one = Buffer.sub tmp 0ul 5ul in
  let y2  = Buffer.sub tmp 5ul 5ul in
  let dyyi = Buffer.sub tmp 10ul 5ul in
  let dyy = Buffer.sub tmp 15ul 5ul in
  let h0 = ST.get() in
  make_one one;
  (**) let h1 = ST.get() in
  (**) modifies_subbuffer_1 h0 h1 one tmp;
  (**) lemma_red_51_is_red_5413 (as_seq h1 y);
  Hacl.Bignum25519.fsquare y2 y; // y2 = y `fmul` y
  (**) let h1' = ST.get() in
  (**) modifies_subbuffer_1 h1 h1' y2 tmp;
  (**) lemma_modifies_1_trans tmp h0 h1 h1';
  Hacl.Bignum25519.times_d dyy y2; // dyy = d `fmul` (y `fmul` y)
  (**) let h1'' = ST.get() in
  (**) modifies_subbuffer_1 h1' h1'' dyy tmp;
  (**) lemma_modifies_1_trans tmp h0 h1' h1'';
  
  Hacl.Bignum25519.fsum dyy one;   // dyy = (d `fmul` (y `fmul` y)) `fadd` one
  let h4 = ST.get() in
  (**) modifies_subbuffer_1 h1'' h4 dyy tmp;
  (**) lemma_modifies_1_trans tmp h0 h1'' h4;
  (**) lemma_red_53_is_red_5413 (as_seq h4 dyy);
  Hacl.Bignum25519.reduce_513 dyy;
  (**) let h5 = ST.get() in
  (**) modifies_subbuffer_1 h4 h5 dyy tmp;
  (**) lemma_modifies_1_trans tmp h0 h4 h5;
  Hacl.Bignum25519.inverse dyyi dyy; // dyyi = modp_inv ((d `fmul` (y `fmul` y)) `fadd` one)
  (**) let h6 = ST.get() in
  (**) modifies_subbuffer_1 h5 h6 dyyi tmp;
  (**) lemma_modifies_1_trans tmp h0 h5 h6;
  Hacl.Bignum25519.fdifference one y2; // one = (y `fmul` y) `fsub` 1
  (**) let h7 = ST.get() in
  (**) modifies_subbuffer_1 h6 h7 one tmp;
  (**) lemma_modifies_1_trans tmp h0 h6 h7;
  (**) lemma_modifies_0_1' tmp h h0 h7;
  (**) lemma_red_513_is_red_53 (as_seq h7 dyyi);
  Hacl.Bignum25519.fmul x2 dyyi one; //
  (**) let h8 = ST.get() in
  Hacl.Bignum25519.reduce x2;
  (**) let h9 = ST.get() in
  (**) lemma_modifies_1_trans x2 h7 h8 h9;
  (**) lemma_modifies_0_1 x2 h h7 h9;
  pop_frame();
  (**) let hfin = ST.get() in
  (**) modifies_popped_1 x2 hinit h h9 hfin


#reset-options "--max_fuel 0 --z3rlimit 20"

private
val is_0:
  x:elemB ->
  Stack bool
    (requires (fun h -> live h x /\ Hacl.Bignum25519.red_51 (as_seq h x) /\
      (let s = as_seq h x in
       FStar.Mul.(v (Seq.index s 0) + pow2 51 * v (Seq.index s 1)
                  + pow2 102 * v (Seq.index s 2) + pow2 153 * v (Seq.index s 3)
                  + pow2 204 * v (Seq.index s 4) < Spec.Curve25519.prime)) ))
    (ensures (fun h0 b h1 -> h0 == h1 /\ live h0 x /\
      (b <==> (seval (as_seq h0 x) = 0))))
#reset-options "--max_fuel 0 --z3rlimit 200"
let is_0 x =
  let x0 = x.(0ul) in
  let x1 = x.(1ul) in
  let x2 = x.(2ul) in
  let x3 = x.(3ul) in
  let x4 = x.(4ul) in
  let h = ST.get() in
  lemma_reveal_seval (as_seq h x);
  Math.Lemmas.modulo_lemma (let s = as_seq h x in
       FStar.Mul.(v (Seq.index s 0) + pow2 51 * v (Seq.index s 1)
                  + pow2 102 * v (Seq.index s 2) + pow2 153 * v (Seq.index s 3)
                  + pow2 204 * v (Seq.index s 4))) Spec.Curve25519.prime;
  FStar.UInt64.(x0 =^ 0uL && x1 =^ 0uL && x2 =^ 0uL && x3 =^ 0uL && x4 =^ 0uL)


#reset-options "--max_fuel 0 --z3rlimit 20"

inline_for_extraction
private
val mul_modp_sqrt_m1:
  x:elemB ->
  Stack unit
    (requires (fun h -> live h x /\ red_513 (as_seq h x) ))
    (ensures (fun h0 _ h1 -> live h1 x /\ live h0 x /\ modifies_1 x h0 h1
      /\ red_513 (as_seq h0 x) /\ red_513 (as_seq h1 x) /\
      seval (as_seq h1 x)
      == Spec.Curve25519.(seval (as_seq h0 x) `fmul` (Spec.Ed25519.modp_sqrt_m1))
    ))
#reset-options "--max_fuel 0 --z3rlimit 200"
let mul_modp_sqrt_m1 x =
  let open FStar.Mul in
  assert_norm(pow2 51 = 0x8000000000000);
  assert_norm((0x00061b274a0ea0b0 + pow2 51 * 0x0000d5a5fc8f189d + pow2 102 *  0x0007ef5e9cbd0c60 + pow2 153 *  0x00078595a6804c9e + pow2 204 * 0x0002b8324804fc1d) % (pow2 255 - 19) = Spec.Ed25519.modp_sqrt_m1);
  let h0 = ST.get() in
  push_frame();
  let h0' = ST.get() in
  let sqrt_m1 = create 0uL 5ul in
  let h0'' = ST.get() in
  Hacl.Lib.Create64.make_h64_5 sqrt_m1 0x00061b274a0ea0b0uL 0x0000d5a5fc8f189duL 0x0007ef5e9cbd0c60uL 0x00078595a6804c9euL 0x0002b8324804fc1duL;
  let h = ST.get() in
  lemma_modifies_0_1' sqrt_m1 h0' h0'' h;
  no_upd_fresh h0 h0' x;
  no_upd_lemma_0 h0' h x;
  lemma_intro_red_51 (as_seq h sqrt_m1);
  lemma_reveal_seval (as_seq h sqrt_m1);
  assert(seval (as_seq h sqrt_m1) = Spec.Ed25519.modp_sqrt_m1);
  lemma_red_513_is_red_53 (as_seq h x);
  lemma_red_51_is_red_5413 (as_seq h sqrt_m1);
  Hacl.Bignum25519.fmul x x sqrt_m1;
  pop_frame()


#reset-options "--max_fuel 0 --z3rlimit 100"

inline_for_extraction
private
val gte_q:
  x:elemB ->
  Stack bool
    (requires (fun h -> live h x /\ red_51 (as_seq h x)))
    (ensures (fun h0 b h1 -> live h0 x /\ h0 == h1
     /\ (b <==> (let s = as_seq h0 x in
       FStar.Mul.(v (Seq.index s 0) + pow2 51 * v (Seq.index s 1)
                  + pow2 102 * v (Seq.index s 2) + pow2 153 * v (Seq.index s 3)
                  + pow2 204 * v (Seq.index s 4)) >= pow2 255 - 19)) ))
let gte_q x =
  let h = ST.get() in
  lemma_reveal_red_51 (as_seq h x);
  assert_norm(pow2 51 = 0x8000000000000);
  assert_norm(pow2 102 = 0x40000000000000000000000000);
  assert_norm(pow2 153 = 0x200000000000000000000000000000000000000);
  assert_norm(pow2 204 = 0x1000000000000000000000000000000000000000000000000000);
  assert_norm(pow2 255 - 19 = 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed);
  let x0 = x.(0ul) in
  let x1 = x.(1ul) in
  let x2 = x.(2ul) in
  let x3 = x.(3ul) in
  let x4 = x.(4ul) in
  FStar.UInt64.(x0 >=^ 0x7ffffffffffeduL && x1 =^ 0x7ffffffffffffuL && x2 =^ 0x7ffffffffffffuL && x3 =^ 0x7ffffffffffffuL && x4 =^ 0x7ffffffffffffuL)


open FStar.Mul

inline_for_extraction
private
val copy:
  src:elemB ->
  dest:elemB{disjoint src dest} ->
  Stack unit
    (requires (fun h -> live h src /\ live h dest))
    (ensures (fun h0 _ h1 -> live h0 src /\ live h1 dest /\ modifies_1 dest h0 h1 /\
      as_seq h1 dest == as_seq h0 src))
let copy src dest =
  let h0 = ST.get() in
  blit src 0ul dest 0ul 5ul;
  let h1 = ST.get() in
  Seq.lemma_eq_intro (Seq.slice (as_seq h0 src) 0 5) (as_seq h0 src);
  Seq.lemma_eq_intro (Seq.slice (as_seq h1 dest) 0 5) (as_seq h1 dest)


private
let lemma_mul_5 (a:nat) (b:nat) (c:nat) (d:nat) (e:nat) : Lemma
  (a + pow2 51 * b + pow2 102 * c + pow2 153 * e + pow2 204 * e >= 0)
  = ()


inline_for_extraction
private
val fdifference_norm:
  x:elemB ->
  y:elemB{disjoint x y} ->
  Stack unit
    (requires (fun h -> live h x /\ live h y /\ red_513 (as_seq h y) /\ red_513 (as_seq h x)))
    (ensures (fun h0 _ h1 -> live h0 x /\ live h0 y /\ live h1 x /\ live h1 y /\ red_513 (as_seq h0 x)
      /\ red_513 (as_seq h0 y)
      /\ modifies_1 x h0 h1 /\ red_51 (as_seq h1 x) /\
      (let s = as_seq h1 x in
       FStar.Mul.(Hacl.UInt64.(v (Seq.index s 0)
                               + pow2 51 * v (Seq.index s 1)
                               + pow2 102 * v (Seq.index s 2)
                               + pow2 153 * v (Seq.index s 3)
                               + pow2 204 * v (Seq.index s 4) < Spec.Curve25519.prime))) /\
      seval (as_seq h1 x) = Spec.Curve25519.(seval (as_seq h0 y) `fsub` seval (as_seq h0 x))
    ))
let fdifference_norm x y =
  fdifference x y;
  reduce_513 x;
  reduce x


private
let lemma_distr_4 a b c d e : Lemma (a * (b + c + d + e) == a * b + a * c + a * d + a * e)
  = Math.Lemmas.distributivity_add_right a (b + c + d) e;
    Math.Lemmas.distributivity_add_right a (b + c) d;
    Math.Lemmas.distributivity_add_right a (b) c


private
let lemma_x_mod_2 (a:nat) (b:nat) (c:nat) (d:nat) (e:nat) :
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

inline_for_extraction
private val x_mod_2:
  x:felem ->
  Stack Hacl.UInt64.t
    (requires (fun h -> live h x /\ red_51 (as_seq h x) /\
      (let s = as_seq h x in
       FStar.Mul.(Hacl.UInt64.(v (Seq.index s 0)
                               + pow2 51 * v (Seq.index s 1)
                               + pow2 102 * v (Seq.index s 2)
                               + pow2 153 * v (Seq.index s 3)
                               + pow2 204 * v (Seq.index s 4) < pow2 255 - 19)))))
    (ensures (fun h0 z h1 -> h0 == h1 /\ live h0 x /\ v z = seval (as_seq h0 x) % 2))
let x_mod_2 x =
  let h = ST.get() in
  Hacl.Bignum25519.lemma_reveal_seval (as_seq h x);
  Math.Lemmas.modulo_lemma (let s = as_seq h x in v (Seq.index s 0)
                               + pow2 51 * v (Seq.index s 1)
                               + pow2 102 * v (Seq.index s 2)
                               + pow2 153 * v (Seq.index s 3)
                               + pow2 204 * v (Seq.index s 4)) Spec.Curve25519.prime;
  lemma_x_mod_2 (v (get h x 0)) (v (get h x 1)) (v (get h x 2)) (v (get h x 3)) (v (get h x 4));
  let x0 = x.(0ul) in
  let z  = x0 &^ 1uL in
  assert_norm(pow2 1 = 2);
  UInt.logand_mask (v x0) 1;
  z


private
let lemma_modifies_2 #a #a' h (b:buffer a) (b':buffer a') :
  Lemma (modifies_2 b b' h h)
  = lemma_intro_modifies_2 b b' h h


private
let lemma_modifies_1 #a h (b:buffer a) :
  Lemma (modifies_1 b h h)
  = lemma_intro_modifies_1 b h h

inline_for_extraction
private
val recover_x_step_2:
  x:elemB ->
  sign:Hacl.UInt64.t{v sign < 2} ->
  x2:elemB{disjoint x x2} ->
  Stack UInt8.t
    (requires (fun h -> live h x2 /\ live h x /\
      (let s = as_seq h x2 in
       red_51 s /\
       FStar.Mul.(Hacl.UInt64.(v (Seq.index s 0)
                               + pow2 51 * v (Seq.index s 1)
                               + pow2 102 * v (Seq.index s 2)
                               + pow2 153 * v (Seq.index s 3)
                               + pow2 204 * v (Seq.index s 4) < Spec.Curve25519.prime))) ))
    (ensures (fun h0 z h1 -> live h0 x2 /\ live h0 x /\ live h1 x /\ live h1 x2 /\
      (let x2 = as_seq h0 x2 in
       if seval x2 = 0 && v sign = 0
       then (modifies_1 x h0 h1 /\ norm h1 x /\ seval (as_seq h1 x) = 0 /\ z == 1uy)
       else if seval x2 = 0 && v sign = 1
       then (h0 == h1 /\ z == 0uy)
       else (h0 == h1 /\ z == 2uy))))
let recover_x_step_2 x sign x2 =
  let x2_is_0 = is_0 x2 in
  if x2_is_0 then (
    if sign =^ 0uL then (
      make_zero x;
      1uy
    ) else 0uy
  ) else 2uy


#reset-options "--max_fuel 0 --z3rlimit 100"


inline_for_extraction
private
val recover_x_step_3:
  tmp:buffer Hacl.UInt64.t{length tmp = 20} ->
  Stack unit
    (requires (fun h -> live h tmp /\
      (let x2 = as_seq h (Buffer.sub tmp 0ul 5ul) in
       red_513 x2)))
    (ensures (fun h0 _ h1 -> live h0 tmp /\ live h1 tmp /\ modifies_1 tmp h0 h1 /\
      (let x2 = as_seq h0 (Buffer.sub tmp 0ul 5ul) in
       let x2' = as_seq h1 (Buffer.sub tmp 0ul 5ul) in
       let x3 = as_seq h1 (Buffer.sub tmp 5ul 5ul) in
       let x = Spec.Curve25519.(seval x2 ** ((prime + 3) / 8)) in
       let y = if Spec.Curve25519.((x `fmul` x) `fsub` seval x2) <> 0 then Spec.Curve25519.(x `fmul` Spec.Ed25519.modp_sqrt_m1) else x in
       seval x3 == y /\ red_51 x3 /\ x2' == x2 /\ v (Seq.index x3 0) + pow2 51 * v (Seq.index x3 1)
       + pow2 102 * v (Seq.index x3 2) + pow2 153 * v (Seq.index x3 3)
       + pow2 204 * v (Seq.index x3 4) < Spec.Curve25519.prime)))
let recover_x_step_3 tmp =
  let x2  = Buffer.sub tmp 0ul 5ul in
  let x3  = Buffer.sub tmp 5ul 5ul in
  let t0  = Buffer.sub tmp 10ul 5ul in
  let t1  = Buffer.sub tmp 15ul 5ul in
  Hacl.Impl.Ed25519.Pow2_252m2.pow2_252m2 x3 x2;
  let h' = ST.get() in
  lemma_red_513_is_red_5413 (as_seq h' x3);
  Hacl.Bignum25519.fsquare t0 x3;
  copy x2 t1;
  fdifference_norm t1 t0;
  let t1_is_0 = is_0 t1 in
  if t1_is_0 then ()
  else (
    mul_modp_sqrt_m1 x3
  );
  Hacl.Bignum25519.reduce x3


inline_for_extraction
private
val recover_x_step_4:
  tmp:buffer Hacl.UInt64.t{length tmp = 20} ->
  Stack bool
    (requires (fun h -> live h tmp /\
      (let x2 = as_seq h (Buffer.sub tmp 0ul 5ul) in
       let x3 = as_seq h (Buffer.sub tmp 5ul 5ul) in
       red_513 x2 /\ red_51 x3 /\ v (Seq.index x3 0) + pow2 51 * v (Seq.index x3 1)
       + pow2 102 * v (Seq.index x3 2) + pow2 153 * v (Seq.index x3 3)
       + pow2 204 * v (Seq.index x3 4) < Spec.Curve25519.prime)))
    (ensures (fun h0 z h1 -> live h0 tmp /\ live h1 tmp /\ modifies_1 tmp h0 h1 /\
      (let x2 = as_seq h0 (Buffer.sub tmp 0ul 5ul) in
       let x3 = as_seq h0 (Buffer.sub tmp 5ul 5ul) in
       let x2' = as_seq h1 (Buffer.sub tmp 0ul 5ul) in
       let x3' = as_seq h1 (Buffer.sub tmp 5ul 5ul) in
       let u = seval x3 in let v = seval x2 in
       let y = Spec.Curve25519.((u `fmul` u) `fsub` v) in
       if y <> 0 then z == false
       else (x2' == x2 /\ x3' == x3 /\ z == true))))
#reset-options "--max_fuel 0 --z3rlimit 100"
let recover_x_step_4 tmp =
  let h0 = ST.get() in
  let x2  = Buffer.sub tmp 0ul 5ul in
  let x3  = Buffer.sub tmp 5ul 5ul in
  let t0  = Buffer.sub tmp 10ul 5ul in
  let t1  = Buffer.sub tmp 15ul 5ul in
  lemma_red_51_is_red_5413 (as_seq h0 x3);
  Hacl.Bignum25519.fsquare t0 x3;
  let h = ST.get() in
  copy x2 t1;
  let h' = ST.get() in
  no_upd_lemma_1 h0 h t0 x2;
  no_upd_lemma_1 h h' t1 x2;
  fdifference_norm t1 t0;
  is_0 t1


private
val lemma_fdiff_prime:
  x:Spec.Curve25519.elem ->
  Lemma (Spec.Curve25519.(0 `fsub` x == prime `fsub` x))
let lemma_fdiff_prime x =
  FStar.Math.Axioms.lemma_mod_sub_distr_l_l Spec.Curve25519.prime x Spec.Curve25519.prime


inline_for_extraction
private
val recover_x_step_5:
  x:elemB ->
  sign:Hacl.UInt64.t{v sign < 2} ->
  tmp:buffer Hacl.UInt64.t{length tmp = 20 /\ disjoint x tmp} ->
  Stack unit
    (requires (fun h -> live h x /\ live h tmp /\
      (let x3 = as_seq h (Buffer.sub tmp 5ul 5ul) in
       red_51 x3 /\ v (Seq.index x3 0) + pow2 51 * v (Seq.index x3 1)
       + pow2 102 * v (Seq.index x3 2) + pow2 153 * v (Seq.index x3 3)
       + pow2 204 * v (Seq.index x3 4) < Spec.Curve25519.prime)))
    (ensures (fun h0 _ h1 -> live h0 x /\ live h0 tmp /\ live h1 x /\ live h1 tmp /\
      modifies_2 x tmp h0 h1 /\
      (let x3  = as_seq h0 (Buffer.sub tmp 5ul 5ul) in
       let x   = as_seq h1 x in
       let r   = if (seval x3 % 2) <> v sign then Spec.Curve25519.(prime `fsub` seval x3) else seval x3 in
       seval x == r /\ red_51 x)))
#reset-options "--max_fuel 0 --z3rlimit 100"
let recover_x_step_5 x sign tmp =
  let h0 = ST.get() in
  let x3  = Buffer.sub tmp 5ul 5ul in
  lemma_red_51_is_red_513 (as_seq h0 x3);
  let t0  = Buffer.sub tmp 10ul 5ul in
  let x0 = x_mod_2 x3 in
  if not(x0 =^ sign) then (
    make_zero t0;
    fdifference_norm x3 t0;
    let h = ST.get() in
    lemma_fdiff_prime (seval (as_seq h0 x3))
  ) else (
    let h = ST.get() in
    lemma_modifies_1 h tmp);
  let h' = ST.get() in
  assert(modifies_1 tmp h0 h');
  assert(red_51 (as_seq h' x3));
  copy x3 x

inline_for_extraction
private
val recover_x_:
  x:elemB ->
  y:elemB{disjoint x y} ->
  sign:UInt64.t{v sign = 0 \/ v sign = 1} ->
  tmp:buffer Hacl.UInt64.t{length tmp = 20 /\ disjoint tmp x /\ disjoint tmp y} ->
  Stack bool
    (requires (fun h -> live h x /\ live h y /\ red_51 (as_seq h y) /\ live h tmp))
    (ensures (fun h0 z h1 -> live h1 x /\ live h0 y /\ modifies_2 x tmp h0 h1 /\
      (let op_String_Access = Seq.index in
       let y = as_seq h0 y in
       lemma_mul_5 (v y.[0]) (v y.[1]) (v y.[2]) (v y.[3]) (v y.[4]);
       let y:nat = v y.[0] + pow2 51 * v y.[1] + pow2 102 * v y.[2] + pow2 153 * v y.[3]
               + pow2 204 * v y.[4] in
       let x = as_seq h1 x in
       let sign = (v sign = 1) in
       let res  = Spec.Ed25519.recover_x y sign in
       (z <==> Some? res)
       /\ (Some? res ==> (seval x = Some?.v res /\ red_51 x)))
      ))
#reset-options "--max_fuel 0 --z3rlimit 500"
let recover_x_ x y sign tmp =
  assert_norm(pow2 32 = 0x100000000);
  let x2  = Buffer.sub tmp 0ul 5ul in
  (* let x3  = Buffer.sub tmp 5ul 5ul in *)
  (* let t0  = Buffer.sub tmp 10ul 5ul in *)
  (* let t1  = Buffer.sub tmp 15ul 5ul in *)
  let b = gte_q y in
  let h0 = ST.get() in
  let res =
  if b then (
    lemma_modifies_2 h0 x tmp;
    false
  ) else (
    lemma_reveal_seval (as_seq h0 y);
    lemma_mul_5 (v (get h0 y 0)) (v (get h0 y 1)) (v (get h0 y 2)) (v (get h0 y 3)) (v (get h0 y 4));
    Math.Lemmas.modulo_lemma (let op_String_Access = Seq.index in let y = as_seq h0 y in
      v y.[0] + pow2 51 * v y.[1] + pow2 102 * v y.[2] + pow2 153 * v y.[3] + pow2 204 * v y.[4]) Spec.Curve25519.prime;
    lemma_disjoint_sub tmp x2 y;
    recover_x_step_1 x2 y;
    let h1 = ST.get() in
    lemma_disjoint_sub tmp x2 x;
    let z = recover_x_step_2 x sign x2 in
    if z = 0uy then (
      lemma_modifies_1 h0 x;
      false
    ) else if z = 1uy then (
      true
    ) else (
      let h2 = ST.get() in
      lemma_red_51_is_red_513 (as_seq h2 x2);
      recover_x_step_3 tmp;
      let h3 = ST.get() in
      let z = recover_x_step_4 tmp in
      if z = false then (
        let h3 = ST.get() in
        lemma_modifies_1 h3 x;
        //assert(modifies_2 x tmp h0 h3);
        false)
      else (
        let h4 = ST.get() in
        recover_x_step_5 x sign tmp;
        let h5 = ST.get() in
        //assert (modifies_1 tmp h0 h1);
        //assert (h1 == h2);
        //assert (modifies_1 tmp h2 h3);
        //assert (modifies_1 tmp h3 h4);
        lemma_modifies_1_trans tmp h2 h3 h4;
        //assert (modifies_1 tmp h2 h4);
        lemma_modifies_1_trans tmp h0 h1 h4;
        //assert (modifies_1 tmp h0 h4);
        //assert (modifies_2 x tmp h4 h5);
        lemma_modifies_1_2''' tmp x h0 h4 h5;
        true
      )
    )
   ) in
   res


#reset-options "--max_fuel 0 --z3rlimit 100"

let recover_x x y sign =
  assert_norm(pow2 32 = 0x100000000);
  push_frame();
  let tmp = create 0uL 20ul in
  let res = recover_x_ x y sign tmp in
  pop_frame();
  res
