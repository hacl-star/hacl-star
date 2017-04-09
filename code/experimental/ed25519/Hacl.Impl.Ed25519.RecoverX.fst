module Hacl.Impl.Ed25519.RecoverX

open FStar.Buffer
open FStar.UInt64
open Hacl.Spec.BignumQ.Eval

let elemB = b:buffer Hacl.UInt64.t{length b = 5}

private
val recover_x_step_1:
  x2:elemB ->
  y:elemB ->
  Stack unit
    (requires (fun h -> live h x2 /\ live h y))
    (ensures (fun h0 _ h1 -> live h1 x2 /\ live h0 y /\ modifies_1 x2 h0 h1))
let recover_x_step_1 x2 y =
  push_frame();
  let zero = (Hacl.Cast.uint64_to_sint64 0uL) in
  let one' = (Hacl.Cast.uint64_to_sint64 1uL) in
  let tmp = create (Hacl.Cast.uint64_to_sint64 0uL) 25ul in
  let one = Buffer.sub tmp 0ul 5ul in
  let y2  = Buffer.sub tmp 5ul 5ul in
  let dyyi = Buffer.sub tmp 10ul 5ul in
  let dyy = Buffer.sub tmp 15ul 5ul in
  Hacl.Lib.Create64.make_h64_5 one one' zero zero zero zero;
  Hacl.Bignum25519.fsquare y2 y;
  Hacl.Bignum25519.times_d dyy y2;
  Hacl.Bignum25519.fsum dyy one;
  Hacl.Bignum25519.inverse dyyi dyy;
  Hacl.Bignum25519.fdifference one y2;
  Hacl.Bignum25519.fmul x2 one dyyi;
  Hacl.Bignum25519.reduce x2;  
  pop_frame()


(* val compare: *)
(*   x:elemB -> *)
(*   y:elemB -> *)
(*   Stack bool *)
(*     (requires (fun h -> live h x /\ live h y)) *)
(*     (ensures (fun h0 b h1 -> h0 == h1 /\ live h0 x /\ live h0 y /\ *)
(*       b <==> (as_seq h0 x == as_seq h0 y))) *)
(* let compare x y = *)
(*   let x0 = x.(0ul) in *)
(*   let x1 = x.(1ul) in *)
(*   let x2 = x.(2ul) in *)
(*   let x3 = x.(3ul) in *)
(*   let x4 = x.(4ul) in *)
(*   let y0 = y.(0ul) in *)
(*   let y1 = y.(1ul) in *)
(*   let y2 = y.(2ul) in *)
(*   let y3 = y.(3ul) in *)
(*   let y4 = y.(4ul) in *)
(*   FStar.UInt64.(x0 =^ y0 && x1 =^ y1 && x2 =^ y2 && x3 =^ y3 && x4 =^ y4) *)

private
val is_0:
  x:elemB ->
  Stack bool
    (requires (fun h -> live h x /\ Hacl.Bignum25519.red_51 (as_seq h x)))
    (ensures (fun h0 b h1 -> h0 == h1 /\ live h0 x /\
      b <==> (Hacl.Spec.Bignum.Bigint.seval (as_seq h0 x) == 0)))
let is_0 x =
  let x0 = x.(0ul) in
  let x1 = x.(1ul) in
  let x2 = x.(2ul) in
  let x3 = x.(3ul) in
  let x4 = x.(4ul) in
  FStar.UInt64.(x0 =^ 0uL && x1 =^ 0uL && x2 =^ 0uL && x3 =^ 0uL && x4 =^ 0uL)

private
val mul_modp_sqrt_m1:
  x:elemB ->
  Stack unit
    (requires (fun h -> live h x /\ Hacl.Bignum25519.red_51 (as_seq h x) ))
    (ensures (fun h0 _ h1 -> live h1 x /\ live h0 x /\ modifies_1 x h0 h1
      /\ Hacl.Bignum25519.red_51 (as_seq h0 x) /\ Hacl.Bignum25519.red_51 (as_seq h1 x) /\
      Hacl.Spec.Bignum.Bigint.seval (as_seq h1 x)
      == Spec.Curve25519.(Hacl.Spec.Bignum.Bigint.seval (as_seq h0 x) `fmul` (Spec.Ed25519.modp_sqrt_m1))
    ))
let mul_modp_sqrt_m1 x =
  push_frame();
  let sqrt_m1 = create 0uL 5ul in
  Hacl.Lib.Create64.make_h64_5 sqrt_m1 0x00061b274a0ea0b0uL 0x0000d5a5fc8f189duL 0x0007ef5e9cbd0c60uL 0x00078595a6804c9euL 0x0002b8324804fc1duL;
  Hacl.Bignum25519.fmul x x sqrt_m1;
  Hacl.Bignum25519.reduce x;
  pop_frame()


val recover_x:
  x:elemB ->
  y:elemB{disjoint x y} ->
  sign:Hacl.UInt64.t ->
  Stack bool
    (requires (fun h -> live h x /\ live h y))
    (ensures (fun h0 _ h1 -> live h1 x /\ live h0 y /\ modifies_1 x h0 h1))
let recover_x x y sign =
  push_frame();
  let tmp = create 0uL 20ul in
  let x2  = Buffer.sub tmp 0ul 5ul in
  let x3  = Buffer.sub tmp 5ul 5ul in
  let t0  = Buffer.sub tmp 10ul 5ul in
  let t1  = Buffer.sub tmp 15ul 5ul in
  Hacl.Impl.BignumQ.Mul.subm_conditional x y;
  let x4 = x.(4ul) in
  let res =
  if x4 >=^ 0x10000000000uL then false
  else (
    recover_x_step_1 x2 y;
    Hacl.Impl.Ed25519.Pow2_252m2.pow2_252m2 x3 x2;
    Hacl.Bignum25519.fsquare t0 x3;
    blit x2 0ul t1 0ul 5ul;
    Hacl.Bignum25519.fdifference t1 t0;
    Hacl.Bignum25519.reduce t1;
    let t1_is_0 = is_0 t1 in
    if t1_is_0 then ()
    else (
      mul_modp_sqrt_m1 x3
    );
    Hacl.Bignum25519.fsquare t0 x3;
    blit x2 0ul t1 0ul 5ul;
    Hacl.Bignum25519.fdifference t1 t0;
    Hacl.Bignum25519.reduce t1;
    let t1_is_0 = is_0 t1 in
    if t1_is_0 then (
      let x0 = x3.(0ul) &^ 1uL in
      if not(x0 =^ sign) then (
        Hacl.Lib.Create64.make_h64_5 t0 0uL 0uL 0uL 0uL 0uL;
        Hacl.Bignum25519.fdifference x3 t0;
        Hacl.Bignum25519.reduce x3
      ) else ();
      blit x3 0ul x 0ul 5ul;
      true
    )
    else false
  ) in
  pop_frame();
  res
