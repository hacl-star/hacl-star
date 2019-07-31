module Hacl.Impl.BignumQ.Mul

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

include Hacl.Spec.BignumQ.Mul

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let barrett_reduction z t =
  let (t0, t1, t2, t3, t4, t5, t6, t7, t8, t9) =
    (t.(0ul), t.(1ul), t.(2ul), t.(3ul), t.(4ul), t.(5ul), t.(6ul), t.(7ul), t.(8ul), t.(9ul)) in
  let (z0, z1, z2, z3, z4)= barrett_reduction5 (t0, t1, t2, t3, t4, t5, t6, t7, t8, t9) in
  z.(0ul) <- z0;
  z.(1ul) <- z1;
  z.(2ul) <- z2;
  z.(3ul) <- z3;
  z.(4ul) <- z4


let mul_modq out x y =
  let (x0, x1, x2, x3, x4) = (x.(0ul), x.(1ul), x.(2ul), x.(3ul), x.(4ul)) in
  let (y0, y1, y2, y3, y4) = (y.(0ul), y.(1ul), y.(2ul), y.(3ul), y.(4ul)) in
  let (z0, z1, z2, z3, z4) = mul_modq5 (x0, x1, x2, x3, x4) (y0, y1, y2, y3, y4) in
  out.(0ul) <- z0;
  out.(1ul) <- z1;
  out.(2ul) <- z2;
  out.(3ul) <- z3;
  out.(4ul) <- z4

let add_modq out x y =
  let (x0, x1, x2, x3, x4) = (x.(0ul), x.(1ul), x.(2ul), x.(3ul), x.(4ul)) in
  let (y0, y1, y2, y3, y4) = (y.(0ul), y.(1ul), y.(2ul), y.(3ul), y.(4ul)) in
  let (z0, z1, z2, z3, z4) = add_modq5 (x0, x1, x2, x3, x4) (y0, y1, y2, y3, y4) in
  out.(0ul) <- z0;
  out.(1ul) <- z1;
  out.(2ul) <- z2;
  out.(3ul) <- z3;
  out.(4ul) <- z4
