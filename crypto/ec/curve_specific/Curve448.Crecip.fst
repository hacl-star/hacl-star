module Curve.Crecip

open FStar.ST
open Hacl.SBuffer
open Curve.Parameters
open Curve.Bigint
open Curve.Bignum

(* Loop for fsquaring, result in the first argument, second is a tmp storage array *)
val loop:
  tmp:bigint -> v:bigint -> ctr:nat -> ST unit (requires (fun h -> True)) (ensures (fun h0 _ h1 -> True))
let rec loop tmp v ctr =
  match ctr with
  | 0 -> ()
  | _ ->
    fsquare tmp v;
    fsquare v tmp;
    loop tmp v (ctr-1)

val crecip':
  output:bigint -> z:bigint -> ST unit (requires (fun h -> True)) (ensures (fun h0 _ h1 -> True))
let crecip' output z = 
  let t0 = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in
  let t1 = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in
  let t2 = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in

  fsquare t1 z;  (* 2 *)
  fmul t2 z t1;  (* 3 *)
  fsquare t1 t2; (* 6 *)
  fmul t2 t1 z; (* 7 = 2^3 - 2 ^ 0 *)
  fsquare t0 t2; (* 2^4 - 2^1 *)
  loop t1 t0 1; (* 2^6 - 2^3 *)
  fmul t1 t0 t2; (* 2^6 - 2^0 *)
  fsquare t0 t1; (* 2^7 - 2^1 *)
  loop t1 t0 1; (* 2^9 - 2^3 *)
  fmul t1 t2 t0; (* 2^9 - 2^0 *)
  fsquare t0 t1; (* 2^10 - 2^1 *)
  loop t2 t0 4; (* 2^18 - 2^9 *)
  fmul t2 t0 t1; (* 2^18 - 2^0 *)
  fsquare t0 t2; (* 2^19 - 2^1 *)
  fmul t1 z t0; (* 2^19 - 2^0 *)
  loop t0 t1 9; (* 2^37 - 2^18 *)
  fmul t0 t1 t2; (* 2^37 - 2^0 *)
  fsquare t1 t0; (* 2^38 - 2^1 *)
  loop t2 t1 18; (* 2^74 - 2^37 *)
  fmul t2 t1 t0; (* 2^74 - 2^0 *)
  fsquare t1 t2; (* 2^75 - 2^1 *)
  loop t2 t1 18; (* 2^111 - 2^37 *)
  fmul t2 t1 t0; (* 2^111 - 2^0 *)
  fsquare t1 t2; (* 2^112 - 2^1 *)
  loop t0 t1 55; (* 2^222 - 2^111 *)
  fmul t0 t2 t1; (* 2^222 - 2^0 *)
  fsquare t2 t0; (* 2^223 - 2^1 *)
  fmul t1 z t2; (* 2^223 - 2^0 *)
  fsquare t2 t1; (* 2^224 - 2^1 *)
  loop t1 t2 111; (* 2^446 - 2^223 *)
  fmul t1 t0 t2; (* 2^446 - 2^223 + 2^222 - 2^0 == 2^446 - 2^222 - 2^0 *)
  loop t0 t1 1; (* 2^448 - 2^224 - 4 *)
  fmul output t1 z (* 2^448 - 2^224 - 3 *)
