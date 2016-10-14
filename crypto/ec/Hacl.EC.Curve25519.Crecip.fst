module Hacl.EC.Curve25519.Crecip

open FStar.Mul
open FStar.ST
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer
open Hacl.UInt64
(* open Hacl.SBuffer *)
open FStar.Buffer
open FStar.Math.Lib
open Hacl.EC.Curve25519.Parameters
open Hacl.EC.Curve25519.Bigint
open Hacl.EC.Curve25519.Bignum


#reset-options "--initial_fuel 0 --max_fuel 0"

(* Module abbreviations *)
(* module B  = Hacl.SBuffer *)
module B = FStar.Buffer
module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module U8  = FStar.UInt8
module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32  = Hacl.UInt32
module H64  = Hacl.UInt64
module H128  = Hacl.UInt128

val loop: tmp:bigint -> v:bigint{disjoint tmp v} -> ctr:U32.t -> Stack unit 
    (requires (fun h -> live h tmp /\ live h v)) 
    (ensures (fun h0 _ h1 -> live h1 tmp /\ live h1 v /\ modifies_2 tmp v h0 h1))
let rec loop tmp v ctr =
  if U32 (ctr =^ 0ul) then ()
  else (
    fsquare tmp v;
    fsquare v tmp;
    let h = ST.get() in
    assert(live h tmp /\ live h v);
    assert(U32.v ctr > 0);
    loop tmp v (U32 (ctr -^ 1ul))
  )

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 50"

val crecip_0: tmp:bigint{length tmp = 50} -> z:bigint{disjoint tmp z} -> Stack unit
  (requires (fun h -> live h tmp /\ live h z))
  (ensures  (fun h0 _ h1 -> live h1 tmp /\ modifies_1 tmp h0 h1))
let crecip_0 tmp z =
  let z2      = sub tmp 0ul nlength in
  let z9      = sub tmp 5ul nlength in
  let z11     = sub tmp 10ul nlength in
  let z2_5_0   = sub tmp 15ul nlength in
  (* let z2_10_0  = sub tmp 20ul nlength in *)
  (* let z2_20_0  = sub tmp 25ul nlength in *)
  (* let z2_50_0  = sub tmp 30ul nlength in *)
  (* let z2_100_0 = sub tmp 35ul nlength in *)
  let t0      = sub tmp 40ul nlength in
  let t1      = sub tmp 45ul nlength in
  fsquare z2 z;  (* 2 *)
  fsquare t1 z2;  (* 4 *)
  fsquare t0 t1;   (* 8 *)
  fmul z9 t0 z;  (* 9 *)
  fmul z11 z9 z2;  (* 11 *)
  fsquare t0 z11;  (* 22 *)
  fmul z2_5_0 t0 z9;  (* 2^5 - 2^0 = 31 *)
  ()

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 50"

val crecip_1: tmp:bigint{length tmp = 50} -> z:bigint{disjoint tmp z} -> Stack unit
  (requires (fun h -> live h tmp /\ live h z))
  (ensures  (fun h0 _ h1 -> live h1 tmp /\ modifies_1 tmp h0 h1))
let crecip_1 tmp z =
  (* let z2      = sub tmp 0ul nlength in *)
  (* let z9      = sub tmp 5ul nlength in *)
  (* let z11     = sub tmp 10ul nlength in *)
  let z2_5_0   = sub tmp 15ul nlength in
  let z2_10_0  = sub tmp 20ul nlength in
  (* let z2_20_0  = sub tmp 25ul nlength in *)
  (* let z2_50_0  = sub tmp 30ul nlength in *)
  (* let z2_100_0 = sub tmp 35ul nlength in *)
  let t0      = sub tmp 40ul nlength in
  let t1      = sub tmp 45ul nlength in
  fsquare t0 z2_5_0;  (* 2^6 - 2^1 *)
  fsquare t1 t0;  (* 2^7 - 2^2 *)
  fsquare t0 t1;  (* 2^8 - 2^3 *)
  fsquare t1 t0;  (* 2^9 - 2^4 *)
  fsquare t0 t1;  (* 2^10 - 2^5 *)
  fmul z2_10_0 t0 z2_5_0;  (* 2^10 - 2^0 *)	  
  ()


#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 50"

val crecip_2: tmp:bigint{length tmp = 50} -> z:bigint{disjoint tmp z} -> Stack unit
  (requires (fun h -> live h tmp /\ live h z))
  (ensures  (fun h0 _ h1 -> live h1 tmp /\ modifies_1 tmp h0 h1))
let crecip_2 tmp z =
  (* let z2      = sub tmp 0ul nlength in *)
  (* let z9      = sub tmp 5ul nlength in *)
  (* let z11     = sub tmp 10ul nlength in *)
  (* let z2_5_0   = sub tmp 15ul nlength in *)
  let z2_10_0  = sub tmp 20ul nlength in
  let z2_20_0  = sub tmp 25ul nlength in
  let z2_50_0  = sub tmp 30ul nlength in
  (* let z2_100_0 = sub tmp 35ul nlength in *)
  let t0      = sub tmp 40ul nlength in
  let t1      = sub tmp 45ul nlength in
  fsquare t0 z2_10_0;  (* 2^11 - 2^1 *)
  fsquare t1 t0;  (* 2^12 - 2^2 *)
  loop t0 t1 4ul;  (* 2^20 - 2^10 *)	  
  fmul z2_20_0 t1 z2_10_0;  (* 2^20 - 2^0 *)   
  fsquare t0 z2_20_0;  (* 2^21 - 2^1 *) 
  fsquare t1 t0;  (* 2^22 - 2^2 *) 
  loop t0 t1 9ul;  (* 2^40 - 2^20 *)
  fmul t0 t1 z2_20_0;  (* 2^40 - 2^0 *)   
  fsquare t1 t0;  (* 2^41 - 2^1 *) 
  fsquare t0 t1;  (* 2^42 - 2^2 *) 
  loop t1 t0 4ul;  (* 2^50 - 2^10 *)  
  fmul z2_50_0 t0 z2_10_0;  (* 2^50 - 2^0 *)   
  ()


#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 50"

val crecip_3: tmp:bigint{length tmp = 50} -> z:bigint{disjoint tmp z} -> Stack unit
  (requires (fun h -> live h tmp /\ live h z))
  (ensures  (fun h0 _ h1 -> live h1 tmp /\ modifies_1 tmp h0 h1))
let crecip_3 tmp z =
  (* let z2      = sub tmp 0ul nlength in *)
  (* let z9      = sub tmp 5ul nlength in *)
  (* let z11     = sub tmp 10ul nlength in *)
  (* let z2_5_0   = sub tmp 15ul nlength in *)
  (* let z2_10_0  = sub tmp 20ul nlength in *)
  (* let z2_20_0  = sub tmp 25ul nlength in *)
  let z2_50_0  = sub tmp 30ul nlength in
  let z2_100_0 = sub tmp 35ul nlength in
  let t0      = sub tmp 40ul nlength in
  let t1      = sub tmp 45ul nlength in
  fsquare t0 z2_50_0;  (* 2^51 - 2^1 *) 
  fsquare t1 t0;  (* 2^52 - 2^2 *) 
  loop t0 t1 24ul;  (* 2^100 - 2^50 *)  
  fmul z2_100_0 t1 z2_50_0;  (* 2^100 - 2^0 *)   
  fsquare t1 z2_100_0;  (* 2^101 - 2^1 *) 
  fsquare t0 t1;  (* 2^102 - 2^2 *) 
  loop t1 t0 49ul;  (* 2^200 - 2^100 *)  
  fmul t1 t0 z2_100_0;  (* 2^200 - 2^0 *) 
  ()


#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 50"

val crecip_4: tmp:bigint{length tmp = 50} -> z:bigint{disjoint tmp z} -> Stack unit
  (requires (fun h -> live h tmp /\ live h z))
  (ensures  (fun h0 _ h1 -> live h1 tmp /\ modifies_1 tmp h0 h1))
let crecip_4 tmp z =
  (* let z2      = sub tmp 0ul nlength in *)
  (* let z9      = sub tmp 5ul nlength in *)
  (* let z11     = sub tmp 10ul nlength in *)
  (* let z2_5_0   = sub tmp 15ul nlength in *)
  (* let z2_10_0  = sub tmp 20ul nlength in *)
  (* let z2_20_0  = sub tmp 25ul nlength in *)
  let z2_50_0  = sub tmp 30ul nlength in
  (* let z2_100_0 = sub tmp 35ul nlength in *)
  let t0      = sub tmp 40ul nlength in
  let t1      = sub tmp 45ul nlength in
  fsquare t0 t1;  (* 2^201 - 2^1 *) 
  fsquare t1 t0;  (* 2^202 - 2^2 *) 
  loop t0 t1 24ul;  (* 2^250 - 2^50 *)  
  fmul t0 t1 z2_50_0;  (* 2^250 - 2^0 *)   
  fsquare t1 t0;  (* 2^251 - 2^1 *) 
  fsquare t0 t1;  (* 2^252 - 2^2 *) 
  fsquare t1 t0;  (* 2^253 - 2^3 *) 
  fsquare t0 t1;  (* 2^254 - 2^4 *) 
  fsquare t1 t0;  (* 2^255 - 2^5 *) 
  ()

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 50"

val crecip': output:bigint -> z:bigint{disjoint output z} -> Stack unit 
  (requires (fun h -> live h output /\ live h z)) 
  (ensures (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1))
let crecip' output z = 
  push_frame();
  let tmp = create (Hacl.Cast.uint64_to_sint64 0uL) (U32 (10ul *^ nlength)) in
  (* let z2      = sub tmp 0ul nlength in *)
  (* let z9      = sub tmp 5ul nlength in *)
  let z11     = sub tmp 10ul nlength in
  (* let z2_5_0   = sub tmp 15ul nlength in *)
  (* let z2_10_0  = sub tmp 20ul nlength in *)
  (* let z2_20_0  = sub tmp 25ul nlength in *)
  (* let z2_50_0  = sub tmp 30ul nlength in *)
  (* let z2_100_0 = sub tmp 35ul nlength in *)
  (* let t0      = sub tmp 40ul nlength in *)
  let t1      = sub tmp 45ul nlength in
  crecip_0 tmp z;
  crecip_1 tmp z;
  crecip_2 tmp z;
  crecip_3 tmp z;
  crecip_4 tmp z;
  fmul output t1 z11;  (* 2^255 - 21 *) 
  pop_frame()
