module Hacl.Impl.P256.Q.CR

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST


open Lib.IntTypes
open Lib.Buffer


#set-options "--z3rlimit 300" 


open Hacl.Impl.P256.LowLevel
open Hacl.Impl.P256.Q.PrimitivesMasking

let pointLen = 8ul

(*cmovznz *)
val select: r: lbuffer uint64 pointLen 
  -> a: lbuffer uint64 pointLen
  -> b: lbuffer uint64 pointLen
  -> bit: uint8 {v bit = 0 \/ v bit = 1} 
  -> Stack unit 
    (requires fun h ->  live h r /\ live h a /\ live h b)
    (ensures fun h0 _ h1 -> modifies (loc r) h0 h1)

let select r a b bit = 
  let x = sub r (size 0) (size 4) in 
  let y = sub r (size 4) (size 4) in 

  let pX = sub a (size 0) (size 4) in 
  let pY = sub a (size 4) (size 4) in  

  let qX = sub b (size 0) (size 4) in 
  let qY = sub b (size 4) (size 4) in  

  let bitAsUInt64 = to_u64 bit in 

  cmovznz4 x pX qX bitAsUInt64;
  cmovznz4 y pY qY bitAsUInt64



val do_lookup: result: lbuffer uint64 pointLen ->  a: lbuffer uint64 (pointLen *. 16ul) -> scalar: uint8 {v scalar < 16} -> 
Stack unit
  (requires fun h -> live h result /\ live h a)
  (ensures fun h0 _ h1 -> True)

let do_lookup result a scalar =
  push_frame();
    let tn = create (pointLen *. 14ul) (u64 0) in 

    let t0_0 = sub tn (size 0) pointLen in 
    let t0_1 = sub tn pointLen pointLen in 
    let t0_2 = sub tn (2ul *. pointLen) pointLen in 
    let t0_3 = sub tn (3ul *. pointLen) pointLen in 
    let t0_4 = sub tn (4ul *. pointLen) pointLen in 
    let t0_5 = sub tn (5ul *. pointLen) pointLen in 
    let t0_6 = sub tn (6ul *. pointLen) pointLen in 
    let t0_7 = sub tn (7ul *. pointLen) pointLen in 

    let t1_0 = sub tn (8ul *. pointLen) pointLen in 
    let t1_1 = sub tn (9ul *. pointLen) pointLen in 
    let t1_2 = sub tn (10ul *. pointLen) pointLen in 
    let t1_3 = sub tn (11ul *. pointLen) pointLen in 

    let t2_0 = sub tn (12ul *. pointLen) pointLen in 
    let t2_1 = sub tn (13ul *. pointLen) pointLen in 
  
    let b0 = logand scalar 1uy in 
    let b1 = logand scalar 2uy in 
    let b2 = logand scalar 4uy in 
    let b3 = logand scalar 8uy in 

    select t0_0 (sub a (size 0) pointLen) (sub a (size 1 *. pointLen) pointLen) b0;
    select t0_1 (sub a (size 2 *. pointLen) pointLen) (sub a (size 3 *. pointLen) pointLen) b0;
    select t0_2 (sub a (size 4 *. pointLen) pointLen) (sub a (size 5 *. pointLen) pointLen) b0;
    select t0_3 (sub a (size 6 *. pointLen) pointLen) (sub a (size 7 *. pointLen) pointLen) b0;
    select t0_4 (sub a (size 8 *. pointLen) pointLen) (sub a (size 9 *. pointLen) pointLen) b0;
    select t0_5 (sub a (size 10 *. pointLen) pointLen) (sub a (size 11 *. pointLen) pointLen) b0;
    select t0_6 (sub a (size 12 *. pointLen) pointLen) (sub a (size 13 *. pointLen) pointLen) b0;
    select t0_7 (sub a (size 14 *. pointLen) pointLen) (sub a (size 15 *. pointLen) pointLen) b0;

    select t1_0 t0_0 t0_1 b1;
    select t1_1 t0_2 t0_3 b1;
    select t1_2 t0_4 t0_5 b1;
    select t1_3 t0_6 t0_6 b1;

    select t2_0 t1_0 t1_1 b2;
    select t2_1 t1_2 t1_3 b2;

    select result t2_0 t2_1 b3;
    
  pop_frame()

open Spec.P256.Definitions
