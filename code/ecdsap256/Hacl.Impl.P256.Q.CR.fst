module Hacl.Impl.P256.Q.CR

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST


open Lib.IntTypes
open Lib.Buffer


open Hacl.Impl.P256.LowLevel

let pointLen = 8ul

(*cmovznz *)
val select: r: lbuffer uint64 pointLen 
  -> points: lbuffer uint64 (pointLen *. 16ul) 
  -> id0: size_t
  -> id1: size_t 
  -> bit: uint8 {v bit = 0 \/ v bit = 1} 
  -> Stack unit 
    (requires fun h -> True)
    (ensures fun h0 _ h1 -> modifies (loc r) h0 h1)

let select r points id0 id1 bit = 
  let x = sub r (size 0) (size 4) in 
  let y = sub r (size 4) (size 4) in 

  let pX = sub points (id0 *. pointLen) (size 4) in 
  let pY = sub points ((id0 +. 1ul) *. pointLen) (size 4) in 

  let qX = sub points (id1 *. pointLen) (size 4) in 
  let qY = sub points ((id1 +. 1ul) *. pointLen) (size 4) in 

  let bitAsUInt64 = to_u64 bit in 

  cmovznz4 bitAsUInt64 pX qX x;
  cmovznz4 bitAsUInt64 pY qY y 



val do_lookup: a: lbuffer uint64 (pointLen *. 16ul) -> scalar: uint8 {v scalar < 16} -> Stack unit
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

let do_lookup a scalar =
  push_frame();
    let tn = create (pointLen *. 14ul) (u64 0) in 

    let t0_0 = sub tn (size 0) pointLen in 
  
    let b0 = logand scalar (1uy) in 
    let id0_0 = 0ul in 
    let id1_0 = 1ul in 

  (* for i in range(0...n) *)
    select t0_0 a id0_0 id1_0 b0;
    
  pop_frame()
