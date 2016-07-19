module Hacl.Operations

open FStar.HyperStack
open FStar.HST
open FStar.Buffer
open FStar.UInt32


(* Define base types *)
let u32 = FStar.UInt32.t
let s32 = Hacl.UInt32.t
let bytes = Hacl.SBuffer.u8s


(* Define word functions *)
let rotate_right (a:s32) (b:u32{v b <= 32}) : Tot s32 =
  Hacl.UInt32.logor (Hacl.UInt32.shift_right a b) (Hacl.UInt32.shift_left a (FStar.UInt32.sub 32ul b))


(* Define helper xor function *)
val xor_bytes: output:bytes -> in1:bytes{disjoint in1 output} -> 
  len:u32{v len <= length output /\ v len <= length in1} -> STL unit
  (requires (fun h -> live h output /\ live h in1))
  (ensures  (fun h0 _ h1 -> live h0 output /\ live h0 in1 /\ live h1 output /\ live h1 in1
    /\ modifies_1 output h0 h1 ))
let rec xor_bytes output in1 len =
  if len =^ 0ul then ()
  else
    begin
      let i    = Hacl.UInt32.sub_mod len 1ul in
      let in1i = index in1 i in
      let oi   = index output i in
      let oi   = Hacl.UInt8.logxor in1i oi in
      upd output i oi;
      xor_bytes output in1 i
    end
