module Hacl.Operations

open FStar.HyperStack
open FStar.HST
open FStar.Buffer
open FStar.UInt32
open Hacl.Cast

(* Define base types *)
let u8 = FStar.UInt8.t
let s8 = Hacl.UInt8.t
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
      let i    = FStar.UInt32.sub_mod len 1ul in
      let in1i = Hacl.SBuffer.index in1 i in
      let oi   = Hacl.SBuffer.index output i in
      let oi   = Hacl.UInt8.logxor in1i oi in
      Hacl.SBuffer.upd output i oi;
      xor_bytes output in1 i
    end

val and_bytes: output:bytes -> in1:bytes{disjoint in1 output} ->
  len:u32{v len <= length output /\ v len <= length in1} -> STL unit
  (requires (fun h -> live h output /\ live h in1))
  (ensures  (fun h0 _ h1 -> live h0 output /\ live h0 in1 /\ live h1 output /\ live h1 in1
    /\ modifies_1 output h0 h1 ))
let rec and_bytes output in1 len =
  if len =^ 0ul then ()
  else
    begin
      let i    = FStar.UInt32.sub_mod len 1ul in
      let in1i = Hacl.SBuffer.index in1 i in
      let oi   = Hacl.SBuffer.index output i in
      let oi   = Hacl.UInt8.logand in1i oi in
      Hacl.SBuffer.upd output i oi;
      and_bytes output in1 i
    end


val setall_aux: (b:bytes) -> (l:u32{length b = v l}) -> (x:u8) -> (pos:u32{v pos <= length b /\ v pos < pow2 32})
  -> STL unit
        (requires (fun h -> live h b))
        (ensures  (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))

let rec setall_aux b l v pos =
  if lt pos l then begin
    Hacl.SBuffer.upd b pos (uint8_to_sint8 v);
    setall_aux b l v (FStar.UInt32.add pos 1ul)  end
  else ()


val setall: (b:bytes) -> (l:u32{length b = v l}) -> (x:u8)
  -> STL unit
        (requires (fun h -> live h b))
        (ensures  (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))
let setall b l v = setall_aux b l v 0ul



//
// Naive setmask
// * Be careful, this is not length hiding because if explicitely check
// * the position where the byte is supposed to change
//

val setmask': mask:bytes -> masklen:u32{v masklen = Hacl.SBuffer.length mask /\ v masklen < pow2 32} -> byteval1:s8 -> byteval2:s8 -> pos:u32{v pos <= v masklen} -> i:u32{v i >= 0 /\ v i < v masklen}
  -> STL unit
        (requires (fun h -> live h mask))
        (ensures  (fun h0 _ h1 -> live h1 mask /\ modifies_1 mask h0 h1))

let rec setmask' mask masklen b1 b2 pos i =
  if FStar.UInt32.eq i 0ul then ()
  else begin
    if FStar.UInt32.lt i pos then begin
      Hacl.SBuffer.upd mask i b1 end
    else begin
      Hacl.SBuffer.upd mask i b2 end;
    setmask' mask masklen b1 b2 pos (FStar.UInt32.sub i 1ul)
  end

val setmask: mask:bytes -> masklen:u32{v masklen = Hacl.SBuffer.length mask /\ v masklen < pow2 32 /\ v masklen >= 1} -> byteval1:s8 -> byteval2:s8 -> pos:u32{v pos <= v masklen}
  -> STL unit
        (requires (fun h -> live h mask))
        (ensures  (fun h0 _ h1 -> live h1 mask /\ modifies_1 mask h0 h1))
let setmask mask masklen b1 b2 pos = setmask' mask masklen b1 b2 pos (FStar.UInt32.sub masklen 1ul)


(* val setmask': mask:bytes -> masklen:s32 -> byteval1:s8 -> byteval2:s8 -> pos:s32 -> i:s32  *)
(*   -> STL unit *)
(*         (requires (fun h -> live h mask)) *)
(*         (ensures  (fun h0 _ h1 -> live h1 mask /\ modifies_1 mask h0 h1)) *)

(* let rec setmask' mask masklen byteval1 byteval2 pos i = *)
(*   let max = S32.add pos (uint32_to_sint32 1ul) in *)
(*   if i = masklen then () *)
(*   else *)
(*     let r = S8.logor (S8.logand (S8.lt_mask i pos) byteval1) *)
(*                      (S8.logand (S8.lognot (S32.lt_mask i max)) byteval2) in *)
(*     Hacl.SBuffer.upd mask i r; *)
(*     setmask' mask masklen pos (S32.add i (uint32_to_sint32 1ul)) *)

(* val setmask: mask:bytes -> masklen:s32 -> byteval1:s8 -> byteval2:s8 -> pos:s32 -> i:s32  *)
(*   -> STL unit *)
(*         (requires (fun h -> live h mask)) *)
(*         (ensures  (fun h0 _ h1 -> live h1 mask /\ modifies_1 mask h0 h1)) *)
(* let setmask mask masklen pos = setmask' mask masklen pos (uint32_to_sint32 0ul) *)
