module Hacl.Operations

open FStar.HyperStack
open FStar.HST
open FStar.Buffer
open FStar.UInt32
open Hacl.Cast

(* Module aliases *)
module U32 = FStar.UInt32
module S32 = Hacl.UInt32
module S8  = Hacl.UInt8
module SB  = Hacl.SBuffer

(* Define base types *)
let u8 = FStar.UInt8.t
let s8 = Hacl.UInt8.t
let u32 = FStar.UInt32.t
let s32 = Hacl.UInt32.t
let bytes = Hacl.SBuffer.u8s





//
// Word rotations
// This should probably relocated to Hacl.UInt32...
//

let rotate_right (a:s32) (b:u32{v b <= 32}) : Tot s32 =
  S32.logor (S32.shift_right a b) (S32.shift_left a (U32.sub 32ul b))


//
// Inplace XOR of two buffers
//

val xor_bytes: output:bytes -> in1:bytes{disjoint in1 output} ->
  len:u32{v len <= length output /\ v len <= length in1} -> STL unit
  (requires (fun h -> live h output /\ live h in1))
  (ensures  (fun h0 _ h1 -> live h0 output /\ live h0 in1 /\ live h1 output /\ live h1 in1
    /\ modifies_1 output h0 h1 ))
let rec xor_bytes output in1 len =
  if len =^ 0ul then ()
  else
    begin
      let i    = U32.sub_mod len 1ul in
      let in1i = SB.index in1 i in
      let oi   = SB.index output i in
      let oi   = S8.logxor in1i oi in
      SB.upd output i oi;
      xor_bytes output in1 i
    end


//
// Inplace AND of two buffers
//

val and_bytes: output:bytes -> in1:bytes{disjoint in1 output} ->
  len:u32{v len <= length output /\ v len <= length in1} -> STL unit
  (requires (fun h -> live h output /\ live h in1))
  (ensures  (fun h0 _ h1 -> live h0 output /\ live h0 in1 /\ live h1 output /\ live h1 in1
    /\ modifies_1 output h0 h1 ))
let rec and_bytes output in1 len =
  if len =^ 0ul then ()
  else
    begin
      let i    = U32.sub_mod len 1ul in
      let in1i = SB.index in1 i in
      let oi   = SB.index output i in
      let oi   = S8.logand in1i oi in
      SB.upd output i oi;
      and_bytes output in1 i
    end

//
// Inplace OR of two buffers
//

val or_bytes: output:bytes -> in1:bytes{disjoint in1 output} ->
  len:u32{v len <= length output /\ v len <= length in1} -> STL unit
  (requires (fun h -> live h output /\ live h in1))
  (ensures  (fun h0 _ h1 -> live h0 output /\ live h0 in1 /\ live h1 output /\ live h1 in1
    /\ modifies_1 output h0 h1 ))
let rec or_bytes output in1 len =
  if len =^ 0ul then ()
  else
    begin
      let i    = U32.sub_mod len 1ul in
      let in1i = SB.index in1 i in
      let oi   = SB.index output i in
      let oi   = S8.logor in1i oi in
      SB.upd output i oi;
      or_bytes output in1 i
    end


//
// Inplace NOR of two buffers
//

val nor_bytes: output:bytes -> in1:bytes{disjoint in1 output} ->
  len:u32{v len <= length output /\ v len <= length in1} -> STL unit
  (requires (fun h -> live h output /\ live h in1))
  (ensures  (fun h0 _ h1 -> live h0 output /\ live h0 in1 /\ live h1 output /\ live h1 in1
    /\ modifies_1 output h0 h1 ))
let rec nor_bytes output in1 len =
  if len =^ 0ul then ()
  else
    begin
      let i    = U32.sub_mod len 1ul in
      let in1i = SB.index in1 i in
      let oi   = SB.index output i in
      let oi   = S8.lognot (S8.logor in1i oi) in
      SB.upd output i oi;
      nor_bytes output in1 i
    end

//
// Setall
//

val setall': (b:bytes) -> (l:u32{length b = v l}) -> (x:s8) -> (pos:u32{v pos <= length b /\ v pos < pow2 32})
  -> STL unit
        (requires (fun h -> live h b))
        (ensures  (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))

let rec setall' buf buflen x pos =
  if lt pos buflen then begin
    SB.upd buf pos x;
    setall' buf buflen x (U32.add pos 1ul)  end
  else ()


val setall: (buf:bytes) -> (buflen:u32{length buf = v buflen}) -> (x:u8)
  -> STL unit
        (requires (fun h -> live h buf))
        (ensures  (fun h0 _ h1 -> live h1 buf /\ modifies_1 buf h0 h1))
let setall buf buflen x = setall' buf buflen x 0ul


//
// Setmask1
// (Setmask1 is an alias for setall)
//

val setmask1: (buf:bytes) -> (buflen:u32{length buf = v buflen}) -> (x:s8)
  -> STL unit
        (requires (fun h -> live h buf))
        (ensures  (fun h0 _ h1 -> live h1 buf /\ modifies_1 buf h0 h1))
let setmask1 b l v = setall' b l v 0ul


//
// Setmask2
//

val setmask2': mask:bytes -> masklen:u32{v masklen = SB.length mask /\ v masklen < pow2 32} -> byteval1:s8 -> byteval2:s8 -> pos:s32{v pos <= v masklen} -> i:u32{v i >= 0 /\ v i <= v masklen}
  -> STL unit
        (requires (fun h -> live h mask))
        (ensures  (fun h0 _ h1 -> live h1 mask /\ modifies_1 mask h0 h1))

let rec setmask2' mask masklen b1 b2 pos i =
  if U32.lt i masklen then
    let m32 = S32.lt_mask (uint32_to_sint32 i) pos in
    let m8 = sint32_to_sint8 m32 in
    let b = S8.logor (S8.logand m8 b1)
                     (S8.logand (S8.lognot m8) b2) in
    SB.upd mask i b;
    setmask2' mask masklen b1 b2 pos (U32.add i 1ul)
  else ()

val setmask2: mask:bytes -> masklen:u32{v masklen = SB.length mask /\ v masklen < pow2 32} -> byteval1:s8 -> byteval2:s8 -> pos:s32{v pos <= v masklen}
  -> STL unit
        (requires (fun h -> live h mask))
        (ensures  (fun h0 _ h1 -> live h1 mask /\ modifies_1 mask h0 h1))
let setmask2 mask masklen b1 b2 pos = setmask2' mask masklen b1 b2 pos 0ul


//
// Setmask3
//

val setmask3': mask:bytes -> masklen:u32{v masklen = SB.length mask /\ v masklen < pow2 32} -> byteval1:s8 -> byteval2:s8 -> byteval3:s8 -> pos1:s32{v pos1 <= v masklen} -> pos2:s32{v pos1 < v pos2 /\ v pos2 <= v masklen} -> i:u32{v i >= 0 /\ v i <= v masklen}
  -> STL unit
        (requires (fun h -> live h mask))
        (ensures  (fun h0 _ h1 -> live h1 mask /\ modifies_1 mask h0 h1))

let rec setmask3' mask masklen b1 b2 b3 pos1 pos2 i =
  if U32.lt i masklen then
    let c1  = sint32_to_sint8 (S32.gte_mask (uint32_to_sint32 i) pos1) in
    let c2  = sint32_to_sint8 (S32.gte_mask (uint32_to_sint32 i) pos2) in
    let nc2 = S8.lognot c2 in
    let r1 = S8.logand b1 (S8.logand (S8.lognot c1) (S8.lognot c2)) in
    let r2 = S8.logand b2 (S8.logand c1 (S8.lognot c2)) in
    let r3 = S8.logand b3 (S8.logand c1 c2) in
    let b = S8.logor r1 (S8.logor r2 r3) in
    SB.upd mask i b;
    setmask3' mask masklen b1 b2 b3 pos1 pos2 (U32.add i 1ul)
  else ()

val setmask3: mask:bytes -> masklen:u32{v masklen = SB.length mask /\ v masklen < pow2 32} -> byteval1:s8 -> byteval2:s8 -> byteval3:s8 -> pos1:s32{v pos1 <= v masklen} -> pos2:s32{v pos1 < v pos2 /\ v pos2 <= v masklen}
  -> STL unit
        (requires (fun h -> live h mask))
        (ensures  (fun h0 _ h1 -> live h1 mask /\ modifies_1 mask h0 h1))
let setmask3 mask masklen b1 b2 b3 pos1 pos2 = setmask3' mask masklen b1 b2 b3 pos1 pos2 0ul


//
// Copymask
//

val copymask': buf:bytes -> bufstart:s32 -> bufstop:s32{v bufstart < v bufstop} -> out:bytes{disjoint out buf} -> masklen:u32{v masklen = length out /\ v masklen = length buf /\ v bufstop < v masklen} -> i:u32{v i <= v masklen}
  -> STL unit
        (requires (fun h -> live h buf /\ live h out))
        (ensures  (fun h0 _ h1 -> live h1 buf /\ live h1 out /\ modifies_1 out h0 h1))

let rec copymask' buf bufstart bufstop out masklen i =
  if U32.lt i masklen then
    let c1 = sint32_to_sint8 (S32.gte_mask (uint32_to_sint32 i) bufstart) in
    let c2 = sint32_to_sint8 (S32.gte_mask (uint32_to_sint32 i) bufstop) in
    let nc2 = S8.lognot c2 in
    let bout = SB.index out i in
    let bbuf = SB.index buf i in
    let r1 = S8.logand bout (S8.logand (S8.lognot c1) (S8.lognot c2)) in
    let r2 = S8.logand bbuf (S8.logand c1 (S8.lognot c2)) in
    let r3 = S8.logand bout (S8.logand c1 c2) in
    let b = S8.logor r1 (S8.logor r2 r3) in
    SB.upd out i b;
    copymask' buf bufstart bufstop out masklen (U32.add i 1ul)
  else ()


val copymask: buf:bytes -> bufstart:s32 -> bufstop:s32{v bufstart < v bufstop} -> out:bytes{disjoint out buf} -> masklen:u32{v masklen = length out /\ v masklen = length buf /\ v bufstop < v masklen}
  -> STL unit
        (requires (fun h -> live h buf /\ live h out))
        (ensures  (fun h0 _ h1 -> live h1 buf /\ live h1 out /\ modifies_1 out h0 h1))

let rec copymask buf bufstart bufstop out masklen = copymask' buf bufstart bufstop out masklen 0ul
