module Hacl.Operations

open FStar.HyperStack
open FStar.ST
open FStar.Buffer
open FStar.Buffer.Quantifiers
open Math.Logic.Axioms
open FStar.UInt32
open Hacl.Cast



(* Module aliases *)
module U8  = FStar.UInt8
module S8  = Hacl.UInt8
module U16  = FStar.UInt16
module S16  = Hacl.UInt16
module U32 = FStar.UInt32
module S32 = Hacl.UInt32
module U64  = FStar.UInt64
module S64  = Hacl.UInt64
module SB  = Hacl.SBuffer
module FB  = FStar.Buffer
module MLA = Math.Logic.Axioms


(* Define base types *)
let u8 = FStar.UInt8.t
let s8 = Hacl.UInt8.t
let u16 = FStar.UInt16.t
let s16 = Hacl.UInt16.t
let u32 = FStar.UInt32.t
let s32 = Hacl.UInt32.t
let u64 = FStar.UInt64.t
let s64 = Hacl.UInt64.t
let bytes = Hacl.SBuffer.u8s


#set-options "--z3timeout 10"

//
// Word rotations
// This should probably relocated to Hacl.UInt32...
//

let rotate_right (a:s32) (b:u32{v b <= 32}) : Tot s32 =
  S32.logor (S32.shift_right a b) (S32.shift_left a (U32.sub 32ul b))


//
// Inplace NOT of a buffer
//

val not_bytes: buf:bytes -> len:u32{v len <= length buf}
  -> STL unit
        (requires (fun h -> live h buf))
        (ensures  (fun h0 _ h1 -> live h0 buf /\ live h1 buf /\ modifies_1 buf h0 h1
                  /\ (forall (i:nat). {:pattern (Seq.index (FB.as_seq h1 buf) i)}
                              (i < (U32.v len)) ==> (Seq.index (FB.as_seq h1 buf) i
                                                   == S8.lognot (Seq.index (FB.as_seq h0 buf) i)))
                  /\ (forall (i:nat). {:pattern (Seq.index (FB.as_seq h1 buf) i)}
                              (i >= (U32.v len) /\ i < length buf) ==> (Seq.index (FB.as_seq h1 buf) i
                                                                     == (Seq.index (FB.as_seq h0 buf) i)))))

let rec not_bytes buf len =
  if len =^ 0ul then ()
  else begin
    let i = U32.sub len 1ul in
    let r = S8.lognot (SB.index buf i) in
    SB.upd buf i r;
    not_bytes buf i end


//
// Inplace XOR of two buffers
//

val xor_bytes: output:bytes -> input:bytes{disjoint input output} -> len:u32{v len <= length output /\ v len <= length input}
  -> STL unit
        (requires (fun h -> live h output /\ live h input))
        (ensures  (fun h0 _ h1 -> live h0 output /\ live h0 input
                  /\ (live h1 output /\ live h1 input /\ modifies_1 output h0 h1)
                  /\ (forall (i:nat). {:pattern (Seq.index (FB.as_seq h1 output) i)}
                              (i < (U32.v len)) ==> (Seq.index (FB.as_seq h1 output) i
                                                   == S8.logxor (Seq.index (FB.as_seq h0 output) i)
                                                                (Seq.index (FB.as_seq h0 input) i)))
                  /\ (forall (i:nat). {:pattern (Seq.index (FB.as_seq h1 output) i)}
                              (i >= (U32.v len) /\ i < length output) ==> (Seq.index (FB.as_seq h1 output) i
                                                                       == (Seq.index (FB.as_seq h0 output) i)))))

let rec xor_bytes output input len =
  if len =^ 0ul then ()
  else begin
    let i = U32.sub len 1ul in
    let r = S8.logxor (SB.index output i) (SB.index input i) in
    SB.upd output i r;
    xor_bytes output input i end


//
// Inplace AND of two buffers
//

val and_bytes: output:bytes -> input:bytes{disjoint input output} -> len:u32{v len <= length output /\ v len <= length input}
  -> STL unit
        (requires (fun h -> live h output /\ live h input))
        (ensures  (fun h0 _ h1 -> live h0 output /\ live h0 input
                  /\ (live h1 output /\ live h1 input /\ modifies_1 output h0 h1)
                  /\ (forall (i:nat). {:pattern (Seq.index (FB.as_seq h1 output) i)}
                              (i < (U32.v len)) ==> (Seq.index (FB.as_seq h1 output) i
                                                   == S8.logand (Seq.index (FB.as_seq h0 output) i)
                                                                (Seq.index (FB.as_seq h0 input) i)))
                  /\ (forall (i:nat). {:pattern (Seq.index (FB.as_seq h1 output) i)}
                              (i >= (U32.v len) /\ i < length output) ==> (Seq.index (FB.as_seq h1 output) i
                                                                       == (Seq.index (FB.as_seq h0 output) i)))))

let rec and_bytes output input len =
  if len =^ 0ul then ()
  else begin
    let i = U32.sub len 1ul in
    let r = S8.logand (SB.index output i) (SB.index input i) in
    SB.upd output i r;
    and_bytes output input i end


//
// Inplace OR of two buffers
//

val or_bytes: output:bytes -> input:bytes{disjoint input output} -> len:u32{v len <= length output /\ v len <= length input}
  -> STL unit
        (requires (fun h -> live h output /\ live h input))
        (ensures  (fun h0 _ h1 -> live h0 output /\ live h0 input
                  /\ (live h1 output /\ live h1 input /\ modifies_1 output h0 h1)
                  /\ (forall (i:nat). {:pattern (Seq.index (FB.as_seq h1 output) i)}
                              (i < (U32.v len)) ==> (Seq.index (FB.as_seq h1 output) i
                                                   == S8.logor (Seq.index (FB.as_seq h0 output) i)
                                                                (Seq.index (FB.as_seq h0 input) i)))
                  /\ (forall (i:nat). {:pattern (Seq.index (FB.as_seq h1 output) i)}
                              (i >= (U32.v len) /\ i < length output) ==> (Seq.index (FB.as_seq h1 output) i
                                                                       == (Seq.index (FB.as_seq h0 output) i)))))

let rec or_bytes output input len =
  if len =^ 0ul then ()
  else begin
    let i = U32.sub len 1ul in
    let r = S8.logor (SB.index output i) (SB.index input i) in
    SB.upd output i r;
    or_bytes output input i end


//
// Branch_mask
//

val branch_u8_mask: v1:u8 -> v2:u8 -> mask:u8{U8.v mask = U8.v MLA.u8_zero \/ U8.v mask = U8.v MLA.u8_ones}
  -> Tot (res:u8{((U8.v mask = U8.v MLA.u8_ones) ==> U8.v res = U8.v v1)
                /\ ((U8.v mask = U8.v MLA.u8_zero) ==> U8.v res = U8.v v2)})

let branch_u8_mask v1 v2 mask = U8.logor (U8.logand v1 mask) (U8.logand v2 (U8.lognot mask))

val branch_s8_mask: v1:s8 -> v2:s8 -> mask:s8{S8.v mask = S8.v MLA.s8_zero \/ S8.v mask = S8.v MLA.s8_ones}
  -> Tot (res:s8{((S8.v mask = S8.v MLA.s8_ones) ==> S8.v res = S8.v v1)
                /\ ((S8.v mask = S8.v MLA.s8_zero) ==> S8.v res = S8.v v2)})

let branch_s8_mask v1 v2 mask = S8.logor (S8.logand v1 mask) (S8.logand v2 (S8.lognot mask))


val branch_u16_mask: v1:u16 -> v2:u16 -> mask:u16{U16.v mask = U16.v MLA.u16_zero \/ U16.v mask = U16.v MLA.u16_ones}
  -> Tot (res:u16{((U16.v mask = U16.v MLA.u16_ones) ==> U16.v res = U16.v v1)
                /\ ((U16.v mask = U16.v MLA.u16_zero) ==> U16.v res = U16.v v2)})

let branch_u16_mask v1 v2 mask = U16.logor (U16.logand v1 mask) (U16.logand v2 (U16.lognot mask))

val branch_s16_mask: v1:s16 -> v2:s16 -> mask:s16{S16.v mask = S16.v MLA.s16_zero \/ S16.v mask = S16.v MLA.s16_ones}
  -> Tot (res:s16{((S16.v mask = S16.v MLA.s16_ones) ==> S16.v res = S16.v v1)
                /\ ((S16.v mask = S16.v MLA.s16_zero) ==> S16.v res = S16.v v2)})

let branch_s16_mask v1 v2 mask = S16.logor (S16.logand v1 mask) (S16.logand v2 (S16.lognot mask))


val branch_u32_mask: v1:u32 -> v2:u32 -> mask:u32{U32.v mask = U32.v MLA.u32_zero \/ U32.v mask = U32.v MLA.u32_ones}
  -> Tot (res:u32{((U32.v mask = U32.v MLA.u32_ones) ==> U32.v res = U32.v v1)
                /\ ((U32.v mask = U32.v MLA.u32_zero) ==> U32.v res = U32.v v2)})

let branch_u32_mask v1 v2 mask = U32.logor (U32.logand v1 mask) (U32.logand v2 (U32.lognot mask))

val branch_s32_mask: v1:s32 -> v2:s32 -> mask:s32{S32.v mask = S32.v MLA.s32_zero \/ S32.v mask = S32.v MLA.s32_ones}
  -> Tot (res:s32{((S32.v mask = S32.v MLA.s32_ones) ==> S32.v res = S32.v v1)
                /\ ((S32.v mask = S32.v MLA.s32_zero) ==> S32.v res = S32.v v2)})

let branch_s32_mask v1 v2 mask = S32.logor (S32.logand v1 mask) (S32.logand v2 (S32.lognot mask))


val branch_u64_mask: v1:u64 -> v2:u64 -> mask:u64{U64.v mask = U64.v MLA.u64_zero \/ U64.v mask = U64.v MLA.u64_ones}
  -> Tot (res:u64{((U64.v mask = U64.v MLA.u64_ones) ==> U64.v res = U64.v v1)
                /\ ((U64.v mask = U64.v MLA.u64_zero) ==> U64.v res = U64.v v2)})

let branch_u64_mask v1 v2 mask = U64.logor (U64.logand v1 mask) (U64.logand v2 (U64.lognot mask))

val branch_s64_mask: v1:s64 -> v2:s64 -> mask:s64{S64.v mask = S64.v MLA.s64_zero \/ S64.v mask = S64.v MLA.s64_ones}
  -> Tot (res:s64{((S64.v mask = S64.v MLA.s64_ones) ==> S64.v res = S64.v v1)
                /\ ((S64.v mask = S64.v MLA.s64_zero) ==> S64.v res = S64.v v2)})

let branch_s64_mask v1 v2 mask = S64.logor (S64.logand v1 mask) (S64.logand v2 (S64.lognot mask))


//
// Setall
//

val setall_aux: #t:Type -> b:buffer t -> z:t -> len:U32.t -> ctr:U32.t -> STL unit
  (requires (fun h ->
            (live h b)
            /\ (U32.v len = Seq.length (FB.as_seq h b))
            /\ (U32.v ctr <= U32.v len)
            /\ (forall (i:nat). {:pattern (Seq.index (FB.as_seq h b) i)}
                        (i < (U32.v ctr) ==> Seq.index (FB.as_seq h b) i == z))))
  (ensures  (fun h0 _ h1 ->
            (live h0 b /\ live h1 b /\ modifies_1 b h0 h1)
            /\ (U32.v len = Seq.length (FB.as_seq h1 b))
            /\ (U32.v ctr <= U32.v len)
            /\ (Seq.length (FB.as_seq h0 b) = Seq.length (FB.as_seq h1 b))
            /\ (forall (i:nat). {:pattern (Seq.index (FB.as_seq h1 b) i)}
                        (i < (U32.v len) ==> Seq.index (FB.as_seq h1 b) i == z))))

let rec setall_aux #t b z len ctr =
  if (len -^ ctr) =^ 0ul then ()
  else begin
    FB.upd b ctr z;
    setall_aux #t b z len (ctr +^ 1ul) end

val setall: #t:Type -> b:buffer t -> z:t -> len:U32.t -> STL unit
  (requires (fun h ->
            (live h b)
            /\ (U32.v len = Seq.length (FB.as_seq h b))))
  (ensures  (fun h0 _ h1 ->
            (live h0 b /\ live h1 b /\ modifies_1 b h0 h1)
            /\ (U32.v len = Seq.length (FB.as_seq h1 b))
            /\ (Seq.length (FB.as_seq h0 b) = Seq.length (FB.as_seq h1 b))
            /\ (forall (i:nat). {:pattern (Seq.index (FB.as_seq h1 b) i)}
                        (i < (U32.v len) ==> Seq.index (FB.as_seq h1 b) i == z))))

let setall #t b z len = setall_aux #t b z len 0ul


//
// Set2
//

val set2': buf:bytes -> buflen:u32{v buflen = SB.length buf /\ v buflen < pow2 32} -> byteval1:s8 -> byteval2:s8 -> posi:s32{S32.v posi <= v buflen} -> i:u32{v i >= 0 /\ v i <= v buflen}
  -> STL unit
        (requires (fun h -> live h buf))
        (ensures  (fun h0 _ h1 -> live h1 buf /\ modifies_1 buf h0 h1))

let rec set2' buf buflen b1 b2 posi i =
  if U32.lt i buflen then
    let m32 = S32.lt_mask (uint32_to_sint32 i) posi in
    let m8 = sint32_to_sint8 m32 in
    let b = S8.logor (S8.logand m8 b1)
                     (S8.logand (S8.lognot m8) b2) in
    SB.upd buf i b;
    set2' buf buflen b1 b2 posi (U32.add i 1ul)
  else ()

val set2: buf:bytes -> buflen:u32{v buflen = SB.length buf /\ v buflen < pow2 32} -> byteval1:s8 -> byteval2:s8 -> posi:s32{S32.v posi <= v buflen}
  -> STL unit
        (requires (fun h -> live h buf))
        (ensures  (fun h0 _ h1 -> live h1 buf /\ modifies_1 buf h0 h1))
let set2 buf buflen b1 b2 posi = set2' buf buflen b1 b2 posi 0ul


//
// Setbuf3
//

val setbuf3': buf:bytes -> buflen:u32{v buflen = SB.length buf /\ v buflen < pow2 32} -> byteval1:s8 -> byteval2:s8 -> byteval3:s8 -> posi1:s32{S32.v posi1 <= v buflen} -> posi2:s32{S32.v posi1 < S32.v posi2 /\ S32.v posi2 <= v buflen} -> i:u32{v i >= 0 /\ v i <= v buflen}
  -> STL unit
        (requires (fun h -> live h buf))
        (ensures  (fun h0 _ h1 -> live h1 buf /\ modifies_1 buf h0 h1))

let rec setbuf3' buf buflen b1 b2 b3 posi1 posi2 i =
  if U32.lt i buflen then
    let c1  = sint32_to_sint8 (S32.gte_mask (uint32_to_sint32 i) posi1) in
    let c2  = sint32_to_sint8 (S32.gte_mask (uint32_to_sint32 i) posi2) in
    let nc2 = S8.lognot c2 in
    let r1 = S8.logand b1 (S8.logand (S8.lognot c1) (S8.lognot c2)) in
    let r2 = S8.logand b2 (S8.logand c1 (S8.lognot c2)) in
    let r3 = S8.logand b3 (S8.logand c1 c2) in
    let b = S8.logor r1 (S8.logor r2 r3) in
    SB.upd buf i b;
    setbuf3' buf buflen b1 b2 b3 posi1 posi2 (U32.add i 1ul)
  else ()

val setbuf3: buf:bytes -> buflen:u32{v buflen = SB.length buf /\ v buflen < pow2 32} -> byteval1:s8 -> byteval2:s8 -> byteval3:s8 -> posi1:s32{S32.v posi1 <= v buflen} -> posi2:s32{S32.v posi1 < S32.v posi2 /\ S32.v posi2 <= v buflen}
  -> STL unit
        (requires (fun h -> live h buf))
        (ensures  (fun h0 _ h1 -> live h1 buf /\ modifies_1 buf h0 h1))
let setbuf3 buf buflen b1 b2 b3 posi1 posi2 = setbuf3' buf buflen b1 b2 b3 posi1 posi2 0ul


//
// Copymask
//

val copymask': buf:bytes -> bufstart:s32 -> bufstop:s32{S32.v bufstart <= S32.v bufstop} -> out:bytes{disjoint out buf} -> masklen:u32{v masklen = length out /\ v masklen = length buf /\ S32.v bufstop <= v masklen} -> i:u32{v i <= v masklen}
  -> STL unit
        (requires (fun h -> live h buf /\ live h out))
        (ensures  (fun h0 _ h1 -> live h1 buf /\ live h1 out /\ modifies_1 out h0 h1))

let rec copymask' buf bufstart bufstop out masklen i =
  if U32.lt i masklen then
    let c1 = sint32_to_sint8 (S32.gte_mask (uint32_to_sint32 i) bufstart) in
    let c2 = sint32_to_sint8 (S32.gte_mask (uint32_to_sint32 i) bufstop) in
    let nc2 = S8.lognot c2 in
    let mask = S8.logand c1 nc2 in
    let bout = SB.index out i in
    let bbuf = SB.index buf i in
    let r1 = S8.logand bbuf mask in
    let r2 = S8.logand bout (S8.lognot mask) in
    let r = S8.logor r1 r2 in
    SB.upd out i r;
    copymask' buf bufstart bufstop out masklen (U32.add i 1ul)
  else ()


val copymask: buf:bytes -> bufstart:s32 -> bufstop:s32{S32.v bufstart <= S32.v bufstop} -> out:bytes{disjoint out buf} -> masklen:u32{v masklen = length out /\ v masklen = length buf /\ S32.v bufstop <= v masklen}
  -> STL unit
        (requires (fun h -> live h buf /\ live h out))
        (ensures  (fun h0 _ h1 -> live h0 out /\ live h1 out /\ modifies_1 out h0 h1))

let rec copymask buf bufstart bufstop out masklen = copymask' buf bufstart bufstop out masklen 0ul
