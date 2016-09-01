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
module FB  = FStar.Buffer

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


#set-options "--lax"

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

#reset-options "--z3timeout 10"

val lemma_x2: #a:Type -> h:mem -> b:buffer a{live h b} -> i:u32{v i < length b} 
  -> Lemma (requires (True)) 
          (ensures  (Seq.index (FB.as_seq h b) (U32.v i) == FB.get h b (U32.v i)))
          [SMTPat (Seq.index (FB.as_seq h b) (U32.v i))]

let lemma_x2 #a h b i = () 

val xor_bytes2: output:bytes -> input:bytes{disjoint input output} -> len:u32{v len <= length output /\ v len <= length input} 
  -> STL unit
        (requires (fun h -> 
                  (live h output /\ live h input)))
        (ensures  (fun h0 _ h1 -> 
                  (live h0 output /\ live h0 input) 
                  /\ (live h1 output /\ live h1 input /\ modifies_1 output h0 h1)
                  /\ (forall (i:nat). {:pattern (Seq.index (FB.as_seq h1 output) i)} 
                              i < (U32.v len) ==> (Seq.index (FB.as_seq h1 output) i
                                                 == S8.logxor (Seq.index (FB.as_seq h0 output) i)
                                                              (Seq.index (FB.as_seq h0 input) i)))
                  /\ (forall (i:nat). {:pattern (Seq.index (FB.as_seq h1 output) i)}
                              (i < 0 /\ i >= (U32.v len)) ==> (Seq.index (FB.as_seq h1 output) i 
                                                           == (Seq.index (FB.as_seq h0 output) i)))))

open FStar.Buffer.Quantifiers

let rec xor_bytes2 output input len =
  if len =^ 0ul then ()
  else begin
    let i = U32.sub len 1ul in
    let r = S8.logxor (SB.index output i) (SB.index input i) in
    SB.upd output i r;
    xor_bytes2 output input i end


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

#reset-options

//
// Setall
//

val setall_aux: #t:Type -> b:buffer t -> z:t -> len:U32.t -> ctr:U32.t -> STL unit
  (requires (fun h -> 
            (live h b)
            /\ (U32.v len = Seq.length (FB.as_seq h b))
            /\ (U32.v ctr <= U32.v len)
            /\ (forall (i:nat). i < (U32.v ctr) ==> Seq.index (FB.as_seq h b) i == z)))
  (ensures  (fun h0 _ h1 -> 
            (live h0 b /\ live h1 b /\ modifies_1 b h0 h1)
            /\ (U32.v len = Seq.length (FB.as_seq h1 b))
            /\ (U32.v ctr <= U32.v len)
            /\ (Seq.length (FB.as_seq h0 b) = Seq.length (FB.as_seq h1 b))
            /\ (forall (i:nat). i < (U32.v len) ==> Seq.index (FB.as_seq h1 b) i == z)))

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
            /\ (forall (i:nat). i < (U32.v len) ==> Seq.index (FB.as_seq h1 b) i == z)))

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
