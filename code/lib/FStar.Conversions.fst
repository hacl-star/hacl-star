module FStar.Conversions

open FStar.Mul
open FStar.Buffer
open FStar.Int.Cast

module U8  = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module FB  = FStar.Buffer


(* Definitions of base types *)
type u8      = FStar.UInt8.t 
type u32     = FStar.UInt32.t
type u64     = FStar.UInt64.t
type bytes   = FStar.Buffer.buffer u8
type uint32s = FStar.Buffer.buffer u32


(* Conversions *)
val be_bytes_of_uint64: b:bytes{length b >= 8} -> x:u64
  -> Stack unit
        (requires (fun h -> live h b))
        (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))

let be_bytes_of_uint64 output x =
 let b0 = uint64_to_uint8 (U64.logand (U64.shift_right x 56ul) 255uL) in
 let b1 = uint64_to_uint8 (U64.logand (U64.shift_right x 48ul) 255uL) in
 let b2 = uint64_to_uint8 (U64.logand (U64.shift_right x 40ul) 255uL) in
 let b3 = uint64_to_uint8 (U64.logand (U64.shift_right x 32ul) 255uL) in
 let b4 = uint64_to_uint8 (U64.logand (U64.shift_right x 24ul) 255uL) in
 let b5 = uint64_to_uint8 (U64.logand (U64.shift_right x 16ul) 255uL) in
 let b6 = uint64_to_uint8 (U64.logand (U64.shift_right x 8ul)  255uL) in
 let b7 = uint64_to_uint8 (U64.logand x 255uL) in
 upd output 0ul b0;
 upd output 1ul b1;
 upd output 2ul b2;
 upd output 3ul b3;
 upd output 4ul b4;
 upd output 5ul b5;
 upd output 6ul b6;
 upd output 7ul b7


#set-options "--z3rlimit 50"

val be_bytes_of_uint32s: output:bytes -> m:uint32s -> len:u32{U32.v len <= length output /\ U32.v len <=  4 * (length m)} 
  -> Stack unit
          (requires (fun h -> live h output /\ live h m))
          (ensures (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1 ))

let rec be_bytes_of_uint32s output m len =
  if len = 0ul then ()
  else
    begin
      let l4 = U32.div len 4ul in
      let l = U32.sub l4 1ul in
      let x = index m l in
      let b0 = uint32_to_uint8 (U32.logand (U32.shift_right x 24ul) 255ul) in
      let b1 = uint32_to_uint8 (U32.logand (U32.shift_right x 16ul) 255ul) in
      let b2 = uint32_to_uint8 (U32.logand (U32.shift_right x 8ul)  255ul) in
      let b3 = uint32_to_uint8 (U32.logand x 255ul) in
      let l4 = U32.sub len 4ul in
      FB.upd output l4 b0;
      FB.upd output (U32.add l4 1ul) b1;
      FB.upd output (U32.add l4 2ul) b2;
      FB.upd output (U32.add l4 3ul) b3;
      be_bytes_of_uint32s output m l4
    end
