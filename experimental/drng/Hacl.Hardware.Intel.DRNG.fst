module Hacl.Hardware.Intel.DRNG

open FStar.ST
open FStar.Buffer
open FStar.HyperStack

(* Aliases for modules *)
module U8  = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module FB  = FStar.Buffer
module HS  = FStar.HyperStack

module AM  = Hacl.Hardware.Intel.DRNG.Assumed


(* Aliases for types *)
let u8  = FStar.UInt8.t 
let u32 = FStar.UInt32.t
let u64 = FStar.UInt64.t
let bytes = FStar.Buffer.buffer u8



(* Get a random uint32_t from the CPU *)
val random_uint32: unit -> Stack u32 (requires (fun h -> True))
                                    (ensures  (fun h0 _ h1 -> modifies_0 h0 h1))
let random_uint32 () =
  push_frame();
  let rr32 = Buffer.create 0ul 1ul in AM.rdrand32_step rr32; 
  let r = rr32.(0ul) in
  pop_frame();
  r


(* Get a random uint64_t from the CPU *)
val random_uint64: unit -> Stack u64 (requires (fun h -> True))
                                    (ensures  (fun h0 _ h1 -> modifies_0 h0 h1))
let random_uint64 () =
  push_frame();
  let rr64 = Buffer.create 0uL 1ul in AM.rdrand64_step rr64; 
  let r = rr64.(0ul) in
  pop_frame();
  r


#set-options "--lax"

(* Get a N random bytes from the CPU *)
val random_bytes: rand:bytes -> n:u32
  -> Stack unit (requires (fun h -> True))
               (ensures  (fun h0 _ h1 -> live h1 rand /\ modifies_1 rand h0 h1))
let random_bytes rand n = AM.rdrand_get_bytes n rand


#reset-options


(* Get a uint64_t seed from the CPU *)
val randseed_uint32: unit -> Stack u32 (requires (fun h -> True))
                                      (ensures  (fun h0 _ h1 -> modifies_0 h0 h1))
let randseed_uint32 () =
  push_frame();
  let rs32 = Buffer.create 0ul 1ul in AM.rdseed32_step rs32;
  let r = rs32.(0ul) in
  pop_frame();
  r


(* Get a uint64_t seed from the CPU *)
val randseed_uint64: unit -> Stack u64 (requires (fun h -> True))
                                      (ensures  (fun h0 _ h1 -> modifies_0 h0 h1))
let randseed_uint64 () =
  push_frame();
  let rs64 = Buffer.create 0uL 1ul in AM.rdseed64_step rs64;
  let r = rs64.(0ul) in
  pop_frame();
  r
