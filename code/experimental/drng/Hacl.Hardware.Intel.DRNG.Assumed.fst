module Hacl.Hardware.Intel.DRNG.Assumed

open Hacl.Hardware.Intel.DRNG

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.HyperStack.ST
open FStar.Buffer
open FStar.HyperStack

(* Aliases for modules *)
module U8  = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module FB  = FStar.Buffer
module HS  = FStar.HyperStack


(* Aliases for types *)
let u8  = FStar.UInt8.t 
let u32 = FStar.UInt32.t
let u64 = FStar.UInt64.t
let bytes = FStar.Buffer.buffer u8



(* assume val rdrand16_step: rand:(buffer u16) *)
(*   -> Stack unit (requires (fun h -> live h rand)) *)
(*                (ensures  (fun h0 _ h1 -> live h1 rand /\ modifies_1 rand h0 h1)) *)

assume val rdrand32_step: rand:(buffer u32)
  -> Stack unit (requires (fun h -> live h rand))
               (ensures  (fun h0 _ h1 -> live h1 rand /\ modifies_1 rand h0 h1))

assume val rdrand64_step: rand:(buffer u64)
  -> Stack unit (requires (fun h -> live h rand))
               (ensures  (fun h0 _ h1 -> live h1 rand /\ modifies_1 rand h0 h1))

assume val rdrand_get_bytes: n:u32 -> rand:bytes
  -> Stack unit (requires (fun h -> live h rand))
               (ensures  (fun h0 _ h1 -> live h1 rand /\ modifies_1 rand h0 h1))

(* assume val rdseed16_step: seed:(buffer u16) *)
(*   -> Stack unit (requires (fun h -> live h seed)) *)
(*                (ensures  (fun h0 _ h1 -> live h1 seed /\ modifies_1 seed h0 h1)) *)

assume val rdseed32_step: seed:(buffer u32)
  -> Stack unit (requires (fun h -> live h seed))
               (ensures  (fun h0 _ h1 -> live h1 seed /\ modifies_1 seed h0 h1))

assume val rdseed64_step: seed:(buffer u64)
  -> Stack unit (requires (fun h -> live h seed))
               (ensures  (fun h0 _ h1 -> live h1 seed /\ modifies_1 seed h0 h1))

