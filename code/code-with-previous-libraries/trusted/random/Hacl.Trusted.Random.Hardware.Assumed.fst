module Hacl.Trusted.Random.Hardware.Assumed

open FStar.HyperStack.All
open FStar.HyperStack.ST
open FStar.Buffer
open FStar.HyperStack

(* Aliases for modules *)
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module FB  = FStar.Buffer
module HS  = FStar.HyperStack
module ST = FStar.HyperStack.ST

(* Aliases for types *)
let uint8_t  = FStar.UInt8.t
let uint32_t = FStar.UInt32.t
let uint64_t = FStar.UInt64.t
let uint8_p  = FStar.Buffer.buffer uint8_t


(* Stateful interfaces assumed for calling RDRAND *)
assume val rdrand_get_bytes: n:uint32_t -> rand:uint8_p ->
  Stack unit (requires (fun h -> live h rand))
             (ensures  (fun h0 _ h1 -> live h1 rand /\ modifies_1 rand h0 h1))

assume val rdrand32_step: rand:(buffer uint32_t) ->
  Stack unit (requires (fun h -> live h rand))
             (ensures  (fun h0 _ h1 -> live h1 rand /\ modifies_1 rand h0 h1))

assume val rdrand64_step: rand:(buffer uint64_t) ->
  Stack unit (requires (fun h -> live h rand))
             (ensures  (fun h0 _ h1 -> live h1 rand /\ modifies_1 rand h0 h1))

(* Stateful interfaces assumed for calling RDSEED *)
assume val rdseed32_step: seed:(buffer uint32_t) ->
  Stack unit (requires (fun h -> live h seed))
             (ensures  (fun h0 _ h1 -> live h1 seed /\ modifies_1 seed h0 h1))

assume val rdseed64_step: seed:(buffer uint64_t) ->
  Stack unit (requires (fun h -> live h seed))
             (ensures  (fun h0 _ h1 -> live h1 seed /\ modifies_1 seed h0 h1))
