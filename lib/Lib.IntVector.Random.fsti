module Lib.IntVector.Random

open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer


(* Stateful interfaces assumed for calling RDRAND *)
val rdrand_get_bytes: #s:secrecy_level -> n:size_t -> rand:lbuffer (uint_t U8 s) n ->
  Stack unit (requires (fun h -> live h rand))
             (ensures  (fun h0 _ h1 -> live h1 rand /\ modifies1 rand h0 h1))

val rdrand32_step: #s:secrecy_level -> rand:(lbuffer (uint_t U32 s) 1ul) ->
  Stack unit (requires (fun h -> live h rand))
             (ensures  (fun h0 _ h1 -> live h1 rand /\ modifies1 rand h0 h1))

val rdrand64_step: #s:secrecy_level -> rand:(lbuffer (uint_t U64 s) 1ul) ->
  Stack unit (requires (fun h -> live h rand))
             (ensures  (fun h0 _ h1 -> live h1 rand /\ modifies1 rand h0 h1))

(* Stateful interfaces assumed for calling RDSEED *)
val rdseed32_step: #s:secrecy_level -> seed:(lbuffer (uint_t U32 s) 1ul) ->
  Stack unit (requires (fun h -> live h seed))
             (ensures  (fun h0 _ h1 -> live h1 seed /\ modifies1 seed h0 h1))

val rdseed64_step: #s:secrecy_level -> seed:(lbuffer (uint_t U64 s) 1ul) ->
  Stack unit (requires (fun h -> live h seed))
             (ensures  (fun h0 _ h1 -> live h1 seed /\ modifies1 seed h0 h1))
