module Lib.RandomBuffer.Hardware

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.HyperStack.ST



(* Get a N random bytes from the CPU *)
val random_bytes: rand:uint8_p -> n:uint32_t ->
  Stack unit (requires (fun h -> live h rand))
             (ensures  (fun h0 _ h1 -> live h1 rand /\ modifies_1 rand h0 h1))

let random_bytes rand n = HTRHA.rdrand_get_bytes n rand



(* Get a random uint32_t from the CPU *)
val random_uint32: unit -> StackInline uint32_t (requires (fun h -> True))
                                               (ensures  (fun h0 _ h1 -> True))
let random_uint32 () =
  push_frame();
  let rr32 = Buffer.create 0ul 1ul in HTRHA.rdrand32_step rr32;
  let r = rr32.(0ul) in
  pop_frame();
  r


(* Get a random uint64_t from the CPU *)
val random_uint64: unit -> StackInline uint64_t (requires (fun h -> True))
                                               (ensures  (fun h0 _ h1 -> True))
let random_uint64 () =
  push_frame();
  let rr64 = Buffer.create 0uL 1ul in HTRHA.rdrand64_step rr64;
  let r = rr64.(0ul) in
  pop_frame();
  r


(* Get a uint64_t seed from the CPU *)
val randseed_uint32: unit -> Stack uint32_t (requires (fun h -> True))
                                           (ensures  (fun h0 _ h1 -> True))
let randseed_uint32 () =
  push_frame();
  let rs32 = Buffer.create 0ul 1ul in HTRHA.rdseed32_step rs32;
  let r = rs32.(0ul) in
  pop_frame();
  r


(* Get a uint64_t seed from the CPU *)
val randseed_uint64: unit -> Stack uint64_t (requires (fun h -> True))
                                           (ensures  (fun h0 _ h1 -> True))
let randseed_uint64 () =
  push_frame();
  let rs64 = Buffer.create 0uL 1ul in HTRHA.rdseed64_step rs64;
  let r = rs64.(0ul) in
  pop_frame();
  r
