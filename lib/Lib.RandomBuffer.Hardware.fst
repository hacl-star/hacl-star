module Lib.RandomBuffer.Hardware

open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer
open Lib.IntVector.Random


(**
val random_bytes:
    #s: secrecy_level
  -> n: size_t
  -> rand: lbuffer (uint_t U8 s) n ->
  Stack unit (requires (fun h -> live h rand))
             (ensures  (fun h0 _ h1 -> live h1 rand /\ modifies1 rand h0 h1)) *)

let random_bytes #s n rand = rdrand_get_bytes #s n rand


(**
val random_uint32: unit ->
  Stack uint32 (requires (fun h -> True))
               (ensures  (fun h0 _ h1 -> True)) *)

let random_uint32 () =
  push_frame();
  let rr32 = create 1ul (u32 0) in
  rdrand32_step #SEC rr32;
  let r = rr32.(0ul) in
  pop_frame();
  r

(**
val random_uint64: unit ->
  Stack uint64 (requires (fun h -> True))
               (ensures  (fun h0 _ h1 -> True)) *)

let random_uint64 () =
  push_frame();
  let rr64 = create 1ul (u64 0) in
  rdrand64_step #SEC rr64;
  let r = rr64.(0ul) in
  pop_frame();
  r


(**
val random_pub_uint32: unit ->
  Stack pub_uint32 (requires (fun h -> True))
                   (ensures  (fun h0 _ h1 -> True)) *)

let random_pub_uint32 () =
  push_frame();
  let rr32 = create 1ul 0ul in
  rdrand32_step #PUB rr32;
  let r = rr32.(0ul) in
  pop_frame();
  r


(**
val random_pub_uint64: unit ->
  Stack pub_uint64 (requires (fun h -> True))
                   (ensures  (fun h0 _ h1 -> True)) *)

let random_pub_uint64 () =
  push_frame();
  let rr64 = create 1ul 0uL in
  rdrand64_step #PUB rr64;
  let r = rr64.(0ul) in
  pop_frame();
  r


(**
val randseed_pub_uint32: unit ->
  Stack pub_uint32 (requires (fun h -> True))
                   (ensures  (fun h0 _ h1 -> True)) *)

let randseed_pub_uint32 () =
  push_frame();
  let rs32 = create 1ul 0ul in
  rdseed32_step #PUB rs32;
  let x = rs32.(0ul) in
  pop_frame ();
  x


(**
val randseed_pub_uint64: unit ->
  Stack pub_uint64 (requires (fun h -> True))
                   (ensures  (fun h0 _ h1 -> True)) *)

let randseed_pub_uint64 () =
  push_frame();
  let rs64 = create 1ul 0uL in
  rdseed64_step #PUB rs64;
  let x = rs64.(0ul) in
  pop_frame ();
  x
