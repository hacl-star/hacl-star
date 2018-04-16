module Hacl.Hardware.Intel.CPUID

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.HyperStack.ST
open FStar.HyperStack
open FStar.Buffer
open FStar.UInt32

open Hacl.Hardware.Intel.CPUID.Assumed



(* Detect if the processor is an Intel CPU *)
val detect_intel_cpu: unit
  -> Stack bool
          (requires (fun h -> True))
          (ensures  (fun h0 _ h1 -> h0 == h1))
let detect_intel_cpu () = if (_is_intel_cpu() = 1ul) then true else false


(* Detect if the processor has support for the RDRAND DRNG feature *)
val detect_intel_feature_rdrand: unit
  -> Stack bool (requires (fun h0 -> True))
               (ensures  (fun h0 _ h1 -> modifies_0 h0 h1))

let detect_intel_feature_rdrand () =
  push_frame();
  let features = { eax = 0ul; ebx = 0ul; ecx = 0ul; edx = 0ul; } in
  let rfeatures = Buffer.create features 1ul in
  let r =
    match detect_intel_cpu () with
    | false -> false
    | true ->
      (* Retrieve the cpuid information from the CPU *)
      cpuid rfeatures 1ul 0ul;
      (* Check the bit for the RDRAND feature *)
      assert_norm (0x40000000 < pow2 32);
      if ((let a = rfeatures.(0ul) in a.ecx &^ 0x40000000ul) =^ 0x40000000ul) then true else false
  in
  pop_frame();
  r


(* Detect if the processor has support for the RDSEED DRNG feature *)
val detect_intel_feature_rdseed: unit
  -> Stack bool (requires (fun h0 -> True))
               (ensures  (fun h0 _ h1 -> modifies_0 h0 h1))

let detect_intel_feature_rdseed () =
  push_frame();
  let features = { eax = 0ul; ebx = 0ul; ecx = 0ul; edx = 0ul; } in
  let rfeatures = Buffer.create features 1ul in
  let r =
    match detect_intel_cpu () with
    | false -> false
    | true ->
      (* Retrieve the cpuid information from the CPU *)
      cpuid rfeatures 7ul 0ul;
      (* Check the bit for the RDSEED feature *)
      assert_norm (0x40000 < pow2 32);
      if ((let a = rfeatures.(0ul) in a.ebx &^ 0x40000ul) =^ 0x40000ul) then true else false
  in
  pop_frame();
  r

