module Test.Hacl.Hardware.Intel.CPUID

open FStar.ST
open FStar.HyperStack
open FStar.Buffer
open FStar.UInt32

open Hacl.Hardware.Intel.CPUID



(* Detect if the processor is an Intel CPU *)
val detect_intel_cpu: unit 
  -> Stack bool
          (requires (fun h -> True))
          (ensures  (fun h0 _ h1 -> h0 == h1))
let detect_intel_cpu () = if (_is_intel_cpu() = 1ul) then true else false


(* Detect if the processor has support for the DRNG features *)
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
      if ((let a = rfeatures.(0ul) in a.ecx &^ 0x40000000ul) =^ 0x40000000ul) then true else false
  in
  pop_frame();
  r


(* Entry point *)
let main () =
  
  (* Detect if the machine is an Intel CPU *)
  (match detect_intel_cpu () with
  | true  -> C.print_string (C.string_of_literal " * CPU Information: Intel processor detected on your machine.\n")
  | false -> C.print_string (C.string_of_literal " * CPU Information: No Intel CPU has been detected on your machine !\n"));

  (* Detect if the machine supports the RDRAND feature *)
  (match detect_intel_feature_rdrand () with
  | true -> C.print_string (C.string_of_literal " *         Feature: Digital Random Number Generator (RDRAND)\n")
  | false -> ());

  C.exit_success
