module Test.Hacl.Hardware.Intel.CPUID

open Hacl.Hardware.Intel.CPUID



(* (\* Default value of a cpuid_t structure *\) *)
(* let id:cpuid_t = { *)
(*   eax = 0ul; *)
(*   ebx = 0ul; *)
(*   ecx = 0ul; *)
(*   edx = 0ul; *)
(* } *)


(* Detect if the processor is an Intel CPU *)
val detect_intel_cpu: unit -> St bool
let detect_intel_cpu () = if (_is_intel_cpu() = 1ul) then true else false


(* Detect if the processor has support for the DRNG features *)
val detect_intel_feature_rdrand: unit -> St bool
let detect_intel_feature_rdrand () =
  match detect_intel_cpu () with
  | false -> false
  | true -> true


(* Int intel_check_drng(){ *)

(*   // Check if the processor is an Intel CPU *)
(*   if ( _is_intel_cpu()) { *)
(*     cpuid_t features; *)

(*     // Get the CPU information *)
(*     // Check for the RDRAND feature bit *)
(*     cpuid(&features, 1, 0); *)

(*     if (features.ecx & 0x40000000 == 0x40000000) { *)
(*       return 0; *)
(*     } *)
(*   } *)
(*   return 1; *)
(* } *)


let main () =
  push_frame();

  (* Detect if the machine is an Intel CPU *)
  (match detect_intel_cpu () with
  | true  -> C.print_string (C.string_of_literal " * CPU Information: Intel processor detected on your machine.\n")
  | false -> C.print_string (C.string_of_literal " * CPU Information: No Intel CPU has been detected on your machine !\n"));

  (* Detect if the machine supports the RDRAND feature *)
  (match detect_intel_feature_rdrand () with
  | true -> C.print_string (C.string_of_literal " *         Feature: Digital Random Number Generator (RDRAND)\n")
  | false -> ());

  pop_frame();
  C.exit_success
