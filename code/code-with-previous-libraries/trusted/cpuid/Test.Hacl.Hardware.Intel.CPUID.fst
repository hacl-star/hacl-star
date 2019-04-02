module Test.Hacl.Hardware.Intel.CPUID

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open Hacl.Hardware.Intel.CPUID

(* Entry point *)
let main () =

  (* Detect if the machine is an Intel CPU *)
  (match detect_intel_cpu () with
  | true  -> C.String.print (C.String.of_literal " * CPU Information: Intel processor detected on your machine.\n")
  | false -> C.String.print (C.String.of_literal " * CPU Information: No Intel CPU has been detected on your machine !\n"));

  (* Detect if the machine supports the RDRAND feature *)
  (match detect_intel_feature_rdrand () with
  | true -> C.String.print (C.String.of_literal " *         Feature: Digital Random Number Generator (RDRAND)\n")
  | false -> ());

  (* Detect if the machine supports the RDSEED feature *)
  (match detect_intel_feature_rdseed () with
  | true -> C.String.print (C.String.of_literal " *         Feature: Digital Random Number Generator (RDSEED)\n")
  | false -> ());

  C.EXIT_SUCCESS
