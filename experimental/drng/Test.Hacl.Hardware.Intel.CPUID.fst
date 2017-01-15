module Test.Hacl.Hardware.Intel.CPUID

open Hacl.Hardware.Intel.CPUID



let check_for_intel_drng () : St unit =
  if (_is_intel_cpu() = 1ul) then
    C.print_string (C.string_of_literal "Intel DRNG is supported on this hardware !\n")
  else begin
    C.print_string (C.string_of_literal "Intel DRNG is not available on this hardware !\n")
  end; ()


(* int intel_check_drng(){ *)

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

(* int main () { *)

(*   if (intel_check_drng() == 0) { *)
(*     printf("Intel CPU with RDRAND feature Enabled !\n"); *)
(*   } else { *)
(*     perror("This hardware does not support DRNG !\n"); *)
(*   } *)
(*   return 0; *)
(* } *)



(* val check_hardware: unit  *)
(*   -> Stack uint8_t (requires (fun h -> True)) *)
(*                   (ensures  (fun _ _ _ -> True)) *)

(* let check_hardware () = *)
(*   if (_is_intel_cpu()) then *)


let main () =
  push_frame();
  check_for_intel_drng ();
  pop_frame();
  C.exit_success
