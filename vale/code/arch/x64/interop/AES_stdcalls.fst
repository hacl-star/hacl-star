module AES_stdcalls

open Vale.Stdcalls.Aes
open Vale.AsLowStar.MemoryHelpers
open X64.MemoryAdapters
open Arch.Types

open Gcm_simplify

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let aes128_key_expansion_stdcall input_b output_b =
  let h0 = get() in

  let x, _ = aes128_key_expansion input_b output_b () in

  let h1 = get() in

  aes_simplify1 input_b h0;
  DV.length_eq (get_downview input_b);
  DV.length_eq (get_downview output_b);
  
  ()

let aes256_key_expansion_stdcall input_b output_b =
  let h0 = get() in

  let x, _ = aes256_key_expansion input_b output_b () in

  let h1 = get() in

  aes_simplify2 input_b h0;
  DV.length_eq (get_downview input_b);
  DV.length_eq (get_downview output_b);
  
  ()
