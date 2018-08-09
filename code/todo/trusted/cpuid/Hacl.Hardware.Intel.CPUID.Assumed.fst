module Hacl.Hardware.Intel.CPUID.Assumed

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.HyperStack.ST
open FStar.Buffer
open FStar.HyperStack

(* Aliases for modules *)
module U8  = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module FB  = FStar.Buffer
module HS  = FStar.HyperStack


(* Aliases for types *)
let u8  = FStar.UInt8.t 
let u32 = FStar.UInt32.t
let u64 = FStar.UInt64.t
let bytes = FStar.Buffer.buffer u8


(* Definition of the cpuid_t type *)
type cpuid_t = {
  eax:u32;
  ebx:u32;
  ecx:u32;
  edx:u32;
}


(* Definition of the cpuid function *)
assume val cpuid : info:(buffer cpuid_t) -> leaf:u32 -> subleaf:u32
  -> Stack unit (requires (fun h -> live h info))
               (ensures  (fun h0 _ h1 -> live h1 info /\ modifies_1 info h0 h1))


(* Definition of the _has_cpuid function *)
assume val _has_cpuid : unit
  -> Stack u32  (requires (fun _ -> True))
               (ensures  (fun h0 _ h1 -> h0 == h1))


(* Definition of the _is_intel_cpu function *)
assume val _is_intel_cpu : unit
  -> Stack u32  (requires (fun _ -> True))
               (ensures  (fun h0 _ h1 -> h0 == h1))
