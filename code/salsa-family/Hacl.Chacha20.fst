module Hacl.Chacha20

(** This module implements Chacha20 
    @summary Chacha20 reference code
    **)
  
module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Buffer
open Hacl.Spec.Endianness
open Hacl.Impl.Chacha20

module U32 = FStar.UInt32

#reset-options "--max_fuel 0 --z3rlimit 100"

let chacha20_key_block block k n ctr =
  push_frame();
  let st = alloc () in
  let l  = init st k n in
  let l  = chacha20_block l block st ctr in
  pop_frame()

let chacha20 output plain len k n ctr = chacha20 output plain len k n ctr
