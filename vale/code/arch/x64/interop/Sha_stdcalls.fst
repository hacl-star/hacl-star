module Sha_stdcalls

module DV = LowStar.BufferView.Down
open Interop.Base
open Vale.AsLowStar.MemoryHelpers
open Words.Seq_s
open Simplify_Sha

#set-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

let math_aux (n:nat) : Lemma ( ((64 * n) * 1) / 16 == 4 * n) = ()

let sha256_update ctx_b in_b num_val k_b =
  let h0 = get() in
  DV.length_eq (get_downview in_b);
  Classical.forall_intro (bounded_buffer_addrs TUInt8 TUInt128 h0 in_b);
  DV.length_eq (get_downview ctx_b);
  DV.length_eq (get_downview k_b);
  lemma_k_reqs_equiv k_b h0; 
  math_aux (UInt64.v num_val);
  as_vale_buffer_len #TUInt8 #TUInt128 in_b;
  let x, _ = Vale.Stdcalls.Sha.sha256_update ctx_b in_b num_val k_b () in
  let h1 = get() in
  reveal_word();
  simplify_le_bytes_to_hash_uint32 ctx_b h0;
  simplify_le_bytes_to_hash_uint32 ctx_b h1;
  lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 in_b h0;
  ()
