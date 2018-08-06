module GHash_stdcall_win

open LowStar.Buffer
module B = LowStar.Buffer
module BV = LowStar.BufferView
open LowStar.Modifies
module M = LowStar.Modifies
open LowStar.ModifiesPat
open FStar.HyperStack.ST
module HS = FStar.HyperStack
module S8 = SecretByte
open Interop
open Words_s
open Types_s
open X64.Machine_s
open X64.Memory_s
open X64.Vale.State
open X64.Vale.Decls
open BufferViewHelpers
open Interop_assumptions
#set-options "--z3rlimit 40"

open Vale_ghash_incremental_bytes_stdcall_win

#set-options "--initial_fuel 6 --max_fuel 6 --initial_ifuel 2 --max_ifuel 2"
let implies_pre (h0:HS.mem) (h_b:s8) (hash_b:s8) (input_b:s8) (num_bytes:nat64)  (stack_b:b8) : Lemma
  (requires pre_cond h0 h_b hash_b input_b num_bytes /\ B.length stack_b == 80 /\ live h0 stack_b /\ buf_disjoint_from stack_b [h_b;hash_b;input_b])
  (ensures (
B.length stack_b == 80 /\ live h0 stack_b /\ buf_disjoint_from stack_b [h_b;hash_b;input_b] /\ (  let taint_func (x:b8) : GTot taint =
    if StrongExcludedMiddle.strong_excluded_middle (x == h_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == hash_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == input_b) then Secret else
    Public in
  let buffers = stack_b::h_b::hash_b::input_b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_h_b = addrs h_b in
  let addr_hash_b = addrs hash_b in
  let addr_input_b = addrs input_b in
  let addr_stack:nat64 = addrs stack_b + 40 in
  let regs = fun r -> begin match r with
    | Rsp -> addr_stack
    | Rcx -> addr_h_b
    | Rdx -> addr_hash_b
    | R8 -> addr_input_b
    | R9 -> num_bytes
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem; memTaint = create_valid_memtaint mem buffers taint_func} in
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) h_b;
  length_t_eq (TBase TUInt128) hash_b;
  length_t_eq (TBase TUInt128) input_b;
  va_pre (va_code_ghash_incremental_bytes_stdcall_win ()) s0 stack_b h_b hash_b input_b num_bytes ))) =
  assert (B.disjoint stack_b h_b);
  assert (B.disjoint stack_b hash_b);
  assert (B.disjoint stack_b input_b);
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) h_b;
  length_t_eq (TBase TUInt128) hash_b;
  length_t_eq (TBase TUInt128) input_b;
  ()

let implies_post (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) (h_b:s8) (hash_b:s8) (input_b:s8) (num_bytes:nat64)  (stack_b:b8) : Lemma
  (requires pre_cond va_s0.mem.hs h_b hash_b input_b num_bytes /\ B.length stack_b == 80 /\ live va_s0.mem.hs stack_b /\ buf_disjoint_from stack_b [h_b;hash_b;input_b]/\
    va_post (va_code_ghash_incremental_bytes_stdcall_win ()) va_s0 va_sM va_fM stack_b h_b hash_b input_b num_bytes )
  (ensures post_cond va_s0.mem.hs va_sM.mem.hs h_b hash_b input_b num_bytes ) =
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) h_b;
  length_t_eq (TBase TUInt128) hash_b;
  length_t_eq (TBase TUInt128) input_b;
  assert (Seq.equal
    (buffer128_as_seq (va_get_mem va_sM) input_b)
    (buffer_to_seq_quad input_b va_s0.mem.hs));
  ()

val ghost_ghash_incremental_bytes_stdcall_win: h_b:s8 -> hash_b:s8 -> input_b:s8 -> num_bytes:nat64 ->  stack_b:b8 -> (h0:HS.mem{pre_cond h0 h_b hash_b input_b num_bytes /\ B.length stack_b == 80 /\ live h0 stack_b /\ buf_disjoint_from stack_b [h_b;hash_b;input_b]}) -> GTot (h1:HS.mem{post_cond h0 h1 h_b hash_b input_b num_bytes  /\ M.modifies (M.loc_union (M.loc_buffer hash_b) (M.loc_buffer stack_b)) h0 h1})

let ghost_ghash_incremental_bytes_stdcall_win h_b hash_b input_b num_bytes stack_b h0 =
  let taint_func (x:b8) : GTot taint =
    if StrongExcludedMiddle.strong_excluded_middle (x == h_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == hash_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == input_b) then Secret else
    Public in
  let buffers = stack_b::h_b::hash_b::input_b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_h_b = addrs h_b in
  let addr_hash_b = addrs hash_b in
  let addr_input_b = addrs input_b in
  let addr_stack:nat64 = addrs stack_b + 40 in
  let regs = fun r -> begin match r with
    | Rsp -> addr_stack
    | Rcx -> addr_h_b
    | Rdx -> addr_hash_b
    | R8 -> addr_input_b
    | R9 -> num_bytes
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem; memTaint = create_valid_memtaint mem buffers taint_func} in
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) h_b;
  length_t_eq (TBase TUInt128) hash_b;
  length_t_eq (TBase TUInt128) input_b;
  implies_pre h0 h_b hash_b input_b num_bytes stack_b ;
  let s1, f1 = va_lemma_ghash_incremental_bytes_stdcall_win (va_code_ghash_incremental_bytes_stdcall_win ()) s0 stack_b h_b hash_b input_b num_bytes  in
  // Ensures that the Vale execution was correct
  assert(s1.ok);
  // Ensures that the callee_saved registers are correct
  assert(s0.regs Rbx == s1.regs Rbx);
  assert(s0.regs Rbp == s1.regs Rbp);
  assert(s0.regs Rdi == s1.regs Rdi);
  assert(s0.regs Rsi == s1.regs Rsi);
  assert(s0.regs Rsp == s1.regs Rsp);
  assert(s0.regs R12 == s1.regs R12);
  assert(s0.regs R13 == s1.regs R13);
  assert(s0.regs R14 == s1.regs R14);
  assert(s0.regs R15 == s1.regs R15);
  assert(s0.xmms 6 == s1.xmms 6);
  assert(s0.xmms 7 == s1.xmms 7);
  assert(s0.xmms 8 == s1.xmms 8);
  assert(s0.xmms 9 == s1.xmms 9);
  assert(s0.xmms 10 == s1.xmms 10);
  assert(s0.xmms 11 == s1.xmms 11);
  assert(s0.xmms 12 == s1.xmms 12);
  assert(s0.xmms 13 == s1.xmms 13);
  assert(s0.xmms 14 == s1.xmms 14);
  assert(s0.xmms 15 == s1.xmms 15);
  // Ensures that va_code_ghash_incremental_bytes_stdcall_win is actually Vale code, and that s1 is the result of executing this code
  assert (va_ensure_total (va_code_ghash_incremental_bytes_stdcall_win ()) s0 s1 f1);
  implies_post s0 s1 f1 h_b hash_b input_b num_bytes stack_b ;
  s1.mem.hs

let ghash_incremental_bytes_stdcall_win h_b hash_b input_b num_bytes  =
  push_frame();
  let (stack_b:b8) = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 80) in
  st_put (fun h -> pre_cond h h_b hash_b input_b (UInt64.v num_bytes) /\ B.length stack_b == 80 /\ live h stack_b /\ buf_disjoint_from stack_b [h_b;hash_b;input_b]) (ghost_ghash_incremental_bytes_stdcall_win h_b hash_b input_b (UInt64.v num_bytes) stack_b);
  pop_frame()
