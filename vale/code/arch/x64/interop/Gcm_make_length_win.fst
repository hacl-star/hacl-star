module Gcm_make_length_win

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

open Vale_gcm_make_length_quad_buffer_win

#set-options "--initial_fuel 4 --max_fuel 4 --initial_ifuel 2 --max_ifuel 2"
let implies_pre (h0:HS.mem) (plain_num_bytes:nat64) (auth_num_bytes:nat64) (b:s8)  (stack_b:b8) : Lemma
  (requires pre_cond h0 plain_num_bytes auth_num_bytes b /\ B.length stack_b == 32 /\ live h0 stack_b /\ buf_disjoint_from stack_b [b])
  (ensures (
B.length stack_b == 32 /\ live h0 stack_b /\ buf_disjoint_from stack_b [b] /\ (  let taint_func (x:b8) : GTot taint =
    if StrongExcludedMiddle.strong_excluded_middle (x == b) then Secret else
    Public in
  let buffers = stack_b::b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_b = addrs b in
  let addr_stack:nat64 = addrs stack_b + 0 in
  let regs = fun r -> begin match r with
    | Rsp -> addr_stack
    | Rcx -> plain_num_bytes
    | Rdx -> auth_num_bytes
    | R8 -> addr_b
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem; memTaint = create_valid_memtaint mem buffers taint_func} in
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) b;
  va_pre (va_code_gcm_make_length_quad_buffer_win ()) s0 stack_b plain_num_bytes auth_num_bytes b ))) =
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) b;
  ()

let implies_post (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) (plain_num_bytes:nat64) (auth_num_bytes:nat64) (b:s8)  (stack_b:b8) : Lemma
  (requires pre_cond va_s0.mem.hs plain_num_bytes auth_num_bytes b /\ B.length stack_b == 32 /\ live va_s0.mem.hs stack_b /\ buf_disjoint_from stack_b [b]/\
    va_post (va_code_gcm_make_length_quad_buffer_win ()) va_s0 va_sM va_fM stack_b plain_num_bytes auth_num_bytes b )
  (ensures post_cond va_s0.mem.hs va_sM.mem.hs plain_num_bytes auth_num_bytes b ) =
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) b;
  let b128 = BV.mk_buffer_view b Views.view128 in
  assert (Seq.equal (buffer_as_seq (va_get_mem va_sM) b) (BV.as_seq va_sM.mem.hs b128));
  BV.as_seq_sel va_sM.mem.hs b128 0;
  ()

val ghost_gcm_make_length_quad_buffer_win: plain_num_bytes:nat64 -> auth_num_bytes:nat64 -> b:s8 ->  stack_b:b8 -> (h0:HS.mem{pre_cond h0 plain_num_bytes auth_num_bytes b /\ B.length stack_b == 32 /\ live h0 stack_b /\ buf_disjoint_from stack_b [b]}) -> GTot (h1:HS.mem{post_cond h0 h1 plain_num_bytes auth_num_bytes b })

let ghost_gcm_make_length_quad_buffer_win plain_num_bytes auth_num_bytes b stack_b h0 =
  let taint_func (x:b8) : GTot taint =
    if StrongExcludedMiddle.strong_excluded_middle (x == b) then Secret else
    Public in
  let buffers = stack_b::b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_b = addrs b in
  let addr_stack:nat64 = addrs stack_b + 0 in
  let regs = fun r -> begin match r with
    | Rsp -> addr_stack
    | Rcx -> plain_num_bytes
    | Rdx -> auth_num_bytes
    | R8 -> addr_b
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem; memTaint = create_valid_memtaint mem buffers taint_func} in
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) b;
  implies_pre h0 plain_num_bytes auth_num_bytes b stack_b ;
  let s1, f1 = va_lemma_gcm_make_length_quad_buffer_win (va_code_gcm_make_length_quad_buffer_win ()) s0 stack_b plain_num_bytes auth_num_bytes b  in
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
  // Ensures that va_code_gcm_make_length_quad_buffer_win is actually Vale code, and that s1 is the result of executing this code
  assert (va_ensure_total (va_code_gcm_make_length_quad_buffer_win ()) s0 s1 f1);
  implies_post s0 s1 f1 plain_num_bytes auth_num_bytes b stack_b ;
  s1.mem.hs

let gcm_make_length_quad_buffer_win plain_num_bytes auth_num_bytes b  =
  push_frame();
  let (stack_b:b8) = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 32) in
  st_put (fun h -> pre_cond h (UInt64.v plain_num_bytes) (UInt64.v auth_num_bytes) b /\ B.length stack_b == 32 /\ live h stack_b /\ buf_disjoint_from stack_b [b]) (ghost_gcm_make_length_quad_buffer_win (UInt64.v plain_num_bytes) (UInt64.v auth_num_bytes) b stack_b);
  pop_frame()
