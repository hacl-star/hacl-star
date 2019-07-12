module Quad32_xor_win

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

open Vale_quad32_xor_buffer_win

#set-options "--initial_fuel 6 --max_fuel 6 --initial_ifuel 2 --max_ifuel 2"
let implies_pre (h0:HS.mem) (src1:s8) (src2:s8) (dst:s8)  (stack_b:b8) : Lemma
  (requires pre_cond h0 src1 src2 dst /\ B.length stack_b == 32 /\ live h0 stack_b /\ buf_disjoint_from stack_b [src1;src2;dst])
  (ensures (
B.length stack_b == 32 /\ live h0 stack_b /\ buf_disjoint_from stack_b [src1;src2;dst] /\ (  let taint_func (x:b8) : GTot taint =
    if StrongExcludedMiddle.strong_excluded_middle (x == src1) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == src2) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == dst) then Secret else
    Public in
  let buffers = stack_b::src1::src2::dst::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_src1 = addrs src1 in
  let addr_src2 = addrs src2 in
  let addr_dst = addrs dst in
  let addr_stack:nat64 = addrs stack_b + 0 in
  let regs = fun r -> begin match r with
    | Rsp -> addr_stack
    | Rcx -> addr_src1
    | Rdx -> addr_src2
    | R8 -> addr_dst
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem; memTaint = create_valid_memtaint mem buffers taint_func} in
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) src1;
  length_t_eq (TBase TUInt128) src2;
  length_t_eq (TBase TUInt128) dst;
  va_pre (va_code_quad32_xor_buffer_win ()) s0 stack_b src1 src2 dst ))) =
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) src1;
  length_t_eq (TBase TUInt128) src2;
  length_t_eq (TBase TUInt128) dst;
  ()

let implies_post (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) (src1:s8) (src2:s8) (dst:s8)  (stack_b:b8) : Lemma
  (requires pre_cond va_s0.mem.hs src1 src2 dst /\ B.length stack_b == 32 /\ live va_s0.mem.hs stack_b /\ buf_disjoint_from stack_b [src1;src2;dst]/\
    va_post (va_code_quad32_xor_buffer_win ()) va_s0 va_sM va_fM stack_b src1 src2 dst )
  (ensures post_cond va_s0.mem.hs va_sM.mem.hs src1 src2 dst ) =
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) src1;
  length_t_eq (TBase TUInt128) src2;
  length_t_eq (TBase TUInt128) dst;
  let src1_128 = BV.mk_buffer_view src1 Views.view128 in
  assert (Seq.equal (buffer_as_seq (va_get_mem va_s0) src1) (BV.as_seq va_s0.mem.hs src1_128));
  BV.as_seq_sel va_s0.mem.hs src1_128 0;
  let src2_128 = BV.mk_buffer_view src2 Views.view128 in
  assert (Seq.equal (buffer_as_seq (va_get_mem va_s0) src2) (BV.as_seq va_s0.mem.hs src2_128));
  BV.as_seq_sel va_s0.mem.hs src2_128 0;
  let dst128 = BV.mk_buffer_view dst Views.view128 in
  assert (Seq.equal (buffer_as_seq (va_get_mem va_sM) dst) (BV.as_seq va_sM.mem.hs dst128));
  BV.as_seq_sel va_sM.mem.hs dst128 0;
  ()

val ghost_quad32_xor_buffer_win: src1:s8 -> src2:s8 -> dst:s8 ->  stack_b:b8 -> (h0:HS.mem{pre_cond h0 src1 src2 dst /\ B.length stack_b == 32 /\ live h0 stack_b /\ buf_disjoint_from stack_b [src1;src2;dst]}) -> GTot (h1:HS.mem{post_cond h0 h1 src1 src2 dst })

let ghost_quad32_xor_buffer_win src1 src2 dst stack_b h0 =
  let taint_func (x:b8) : GTot taint =
    if StrongExcludedMiddle.strong_excluded_middle (x == src1) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == src2) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == dst) then Secret else
    Public in
  let buffers = stack_b::src1::src2::dst::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_src1 = addrs src1 in
  let addr_src2 = addrs src2 in
  let addr_dst = addrs dst in
  let addr_stack:nat64 = addrs stack_b + 0 in
  let regs = fun r -> begin match r with
    | Rsp -> addr_stack
    | Rcx -> addr_src1
    | Rdx -> addr_src2
    | R8 -> addr_dst
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem; memTaint = create_valid_memtaint mem buffers taint_func} in
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) src1;
  length_t_eq (TBase TUInt128) src2;
  length_t_eq (TBase TUInt128) dst;
  implies_pre h0 src1 src2 dst stack_b ;
  let s1, f1 = va_lemma_quad32_xor_buffer_win (va_code_quad32_xor_buffer_win ()) s0 stack_b src1 src2 dst  in
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
  // Ensures that va_code_quad32_xor_buffer_win is actually Vale code, and that s1 is the result of executing this code
  assert (va_ensure_total (va_code_quad32_xor_buffer_win ()) s0 s1 f1);
  implies_post s0 s1 f1 src1 src2 dst stack_b ;
  s1.mem.hs

let quad32_xor_buffer_win src1 src2 dst  =
  push_frame();
  let (stack_b:b8) = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 32) in
  st_put (fun h -> pre_cond h src1 src2 dst /\ B.length stack_b == 32 /\ live h stack_b /\ buf_disjoint_from stack_b [src1;src2;dst]) (ghost_quad32_xor_buffer_win src1 src2 dst stack_b);
  pop_frame()
