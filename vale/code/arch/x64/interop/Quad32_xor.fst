module Quad32_xor

open LowStar.Buffer
module B = LowStar.Buffer
module BV = LowStar.BufferView
open LowStar.Modifies
module M = LowStar.Modifies
open LowStar.ModifiesPat
open FStar.HyperStack.ST
module HS = FStar.HyperStack
open Interop
open Words_s
open Types_s
open X64.Machine_s
open X64.Memory_s
open X64.Vale.State
open X64.Vale.Decls
open BufferViewHelpers
open Interop_assumptions
open X64.Vale.StateLemmas
open X64.Vale.Lemmas
module TS = X64.Taint_Semantics_s
module ME = X64.Memory_s
module BS = X64.Bytes_Semantics_s
#set-options "--z3rlimit 60"

friend SecretByte
friend X64.Memory_s
friend X64.Memory
friend X64.Vale.Decls

open Vale_quad32_xor_buffer

#set-options "--initial_fuel 6 --max_fuel 6 --initial_ifuel 2 --max_ifuel 2"
let create_initial_trusted_state is_win src1 src2 dst stack_b (h0:HS.mem{pre_cond h0 src1 src2 dst /\ B.length stack_b == 32 /\ live h0 stack_b /\ buf_disjoint_from stack_b [src1;src2;dst]}) : GTot TS.traceState =
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
  let regs = if is_win then (
    fun r -> begin match r with
    | Rsp -> addr_stack
    | Rcx -> addr_src1
    | Rdx -> addr_src2
    | R8 -> addr_dst
    | _ -> init_regs r end)
  else (
    fun r -> begin match r with
    | Rsp -> addr_stack
    | Rdi -> addr_src1
    | Rsi -> addr_src2
    | Rdx -> addr_dst
    | _ -> init_regs r end)
  in let xmms = init_xmms in
  let (s_b:BS.state) = {BS.ok = true; BS.regs = regs; BS.xmms = xmms; BS.flags = 0;
       BS.mem = Interop.down_mem h0 addrs buffers} in
  let s0:X64.Memory_s.state = {ME.state = s_b; ME.mem = mem} in
  {TS.state = s0; TS.trace = []; TS.memTaint = create_valid_memtaint mem buffers taint_func}

let create_initial_vale_state is_win src1 src2 dst stack_b (h0:HS.mem{pre_cond h0 src1 src2 dst /\ B.length stack_b == 32 /\ live h0 stack_b /\ buf_disjoint_from stack_b [src1;src2;dst]}) : GTot va_state =
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
  let regs = if is_win then (
    fun r -> begin match r with
    | Rsp -> addr_stack
    | Rcx -> addr_src1
    | Rdx -> addr_src2
    | R8 -> addr_dst
    | _ -> init_regs r end)
  else (
    fun r -> begin match r with
    | Rsp -> addr_stack
    | Rdi -> addr_src1
    | Rsi -> addr_src2
    | Rdx -> addr_dst
    | _ -> init_regs r end)
  in let xmms = init_xmms in
  {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem;
      memTaint = create_valid_memtaint mem buffers taint_func}

let create_lemma is_win src1 src2 dst stack_b (h0:HS.mem{pre_cond h0 src1 src2 dst /\ B.length stack_b == 32 /\ live h0 stack_b /\ buf_disjoint_from stack_b [src1;src2;dst]}) : Lemma
  (state_of_S (create_initial_trusted_state is_win src1 src2 dst stack_b h0) == create_initial_vale_state is_win src1 src2 dst stack_b h0) =
    let s_init = create_initial_trusted_state is_win src1 src2 dst stack_b h0 in
    let s0 = state_of_S s_init in
    let s1 = create_initial_vale_state is_win src1 src2 dst stack_b h0 in
    assert (FunctionalExtensionality.feq s1.regs (regs' s_init.TS.state));
    assert (FunctionalExtensionality.feq s1.xmms (xmms' s_init.TS.state));
    lemma_of_ok s_init;
    lemma_of_regs s_init;
    lemma_of_flags s_init;
    lemma_of_xmms s_init;
    lemma_of_mem s_init;
    lemma_of_memTaint s_init;
    ()

// TODO: Prove these two lemmas if they are not proven automatically
let implies_pre (is_win:bool) (h0:HS.mem) (src1:s8) (src2:s8) (dst:s8)  (stack_b:b8) : Lemma
  (requires pre_cond h0 src1 src2 dst /\ B.length stack_b == 32 /\ live h0 stack_b /\ buf_disjoint_from stack_b [src1;src2;dst])
  (ensures (
B.length stack_b == 32 /\ live h0 stack_b /\ buf_disjoint_from stack_b [src1;src2;dst] /\ (
  let s0 = create_initial_vale_state is_win src1 src2 dst stack_b h0 in
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) src1;
  length_t_eq (TBase TUInt128) src2;
  length_t_eq (TBase TUInt128) dst;
  va_pre (va_code_quad32_xor_buffer is_win) s0 is_win stack_b src1 src2 dst ))) =
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) src1;
  length_t_eq (TBase TUInt128) src2;
  length_t_eq (TBase TUInt128) dst;
  assert(Interop.disjoint stack_b src1);
  assert(Interop.disjoint stack_b src2);
  assert(Interop.disjoint stack_b dst);
  ()

let implies_post (is_win:bool) (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) (src1:s8) (src2:s8) (dst:s8)  (stack_b:b8) : Lemma
  (requires pre_cond va_s0.mem.hs src1 src2 dst /\ B.length stack_b == 32 /\ live va_s0.mem.hs stack_b /\ buf_disjoint_from stack_b [src1;src2;dst]/\
    va_post (va_code_quad32_xor_buffer is_win) va_s0 va_sM va_fM is_win stack_b src1 src2 dst )
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

val lemma_ghost_quad32_xor_buffer: is_win:bool -> src1:s8 -> src2:s8 -> dst:s8 ->  stack_b:b8 -> (h0:HS.mem{pre_cond h0 src1 src2 dst /\ B.length stack_b == 32 /\ live h0 stack_b /\ buf_disjoint_from stack_b [src1;src2;dst]}) ->
  Ghost (TS.traceState * nat * HS.mem)
    (requires True)
    (ensures (fun (s1, f1, h1) ->
      (let s0 = create_initial_trusted_state is_win src1 src2 dst stack_b h0 in
      Some s1 == TS.taint_eval_code (va_code_quad32_xor_buffer is_win) f1 s0 /\
      Interop.correct_down h1 addrs [stack_b;src1;src2;dst] s1.TS.state.ME.state.BS.mem /\
      post_cond h0 h1 src1 src2 dst  /\
      calling_conventions is_win s0 s1)
    ))

let lemma_ghost_quad32_xor_buffer is_win src1 src2 dst stack_b h0 =
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) src1;
  length_t_eq (TBase TUInt128) src2;
  length_t_eq (TBase TUInt128) dst;
  implies_pre is_win h0 src1 src2 dst stack_b;
  let s0 = create_initial_trusted_state is_win src1 src2 dst stack_b h0 in
  create_lemma is_win src1 src2 dst stack_b h0;
  let s_v, f_v = va_lemma_quad32_xor_buffer (va_code_quad32_xor_buffer is_win) (state_of_S s0) is_win stack_b src1 src2 dst  in
  implies_post is_win (state_of_S s0) s_v f_v src1 src2 dst stack_b;
  Some?.v (TS.taint_eval_code (va_code_quad32_xor_buffer is_win) f_v s0), f_v, s_v.mem.hs

#set-options "--max_fuel 0 --max_ifuel 0"

let quad32_xor_buffer src1 src2 dst  =
  push_frame();
  let (stack_b:b8) = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 32) in
  st_put
    (fun h -> pre_cond h src1 src2 dst /\ B.length stack_b == 32 /\ live h stack_b /\ buf_disjoint_from stack_b [src1;src2;dst])
  (fun h -> let _, _, h1 =
    if win then lemma_ghost_quad32_xor_buffer true src1 src2 dst stack_b h
    else lemma_ghost_quad32_xor_buffer false src1 src2 dst stack_b h
  in h1);
  pop_frame()
