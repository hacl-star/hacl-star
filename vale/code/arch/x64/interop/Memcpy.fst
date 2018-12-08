module Memcpy

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
open X64.Memory
open X64.Memory_Sems
open X64.Vale.State
open X64.Vale.Decls
open BufferViewHelpers
open Interop_assumptions
open X64.Vale.StateLemmas
open X64.Vale.Lemmas
module TS = X64.Taint_Semantics_s
module ME = X64.Memory
module BS = X64.Bytes_Semantics_s

friend X64.Memory_Sems
friend X64.Memory
friend X64.Vale.Decls
friend X64.Vale.StateLemmas
#set-options "--z3rlimit 60"

open Vale_memcpy


#set-options "--initial_fuel 5 --max_fuel 5 --initial_ifuel 0 --max_ifuel 0"
let create_buffer_list (dst:b8) (src:b8) (stack_b:b8)  : (l:list b8{
    l == [stack_b;dst;src] /\
  (forall x. {:pattern List.memP x l} List.memP x l <==> (x == dst \/ x == src \/ x == stack_b))}) =
  [stack_b;dst;src]

#set-options "--max_fuel 0 --max_ifuel 0"

let create_initial_trusted_state is_win dst src stack_b (h0:HS.mem{pre_cond h0 dst src /\ B.length stack_b == 24 /\ live h0 stack_b /\ buf_disjoint_from stack_b [dst;src]}) : GTot TS.traceState =
  let taint_func (x:b8) : GTot taint =
    if StrongExcludedMiddle.strong_excluded_middle (x == dst) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == src) then Secret else
    Public in
  let buffers = create_buffer_list dst src stack_b in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_dst = addrs dst in
  let addr_src = addrs src in
  let addr_stack:nat64 = addrs stack_b + 0 in
  let regs = if is_win then (
    fun r -> begin match r with
    | Rsp -> addr_stack
    | Rcx -> addr_dst
    | Rdx -> addr_src
    | _ -> init_regs r end)
  else (
    fun r -> begin match r with
    | Rsp -> addr_stack
    | Rdi -> addr_dst
    | Rsi -> addr_src
    | _ -> init_regs r end)
  in let regs = FunctionalExtensionality.on reg regs
  in let xmms = FunctionalExtensionality.on xmm init_xmms in
  let (s0:BS.state) = {BS.ok = true; BS.regs = regs; BS.xmms = xmms; BS.flags = 0;
       BS.mem = Interop.down_mem h0 addrs buffers} in
  {TS.state = s0; TS.trace = []; TS.memTaint = create_valid_memtaint mem buffers taint_func}

val lemma_ghost_memcpy: is_win:bool -> dst:b8 -> src:b8 ->  stack_b:b8 -> (h0:HS.mem{pre_cond h0 dst src /\ B.length stack_b == 24 /\ live h0 stack_b /\ buf_disjoint_from stack_b [dst;src]}) ->
  Ghost (TS.traceState * nat * HS.mem)
    (requires True)
    (ensures (fun (s1, f1, h1) ->
      (let s0 = create_initial_trusted_state is_win dst src stack_b h0 in
      Some s1 == TS.taint_eval_code (va_code_memcpy is_win) f1 s0 /\
      Interop.correct_down h1 addrs [stack_b;dst;src] s1.TS.state.BS.mem /\
      post_cond h0 h1 dst src  /\
      calling_conventions is_win s0 s1 /\
      M.modifies (M.loc_union (M.loc_buffer stack_b) ( M.loc_buffer dst)) h0 h1)
    ))

// ===============================================================================================
//  Everything below this line is untrusted

let create_initial_vale_state is_win dst src stack_b (h0:HS.mem{pre_cond h0 dst src /\ B.length stack_b == 24 /\ live h0 stack_b /\ buf_disjoint_from stack_b [dst;src]}) : GTot va_state =
  let taint_func (x:b8) : GTot taint =
    if StrongExcludedMiddle.strong_excluded_middle (x == dst) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == src) then Secret else
    Public in
  let buffers = create_buffer_list dst src stack_b in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_dst = addrs dst in
  let addr_src = addrs src in
  let addr_stack:nat64 = addrs stack_b + 0 in
  let regs = if is_win then (
    fun r -> begin match r with
    | Rsp -> addr_stack
    | Rcx -> addr_dst
    | Rdx -> addr_src
    | _ -> init_regs r end)
  else (
    fun r -> begin match r with
    | Rsp -> addr_stack
    | Rdi -> addr_dst
    | Rsi -> addr_src
    | _ -> init_regs r end)
  in let regs = X64.Vale.Regs.of_fun regs
  in let xmms = X64.Vale.Xmms.of_fun init_xmms in
  {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem;
      memTaint = create_valid_memtaint mem buffers taint_func}

let create_lemma is_win dst src stack_b (h0:HS.mem{pre_cond h0 dst src /\ B.length stack_b == 24 /\ live h0 stack_b /\ buf_disjoint_from stack_b [dst;src]}) : Lemma
  (create_initial_trusted_state is_win dst src stack_b h0 == state_to_S (create_initial_vale_state is_win dst src stack_b h0)) =
    let s_init = create_initial_trusted_state is_win dst src stack_b h0 in
    let s0 = create_initial_vale_state is_win dst src stack_b h0 in
    let s1 = state_to_S s0 in
    assert (FunctionalExtensionality.feq (regs' s1.TS.state) (regs' s_init.TS.state));
    assert (FunctionalExtensionality.feq (xmms' s1.TS.state) (xmms' s_init.TS.state))

// TODO: Prove these two lemmas if they are not proven automatically
let implies_pre (is_win:bool) (h0:HS.mem) (dst:b8) (src:b8)  (stack_b:b8) : Lemma
  (requires pre_cond h0 dst src /\ B.length stack_b == 24 /\ live h0 stack_b /\ buf_disjoint_from stack_b [dst;src])
  (ensures (
B.length stack_b == 24 /\ live h0 stack_b /\ buf_disjoint_from stack_b [dst;src] /\ (
  let s0 = create_initial_vale_state is_win dst src stack_b h0 in
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt64) dst;
  length_t_eq (TBase TUInt64) src;
  va_pre (va_code_memcpy is_win) s0 is_win stack_b dst src ))) =
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt64) dst;
  length_t_eq (TBase TUInt64) src;
  assert(Interop.disjoint stack_b dst);
  assert(Interop.disjoint stack_b src);
  ()

let seq_nat64_to_seq_U64 (b:Seq.seq nat64) : (Seq.seq UInt64.t) =
Seq.init (Seq.length b) (fun (i:nat { i < Seq.length b }) -> UInt64.uint_to_t (Seq.index b i))

let implies_post (is_win:bool) (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) (dst:b8) (src:b8)  (stack_b:b8) : Lemma
  (requires pre_cond va_s0.mem.hs dst src /\ B.length stack_b == 24 /\ live va_s0.mem.hs stack_b /\ buf_disjoint_from stack_b [dst;src]/\
    va_post (va_code_memcpy is_win) va_s0 va_sM va_fM is_win stack_b dst src )
  (ensures post_cond va_s0.mem.hs va_sM.mem.hs dst src ) =
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt64) dst;
  length_t_eq (TBase TUInt64) src;
  let dst_b = BV.mk_buffer_view dst Views.view64 in
  let src_b = BV.mk_buffer_view src Views.view64 in
  let t = TBase TUInt64 in
  assert (Seq.equal (seq_nat64_to_seq_U64 (buffer_as_seq #t (va_get_mem va_sM) src)) (BV.as_seq va_sM.mem.hs src_b));  
  assert (Seq.equal (seq_nat64_to_seq_U64 (buffer_as_seq #t (va_get_mem va_sM) dst)) (BV.as_seq va_sM.mem.hs dst_b));  
  ()

#set-options "--max_fuel 0 --initial_ifuel 1 --max_ifuel 1"

let lemma_ghost_memcpy is_win dst src stack_b h0 =
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt64) dst;
  length_t_eq (TBase TUInt64) src;
  implies_pre is_win h0 dst src stack_b;
  let s0 = create_initial_trusted_state is_win dst src stack_b h0 in
  let s0' = create_initial_vale_state is_win dst src stack_b h0 in
  create_lemma is_win dst src stack_b h0;
  let s_v, f_v = va_lemma_memcpy (va_code_memcpy is_win) s0' is_win stack_b dst src in
  implies_post is_win s0' s_v f_v dst src stack_b;
  let s1 = Some?.v (TS.taint_eval_code (va_code_memcpy is_win) f_v s0) in
  assert (state_eq_S s1 (state_to_S s_v));
  assert (FunctionalExtensionality.feq s1.TS.state.BS.regs (X64.Vale.Regs.to_fun s_v.regs));
  assert (FunctionalExtensionality.feq s1.TS.state.BS.xmms (X64.Vale.Xmms.to_fun s_v.xmms));
  assert (M.modifies (M.loc_union (M.loc_buffer stack_b) ( M.loc_buffer dst)) h0 s_v.mem.hs);
  s1, f_v, s_v.mem.hs

#set-options "--max_fuel 0 --max_ifuel 0"

let memcpy dst src  =
  push_frame();
  let (stack_b:b8) = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 24) in
  if win then
  st_put
    (fun h -> pre_cond h dst src /\ B.length stack_b == 24 /\ live h stack_b /\ buf_disjoint_from stack_b [dst;src])
    (fun h -> let _, _, h1 =
      lemma_ghost_memcpy true dst src stack_b h
    in (), h1)
  else st_put
    (fun h -> pre_cond h dst src /\ B.length stack_b == 24 /\ live h stack_b /\ buf_disjoint_from stack_b [dst;src])
    (fun h -> let _, _, h1 =
      lemma_ghost_memcpy false dst src stack_b h
    in (), h1);
  pop_frame()

