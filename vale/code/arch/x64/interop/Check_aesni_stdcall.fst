module Check_aesni_stdcall

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

open Vale_check_aesni_stdcall

#set-options "--initial_fuel 3 --max_fuel 3 --initial_ifuel 2 --max_ifuel 2"
let create_initial_trusted_state is_win stack_b (h0:HS.mem{pre_cond h0 /\ B.length stack_b == 8 /\ live h0 stack_b /\ buf_disjoint_from stack_b []}) : GTot TS.traceState =
  let taint_func (x:b8) : GTot taint =
    Public in
  let buffers = stack_b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_stack:nat64 = addrs stack_b + 0 in
  let regs = if is_win then (
    fun r -> begin match r with
    | Rsp -> addr_stack
    | _ -> init_regs r end)
  else (
    fun r -> begin match r with
    | Rsp -> addr_stack
    | _ -> init_regs r end)
  in let regs = FunctionalExtensionality.on reg regs
  in let xmms = FunctionalExtensionality.on xmm init_xmms in
  let (s0:BS.state) = {BS.ok = true; BS.regs = regs; BS.xmms = xmms; BS.flags = 0;
       BS.mem = Interop.down_mem h0 addrs buffers} in
  {TS.state = s0; TS.trace = []; TS.memTaint = create_valid_memtaint mem buffers taint_func}

val lemma_ghost_check_aesni_stdcall: is_win:bool ->  stack_b:b8 -> (h0:HS.mem{pre_cond h0 /\ B.length stack_b == 8 /\ live h0 stack_b /\ buf_disjoint_from stack_b []}) ->
  Ghost (TS.traceState * nat * HS.mem * nat64)
    (requires True)
    (ensures (fun (s1, f1, h1, ret_val) ->
      (let s0 = create_initial_trusted_state is_win stack_b h0 in
      Some s1 == TS.taint_eval_code (va_code_check_aesni_stdcall is_win) f1 s0 /\
      Interop.correct_down h1 addrs [stack_b] s1.TS.state.BS.mem /\
      post_cond h0 h1 (UInt64.uint_to_t ret_val) /\
      ret_val == s1.TS.state.BS.regs Rax /\
      calling_conventions is_win s0 s1 /\
      M.modifies (M.loc_buffer stack_b) h0 h1)
    ))

// ===============================================================================================
//  Everything below this line is untrusted

let create_initial_vale_state is_win stack_b (h0:HS.mem{pre_cond h0 /\ B.length stack_b == 8 /\ live h0 stack_b /\ buf_disjoint_from stack_b []}) : GTot va_state =
  let taint_func (x:b8) : GTot taint =
    Public in
  let buffers = stack_b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_stack:nat64 = addrs stack_b + 0 in
  let regs = if is_win then (
    fun r -> begin match r with
    | Rsp -> addr_stack
    | _ -> init_regs r end)
  else (
    fun r -> begin match r with
    | Rsp -> addr_stack
    | _ -> init_regs r end)
  in let regs = X64.Vale.Regs.of_fun regs
  in let xmms = X64.Vale.Xmms.of_fun init_xmms in
  {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem;
      memTaint = create_valid_memtaint mem buffers taint_func}

let create_lemma is_win stack_b (h0:HS.mem{pre_cond h0 /\ B.length stack_b == 8 /\ live h0 stack_b /\ buf_disjoint_from stack_b []}) : Lemma
  (create_initial_trusted_state is_win stack_b h0 == state_to_S (create_initial_vale_state is_win stack_b h0)) =
    let s_init = create_initial_trusted_state is_win stack_b h0 in
    let s0 = create_initial_vale_state is_win stack_b h0 in
    let s1 = state_to_S s0 in
    assert (FunctionalExtensionality.feq (regs' s1.TS.state) (regs' s_init.TS.state));
    assert (FunctionalExtensionality.feq (xmms' s1.TS.state) (xmms' s_init.TS.state))

#set-options "--initial_fuel 1 --max_fuel 1 --max_ifuel 0"

let implies_pre (is_win:bool) (h0:HS.mem)  (stack_b:b8) : Lemma
  (requires pre_cond h0 /\ B.length stack_b == 8 /\ live h0 stack_b /\ buf_disjoint_from stack_b [])
  (ensures (
B.length stack_b == 8 /\ live h0 stack_b /\ buf_disjoint_from stack_b [] /\ (
  let s0 = create_initial_vale_state is_win stack_b h0 in
  length_t_eq (TBase TUInt64) stack_b;
  va_pre (va_code_check_aesni_stdcall is_win) s0 is_win stack_b ))) =
  length_t_eq (TBase TUInt64) stack_b;
  ()

let implies_post (is_win:bool) (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel)  (stack_b:b8) : Lemma
  (requires pre_cond va_s0.mem.hs /\ B.length stack_b == 8 /\ live va_s0.mem.hs stack_b /\ buf_disjoint_from stack_b []/\
    va_post (va_code_check_aesni_stdcall is_win) va_s0 va_sM va_fM is_win stack_b )
  (ensures post_cond va_s0.mem.hs va_sM.mem.hs (UInt64.uint_to_t (eval_reg Rax va_sM))) =
  length_t_eq (TBase TUInt64) stack_b;
  ()

#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"

let lemma_ghost_check_aesni_stdcall is_win stack_b h0 =
  length_t_eq (TBase TUInt64) stack_b;
  implies_pre is_win h0 stack_b;
  let s0 = create_initial_trusted_state is_win stack_b h0 in
  let s0' = create_initial_vale_state is_win stack_b h0 in
  create_lemma is_win stack_b h0;
  let s_v, f_v = va_lemma_check_aesni_stdcall (va_code_check_aesni_stdcall is_win) s0' is_win stack_b in
  implies_post is_win s0' s_v f_v stack_b;
  let s1 = Some?.v (TS.taint_eval_code (va_code_check_aesni_stdcall is_win) f_v s0) in
  assert (state_eq_S s1 (state_to_S s_v));
  assert (FunctionalExtensionality.feq s1.TS.state.BS.regs (X64.Vale.Regs.to_fun s_v.regs));
  assert (FunctionalExtensionality.feq s1.TS.state.BS.xmms (X64.Vale.Xmms.to_fun s_v.xmms));
  (s1, f_v, s_v.mem.hs, eval_reg Rax s_v)

#set-options "--max_fuel 0 --max_ifuel 0"

let check_aesni_stdcall () =
  push_frame();
  let (stack_b:b8) = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 8) in
  let x = (if win then
  st_put
    (fun h -> pre_cond h /\ B.length stack_b == 8 /\ live h stack_b /\ buf_disjoint_from stack_b [])
    (fun h -> let _, _, h1, x =
        lemma_ghost_check_aesni_stdcall true stack_b h
    in x, h1)
  else st_put
    (fun h -> pre_cond h /\ B.length stack_b == 8 /\ live h stack_b /\ buf_disjoint_from stack_b [])
    (fun h -> let _, _, h1, x =
        lemma_ghost_check_aesni_stdcall false stack_b h
    in x, h1))
  in pop_frame();
  UInt64.uint_to_t x
