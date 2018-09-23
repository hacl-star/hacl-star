module Sha_update_bytes_stdcall

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

friend SecretByte
friend X64.Memory_s
friend X64.Memory
friend X64.Vale.Decls
friend X64.Vale.StateLemmas
#set-options "--z3rlimit 60"

open Vale_sha_update_bytes_stdcall

#set-options "--initial_fuel 6 --max_fuel 6 --initial_ifuel 2 --max_ifuel 2"
let create_initial_trusted_state is_win ctx_b in_b num_val k_b stack_b (h0:HS.mem{pre_cond h0 ctx_b in_b num_val k_b /\ B.length stack_b == (if is_win then 264 else 104) /\ live h0 stack_b /\ buf_disjoint_from stack_b [ctx_b;in_b;k_b]}) : GTot TS.traceState =
  let taint_func (x:b8) : GTot taint =
    if StrongExcludedMiddle.strong_excluded_middle (x == ctx_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == in_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == k_b) then Secret else
    Public in
  let buffers = stack_b::ctx_b::in_b::k_b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_ctx_b = addrs ctx_b in
  let addr_in_b = addrs in_b in
  let addr_k_b = addrs k_b in
  let addr_stack:nat64 = addrs stack_b + (if is_win then 224 else 64) in
  let regs = if is_win then (
    fun r -> begin match r with
    | Rsp -> addr_stack
    | Rcx -> addr_ctx_b
    | Rdx -> addr_in_b
    | R8 -> num_val
    | R9 -> addr_k_b
    | _ -> init_regs r end)
  else (
    fun r -> begin match r with
    | Rsp -> addr_stack
    | Rdi -> addr_ctx_b
    | Rsi -> addr_in_b
    | Rdx -> num_val
    | Rcx -> addr_k_b
    | _ -> init_regs r end)
  in let xmms = init_xmms in
  let (s0:BS.state) = {BS.ok = true; BS.regs = regs; BS.xmms = xmms; BS.flags = 0;
       BS.mem = Interop.down_mem h0 addrs buffers} in
  {TS.state = s0; TS.trace = []; TS.memTaint = create_valid_memtaint mem buffers taint_func}

val lemma_ghost_sha_update_bytes_stdcall: is_win:bool -> ctx_b:s8 -> in_b:s8 -> num_val:nat64 -> k_b:s8 ->  stack_b:b8 -> (h0:HS.mem{pre_cond h0 ctx_b in_b num_val k_b /\ B.length stack_b == (if is_win then 264 else 104) /\ live h0 stack_b /\ buf_disjoint_from stack_b [ctx_b;in_b;k_b]}) ->
  Ghost (TS.traceState * nat * HS.mem)
    (requires True)
    (ensures (fun (s1, f1, h1) ->
      (let s0 = create_initial_trusted_state is_win ctx_b in_b num_val k_b stack_b h0 in
      Some s1 == TS.taint_eval_code (va_code_sha_update_bytes_stdcall is_win) f1 s0 /\
      Interop.correct_down h1 addrs [stack_b;ctx_b;in_b;k_b] s1.TS.state.BS.mem /\
      post_cond h0 h1 ctx_b in_b num_val k_b  /\
      calling_conventions is_win s0 s1 /\
      M.modifies (M.loc_union (M.loc_buffer ctx_b) (M.loc_buffer stack_b)) h0 h1)
    ))

// ===============================================================================================
//  Everything below this line is untrusted

let create_initial_vale_state is_win ctx_b in_b num_val k_b stack_b (h0:HS.mem{pre_cond h0 ctx_b in_b num_val k_b /\ B.length stack_b == (if is_win then 264 else 104) /\ live h0 stack_b /\ buf_disjoint_from stack_b [ctx_b;in_b;k_b]}) : GTot va_state =
  let taint_func (x:b8) : GTot taint =
    if StrongExcludedMiddle.strong_excluded_middle (x == ctx_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == in_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == k_b) then Secret else
    Public in
  let buffers = stack_b::ctx_b::in_b::k_b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_ctx_b = addrs ctx_b in
  let addr_in_b = addrs in_b in
  let addr_k_b = addrs k_b in
  let addr_stack:nat64 = addrs stack_b + (if is_win then 224 else 64) in
  let regs = if is_win then (
    fun r -> begin match r with
    | Rsp -> addr_stack
    | Rcx -> addr_ctx_b
    | Rdx -> addr_in_b
    | R8 -> num_val
    | R9 -> addr_k_b
    | _ -> init_regs r end)
  else (
    fun r -> begin match r with
    | Rsp -> addr_stack
    | Rdi -> addr_ctx_b
    | Rsi -> addr_in_b
    | Rdx -> num_val
    | Rcx -> addr_k_b
    | _ -> init_regs r end)
  in let xmms = init_xmms in
  {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem;
      memTaint = create_valid_memtaint mem buffers taint_func}

let create_lemma is_win ctx_b in_b num_val k_b stack_b (h0:HS.mem{pre_cond h0 ctx_b in_b num_val k_b /\ B.length stack_b == (if is_win then 264 else 104) /\ live h0 stack_b /\ buf_disjoint_from stack_b [ctx_b;in_b;k_b]}) : Lemma
  (create_initial_trusted_state is_win ctx_b in_b num_val k_b stack_b h0 == state_to_S (create_initial_vale_state is_win ctx_b in_b num_val k_b stack_b h0)) =
    let s_init = create_initial_trusted_state is_win ctx_b in_b num_val k_b stack_b h0 in
    let s0 = create_initial_vale_state is_win ctx_b in_b num_val k_b stack_b h0 in
    let s1 = state_to_S s0 in
    assert (FunctionalExtensionality.feq (regs' s1.TS.state) (regs' s_init.TS.state));
    assert (FunctionalExtensionality.feq (xmms' s1.TS.state) (xmms' s_init.TS.state))

let implies_pre_aux (b:s8) (n:nat64) : Lemma
  (requires length b == 64 `op_Multiply` n)
  (ensures buffer_length #(X64.Memory.TBase X64.Memory.TUInt128) b == 4 `op_Multiply` n) = 
    length_t_eq (TBase TUInt128) b

let implies_pre (is_win:bool) (h0:HS.mem) (ctx_b:s8) (in_b:s8) (num_val:nat64) (k_b:s8)  (stack_b:b8) : Lemma
  (requires pre_cond h0 ctx_b in_b num_val k_b /\ B.length stack_b == (if is_win then 264 else 104) /\ live h0 stack_b /\ buf_disjoint_from stack_b [ctx_b;in_b;k_b])
  (ensures (
B.length stack_b == (if is_win then 264 else 104) /\ live h0 stack_b /\ buf_disjoint_from stack_b [ctx_b;in_b;k_b] /\ (
  let s0 = create_initial_vale_state is_win ctx_b in_b num_val k_b stack_b h0 in
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) ctx_b;
  length_t_eq (TBase TUInt128) in_b;
  length_t_eq (TBase TUInt128) k_b;
  va_pre (va_code_sha_update_bytes_stdcall is_win) s0 is_win stack_b ctx_b in_b num_val k_b ))) =
  let s0 = create_initial_vale_state is_win ctx_b in_b num_val k_b stack_b h0 in
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) ctx_b;
  length_t_eq (TBase TUInt128) in_b;
  length_t_eq (TBase TUInt128) k_b;
  assert(Interop.disjoint stack_b ctx_b);
  assert(Interop.disjoint stack_b in_b);
  assert(Interop.disjoint stack_b k_b);
  let k_b128 = BV.mk_buffer_view k_b Views.view128 in
  let t = TBase TUInt128 in
  implies_pre_aux in_b num_val;
  assert (Seq.equal
    (buffer_as_seq #t s0.mem k_b)
    (BV.as_seq h0 k_b128));
  ()

let implies_post (is_win:bool) (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) (ctx_b:s8) (in_b:s8) (num_val:nat64) (k_b:s8)  (stack_b:b8) : Lemma
  (requires pre_cond va_s0.mem.hs ctx_b in_b num_val k_b /\ B.length stack_b == (if is_win then 264 else 104) /\ live va_s0.mem.hs stack_b /\ buf_disjoint_from stack_b [ctx_b;in_b;k_b]/\
    va_post (va_code_sha_update_bytes_stdcall is_win) va_s0 va_sM va_fM is_win stack_b ctx_b in_b num_val k_b )
  (ensures post_cond va_s0.mem.hs va_sM.mem.hs ctx_b in_b num_val k_b /\ M.modifies (M.loc_union (M.loc_buffer ctx_b) (M.loc_buffer stack_b)) va_s0.mem.hs va_sM.mem.hs) =
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) ctx_b;
  length_t_eq (TBase TUInt128) in_b;
  length_t_eq (TBase TUInt128) k_b;
  let ctx_b128 = BV.mk_buffer_view ctx_b Views.view128 in
  let in_b128 = BV.mk_buffer_view in_b Views.view128 in
  let t = TBase TUInt128 in
  let h = va_s0.mem.hs in
  let h' = va_sM.mem.hs in
  let ctx_b128 = BV.mk_buffer_view ctx_b Views.view128 in
  let in_b128 = BV.mk_buffer_view in_b Views.view128 in
  let input_LE = seq_nat8_to_seq_U8 (le_seq_quad32_to_bytes (BV.as_seq h' in_b128)) in
  let hash_in = le_bytes_to_hash (le_seq_quad32_to_bytes (BV.as_seq h ctx_b128)) in
  let hash_out = le_bytes_to_hash (le_seq_quad32_to_bytes (BV.as_seq h' ctx_b128)) in  
  assert (Seq.equal
    (BV.as_seq va_sM.mem.hs in_b128)
    (buffer_as_seq #t va_sM.mem in_b));
  assert (Seq.equal
    (BV.as_seq va_s0.mem.hs ctx_b128)
    (buffer_as_seq #t va_s0.mem ctx_b));
  assert (Seq.equal
    (BV.as_seq va_sM.mem.hs ctx_b128)
    (buffer_as_seq #t va_sM.mem ctx_b)); 
  ()

let lemma_ghost_sha_update_bytes_stdcall is_win ctx_b in_b num_val k_b stack_b h0 =
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) ctx_b;
  length_t_eq (TBase TUInt128) in_b;
  length_t_eq (TBase TUInt128) k_b;
  implies_pre is_win h0 ctx_b in_b num_val k_b stack_b;
  let s0 = create_initial_trusted_state is_win ctx_b in_b num_val k_b stack_b h0 in
  let s0' = create_initial_vale_state is_win ctx_b in_b num_val k_b stack_b h0 in
  create_lemma is_win ctx_b in_b num_val k_b stack_b h0;
  let s_v, f_v = va_lemma_sha_update_bytes_stdcall (va_code_sha_update_bytes_stdcall is_win) s0' is_win stack_b ctx_b in_b num_val k_b in
  implies_post is_win s0' s_v f_v ctx_b in_b num_val k_b stack_b;
   let s1 = Some?.v (TS.taint_eval_code (va_code_sha_update_bytes_stdcall is_win) f_v s0) in
  assert (state_eq_S s1 (state_to_S s_v));
  assert (FunctionalExtensionality.feq s1.TS.state.BS.regs s_v.regs);
  assert (FunctionalExtensionality.feq s1.TS.state.BS.xmms s_v.xmms);
  s1, f_v, s_v.mem.hs

#set-options "--max_fuel 0 --max_ifuel 0"

let sha_update_bytes_stdcall ctx_b in_b num_val k_b =
  push_frame();
  let (stack_b:b8) = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t (if win then 264 else 104)) in
  if win then
  st_put 
    (fun h -> pre_cond h ctx_b in_b num_val k_b /\ B.length stack_b == 264 /\ live h stack_b /\ buf_disjoint_from stack_b [ctx_b;in_b;k_b])
    (fun h -> let _, _, h1 =
      lemma_ghost_sha_update_bytes_stdcall true ctx_b in_b num_val k_b stack_b h
    in h1)
  else st_put
    (fun h -> pre_cond h ctx_b in_b num_val k_b /\ B.length stack_b == 104 /\ live h stack_b /\ buf_disjoint_from stack_b [ctx_b;in_b;k_b])
    (fun h -> let _, _, h1 =
      lemma_ghost_sha_update_bytes_stdcall false ctx_b in_b num_val k_b stack_b h
    in h1);
  pop_frame()
