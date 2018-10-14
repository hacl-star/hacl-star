module GHash_extra_stdcall

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

open Vale_ghash_extra_stdcall

#set-options "--initial_fuel 6 --max_fuel 6 --initial_ifuel 0 --max_ifuel 0"
let create_buffer_list (in_b:s8) (hash_b:s8) (h_b:s8) (stack_b:b8)  : (l:list b8{
    l == [stack_b;in_b;hash_b;h_b] /\
  (forall x. {:pattern List.memP x l} List.memP x l <==> (x == in_b \/ x == hash_b \/ x == h_b \/ x == stack_b))}) =
  [stack_b;in_b;hash_b;h_b]

#set-options "--max_fuel 0 --max_ifuel 0"

let create_initial_trusted_state is_win in_b hash_b h_b num_bytes orig_hash stack_b (h0:HS.mem{pre_cond h0 in_b hash_b h_b (UInt64.uint_to_t num_bytes) orig_hash /\ B.length stack_b == (if is_win then 264 else 104) /\ live h0 stack_b /\ buf_disjoint_from stack_b [in_b;hash_b;h_b]}) : GTot TS.traceState =
  let taint_func (x:b8) : GTot taint =
    if StrongExcludedMiddle.strong_excluded_middle (x == in_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == hash_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == h_b) then Secret else
    Public in
  let buffers = create_buffer_list in_b hash_b h_b stack_b in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_in_b = addrs in_b in
  let addr_hash_b = addrs hash_b in
  let addr_h_b = addrs h_b in
  let addr_stack:nat64 = addrs stack_b + (if is_win then 224 else 64) in
  let regs = if is_win then (
    fun r -> begin match r with
    | Rsp -> addr_stack
    | Rcx -> addr_in_b
    | Rdx -> addr_hash_b
    | R8 -> addr_h_b
    | R9 -> num_bytes
    | _ -> init_regs r end)
  else (
    fun r -> begin match r with
    | Rsp -> addr_stack
    | Rdi -> addr_in_b
    | Rsi -> addr_hash_b
    | Rdx -> addr_h_b
    | Rcx -> num_bytes
    | _ -> init_regs r end)
  in let regs = FunctionalExtensionality.on reg regs
  in let xmms = FunctionalExtensionality.on xmm init_xmms in
  let (s0:BS.state) = {BS.ok = true; BS.regs = regs; BS.xmms = xmms; BS.flags = 0;
       BS.mem = Interop.down_mem h0 addrs buffers} in
  {TS.state = s0; TS.trace = []; TS.memTaint = create_valid_memtaint mem buffers taint_func}

val lemma_ghost_ghash_extra_stdcall: is_win:bool -> in_b:s8 -> hash_b:s8 -> h_b:s8 -> num_bytes:nat64 -> orig_hash:Ghost.erased (quad32) ->  stack_b:b8 -> (h0:HS.mem{pre_cond h0 in_b hash_b h_b (UInt64.uint_to_t num_bytes) orig_hash /\ B.length stack_b == (if is_win then 264 else 104) /\ live h0 stack_b /\ buf_disjoint_from stack_b [in_b;hash_b;h_b]}) ->
  Ghost (TS.traceState * nat * HS.mem)
    (requires True)
    (ensures (fun (s1, f1, h1) ->
      (let s0 = create_initial_trusted_state is_win in_b hash_b h_b num_bytes orig_hash stack_b h0 in
      Some s1 == TS.taint_eval_code (va_code_ghash_extra_stdcall is_win) f1 s0 /\
      Interop.correct_down h1 addrs [stack_b;in_b;hash_b;h_b] s1.TS.state.BS.mem /\
      post_cond h0 h1 in_b hash_b h_b (UInt64.uint_to_t num_bytes) orig_hash  /\
      calling_conventions is_win s0 s1 /\
      M.modifies (M.loc_union (M.loc_buffer stack_b) ( M.loc_buffer hash_b)) h0 h1)
    ))

// ===============================================================================================
//  Everything below this line is untrusted

let create_initial_vale_state is_win in_b hash_b h_b num_bytes orig_hash stack_b (h0:HS.mem{pre_cond h0 in_b hash_b h_b (UInt64.uint_to_t num_bytes) orig_hash /\ B.length stack_b == (if is_win then 264 else 104) /\ live h0 stack_b /\ buf_disjoint_from stack_b [in_b;hash_b;h_b]}) : GTot va_state =
  let taint_func (x:b8) : GTot taint =
    if StrongExcludedMiddle.strong_excluded_middle (x == in_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == hash_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == h_b) then Secret else
    Public in
  let buffers = create_buffer_list in_b hash_b h_b stack_b in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_in_b = addrs in_b in
  let addr_hash_b = addrs hash_b in
  let addr_h_b = addrs h_b in
  let addr_stack:nat64 = addrs stack_b + (if is_win then 224 else 64) in
  let regs = if is_win then (
    fun r -> begin match r with
    | Rsp -> addr_stack
    | Rcx -> addr_in_b
    | Rdx -> addr_hash_b
    | R8 -> addr_h_b
    | R9 -> num_bytes
    | _ -> init_regs r end)
  else (
    fun r -> begin match r with
    | Rsp -> addr_stack
    | Rdi -> addr_in_b
    | Rsi -> addr_hash_b
    | Rdx -> addr_h_b
    | Rcx -> num_bytes
    | _ -> init_regs r end)
  in let regs = X64.Vale.Regs.of_fun regs
  in let xmms = X64.Vale.Xmms.of_fun init_xmms in
  {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem;
      memTaint = create_valid_memtaint mem buffers taint_func}

let create_lemma is_win in_b hash_b h_b num_bytes orig_hash stack_b (h0:HS.mem{pre_cond h0 in_b hash_b h_b (UInt64.uint_to_t num_bytes) orig_hash /\ B.length stack_b == (if is_win then 264 else 104) /\ live h0 stack_b /\ buf_disjoint_from stack_b [in_b;hash_b;h_b]}) : Lemma
  (create_initial_trusted_state is_win in_b hash_b h_b num_bytes orig_hash stack_b h0 == state_to_S (create_initial_vale_state is_win in_b hash_b h_b num_bytes orig_hash stack_b h0)) =
    let s_init = create_initial_trusted_state is_win in_b hash_b h_b num_bytes orig_hash stack_b h0 in
    let s0 = create_initial_vale_state is_win in_b hash_b h_b num_bytes orig_hash stack_b h0 in
    let s1 = state_to_S s0 in
    assert (FunctionalExtensionality.feq (regs' s1.TS.state) (regs' s_init.TS.state));
    assert (FunctionalExtensionality.feq (xmms' s1.TS.state) (xmms' s_init.TS.state))

let implies_pre (is_win:bool) (h0:HS.mem) (in_b:s8) (hash_b:s8) (h_b:s8) (num_bytes:nat64) (orig_hash:Ghost.erased (quad32))  (stack_b:b8) : Lemma
  (requires pre_cond h0 in_b hash_b h_b (UInt64.uint_to_t num_bytes) orig_hash /\ B.length stack_b == (if is_win then 264 else 104) /\ live h0 stack_b /\ buf_disjoint_from stack_b [in_b;hash_b;h_b])
  (ensures (
B.length stack_b == (if is_win then 264 else 104) /\ live h0 stack_b /\ buf_disjoint_from stack_b [in_b;hash_b;h_b] /\ (
  let s0 = create_initial_vale_state is_win in_b hash_b h_b num_bytes orig_hash stack_b h0 in
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) in_b;
  length_t_eq (TBase TUInt128) hash_b;
  length_t_eq (TBase TUInt128) h_b;
  va_pre (va_code_ghash_extra_stdcall is_win) s0 is_win stack_b in_b hash_b h_b num_bytes (Ghost.reveal orig_hash) ))) =
  let s0 = create_initial_vale_state is_win in_b hash_b h_b num_bytes orig_hash stack_b h0 in  
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) in_b;
  length_t_eq (TBase TUInt128) hash_b;
  length_t_eq (TBase TUInt128) h_b;
  assert(Interop.disjoint stack_b in_b);
  assert(Interop.disjoint stack_b hash_b);
  assert(Interop.disjoint stack_b h_b);
  assert (Seq.equal (buffer_to_seq_quad32 in_b h0) (buffer128_as_seq (va_get_mem s0) in_b));
  let h128_b = BV.mk_buffer_view h_b Views.view128 in
  assert (Seq.equal (buffer_as_seq (va_get_mem s0) h_b) (BV.as_seq h0 h128_b));
  BV.as_seq_sel h0 h128_b 0;
  let hash128_b = BV.mk_buffer_view hash_b Views.view128 in
  assert (Seq.equal (buffer_as_seq (va_get_mem s0) hash_b) (BV.as_seq h0 hash128_b));
  BV.as_seq_sel h0 hash128_b 0;  
  ()

let implies_post (is_win:bool) (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) (in_b:s8) (hash_b:s8) (h_b:s8) (num_bytes:nat64) (orig_hash:Ghost.erased (quad32))  (stack_b:b8) : Lemma
  (requires pre_cond va_s0.mem.hs in_b hash_b h_b (UInt64.uint_to_t num_bytes) orig_hash /\ B.length stack_b == (if is_win then 264 else 104) /\ live va_s0.mem.hs stack_b /\ buf_disjoint_from stack_b [in_b;hash_b;h_b]/\
    va_post (va_code_ghash_extra_stdcall is_win) va_s0 va_sM va_fM is_win stack_b in_b hash_b h_b num_bytes (Ghost.reveal orig_hash) )
  (ensures post_cond va_s0.mem.hs va_sM.mem.hs in_b hash_b h_b (UInt64.uint_to_t num_bytes) orig_hash ) =
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) in_b;
  length_t_eq (TBase TUInt128) hash_b;
  length_t_eq (TBase TUInt128) h_b;
  assert (Seq.equal (buffer_to_seq_quad32 in_b va_sM.mem.hs) (buffer128_as_seq (va_get_mem va_sM) in_b));
  let hash128_b = BV.mk_buffer_view hash_b Views.view128 in
  assert (Seq.equal (buffer_as_seq (va_get_mem va_s0) hash_b) (BV.as_seq va_s0.mem.hs hash128_b));
  assert (Seq.equal (buffer_as_seq (va_get_mem va_sM) hash_b) (BV.as_seq va_sM.mem.hs hash128_b));
  BV.as_seq_sel va_s0.mem.hs hash128_b 0;
  BV.as_seq_sel va_sM.mem.hs hash128_b 0;
  let h128_b = BV.mk_buffer_view h_b Views.view128 in
  assert (Seq.equal (buffer_as_seq (va_get_mem va_s0) h_b) (BV.as_seq va_s0.mem.hs h128_b));
  BV.as_seq_sel va_s0.mem.hs h128_b 0;  
  ()

#set-options "--max_fuel 0 --initial_ifuel 1 --max_ifuel 1"

let lemma_ghost_ghash_extra_stdcall is_win in_b hash_b h_b num_bytes orig_hash stack_b h0 =
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) in_b;
  length_t_eq (TBase TUInt128) hash_b;
  length_t_eq (TBase TUInt128) h_b;
  implies_pre is_win h0 in_b hash_b h_b num_bytes orig_hash stack_b;
  let s0 = create_initial_trusted_state is_win in_b hash_b h_b num_bytes orig_hash stack_b h0 in
  let s0' = create_initial_vale_state is_win in_b hash_b h_b num_bytes orig_hash stack_b h0 in
  create_lemma is_win in_b hash_b h_b num_bytes orig_hash stack_b h0;
  let s_v, f_v = va_lemma_ghash_extra_stdcall (va_code_ghash_extra_stdcall is_win) s0' is_win stack_b in_b hash_b h_b num_bytes (Ghost.reveal orig_hash) in
  implies_post is_win s0' s_v f_v in_b hash_b h_b num_bytes orig_hash stack_b;
  let s1 = Some?.v (TS.taint_eval_code (va_code_ghash_extra_stdcall is_win) f_v s0) in
  assert (state_eq_S s1 (state_to_S s_v));
  assert (FunctionalExtensionality.feq s1.TS.state.BS.regs (X64.Vale.Regs.to_fun s_v.regs));
  assert (FunctionalExtensionality.feq s1.TS.state.BS.xmms (X64.Vale.Xmms.to_fun s_v.xmms));
  assert (M.modifies (M.loc_union (M.loc_buffer stack_b) ( M.loc_buffer hash_b)) h0 s_v.mem.hs);
  s1, f_v, s_v.mem.hs

#set-options "--max_fuel 0 --max_ifuel 0"

irreducible
let ghash_extra_stdcall_aux (in_b:s8) (hash_b:s8) (h_b:s8) (num_bytes:UInt64.t) (orig_hash:Ghost.erased (quad32)) (stack_b:b8) : Stack unit
  (fun h -> pre_cond h in_b hash_b h_b num_bytes orig_hash  /\ B.length stack_b == (if win then 264 else 104) /\ live h stack_b /\ buf_disjoint_from stack_b [in_b;hash_b;h_b])
  (fun h0 _ h1 ->
    post_cond h0 h1 in_b hash_b h_b num_bytes orig_hash  /\
    M.modifies (M.loc_union (M.loc_buffer stack_b) ( M.loc_buffer hash_b)) h0 h1) =
  if win then
  st_put
    (fun h -> pre_cond h in_b hash_b h_b num_bytes orig_hash /\ B.length stack_b == 264 /\ live h stack_b /\ buf_disjoint_from stack_b [in_b;hash_b;h_b])
    (fun h -> let _, _, h1 =
      lemma_ghost_ghash_extra_stdcall true in_b hash_b h_b (UInt64.v num_bytes) orig_hash stack_b h
    in (), h1)
  else st_put
    (fun h -> pre_cond h in_b hash_b h_b num_bytes orig_hash /\ B.length stack_b == 104 /\ live h stack_b /\ buf_disjoint_from stack_b [in_b;hash_b;h_b])
    (fun h -> let _, _, h1 =
      lemma_ghost_ghash_extra_stdcall false in_b hash_b h_b (UInt64.v num_bytes) orig_hash stack_b h
    in (), h1)

let ghash_extra_stdcall in_b hash_b h_b num_bytes orig_hash  =
  push_frame();
  let (stack_b:b8) = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t (if win then 264 else 104)) in
  ghash_extra_stdcall_aux in_b hash_b h_b num_bytes orig_hash stack_b;
  pop_frame()
