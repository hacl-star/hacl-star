module Gcm_load_xor_stdcall

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

open Vale_gcm_load_xor_stdcall

#set-options "--initial_fuel 6 --max_fuel 6 --initial_ifuel 0 --max_ifuel 0"
let create_buffer_list (plain_b:s8) (mask_b:s8) (cipher_b:s8) (stack_b:b8)  : (l:list b8{
    l == [stack_b;plain_b;mask_b;cipher_b] /\
  (forall x. {:pattern List.memP x l} List.memP x l <==> (x == plain_b \/ x == mask_b \/ x == cipher_b \/ x == stack_b))}) =
  [stack_b;plain_b;mask_b;cipher_b]

#set-options "--max_fuel 0 --max_ifuel 0"

let create_initial_trusted_state is_win plain_b mask_b cipher_b offset num_blocks key iv stack_b (h0:HS.mem{pre_cond h0 plain_b mask_b cipher_b (UInt64.uint_to_t offset) num_blocks key iv /\ B.length stack_b == 40 /\ live h0 stack_b /\ buf_disjoint_from stack_b [plain_b;mask_b;cipher_b]}) : GTot TS.traceState =
  let taint_func (x:b8) : GTot taint =
    if StrongExcludedMiddle.strong_excluded_middle (x == plain_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == mask_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == cipher_b) then Secret else
    Public in
  let buffers = create_buffer_list plain_b mask_b cipher_b stack_b in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_plain_b = addrs plain_b in
  let addr_mask_b = addrs mask_b in
  let addr_cipher_b = addrs cipher_b in
  let addr_stack:nat64 = addrs stack_b + 0 in
  let regs = if is_win then (
    fun r -> begin match r with
    | Rsp -> addr_stack
    | Rcx -> addr_plain_b
    | Rdx -> addr_mask_b
    | R8 -> addr_cipher_b
    | R9 -> offset
    | _ -> init_regs r end)
  else (
    fun r -> begin match r with
    | Rsp -> addr_stack
    | Rdi -> addr_plain_b
    | Rsi -> addr_mask_b
    | Rdx -> addr_cipher_b
    | Rcx -> offset
    | _ -> init_regs r end)
  in let regs = FunctionalExtensionality.on reg regs
  in let xmms = FunctionalExtensionality.on xmm init_xmms in
  let (s0:BS.state) = {BS.ok = true; BS.regs = regs; BS.xmms = xmms; BS.flags = 0;
       BS.mem = Interop.down_mem h0 addrs buffers} in
  {TS.state = s0; TS.trace = []; TS.memTaint = create_valid_memtaint mem buffers taint_func}

val lemma_ghost_gcm_load_xor_stdcall: is_win:bool -> plain_b:s8 -> mask_b:s8 -> cipher_b:s8 -> offset:nat64 -> num_blocks:Ghost.erased (nat64) -> key:Ghost.erased (aes_key_LE AES_128) -> iv:Ghost.erased (quad32) ->  stack_b:b8 -> (h0:HS.mem{pre_cond h0 plain_b mask_b cipher_b (UInt64.uint_to_t offset) num_blocks key iv /\ B.length stack_b == 40 /\ live h0 stack_b /\ buf_disjoint_from stack_b [plain_b;mask_b;cipher_b]}) ->
  Ghost (TS.traceState * nat * HS.mem)
    (requires True)
    (ensures (fun (s1, f1, h1) ->
      (let s0 = create_initial_trusted_state is_win plain_b mask_b cipher_b offset num_blocks key iv stack_b h0 in
      Some s1 == TS.taint_eval_code (va_code_gcm_load_xor_stdcall is_win) f1 s0 /\
      Interop.correct_down h1 addrs [stack_b;plain_b;mask_b;cipher_b] s1.TS.state.BS.mem /\
      post_cond h0 h1 plain_b mask_b cipher_b (UInt64.uint_to_t offset) num_blocks key iv  /\
      calling_conventions is_win s0 s1 /\
      M.modifies (M.loc_union (M.loc_buffer stack_b) ( M.loc_buffer cipher_b)) h0 h1)
    ))

// ===============================================================================================
//  Everything below this line is untrusted

let create_initial_vale_state is_win plain_b mask_b cipher_b offset num_blocks key iv stack_b (h0:HS.mem{pre_cond h0 plain_b mask_b cipher_b (UInt64.uint_to_t offset) num_blocks key iv /\ B.length stack_b == 40 /\ live h0 stack_b /\ buf_disjoint_from stack_b [plain_b;mask_b;cipher_b]}) : GTot va_state =
  let taint_func (x:b8) : GTot taint =
    if StrongExcludedMiddle.strong_excluded_middle (x == plain_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == mask_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == cipher_b) then Secret else
    Public in
  let buffers = create_buffer_list plain_b mask_b cipher_b stack_b in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_plain_b = addrs plain_b in
  let addr_mask_b = addrs mask_b in
  let addr_cipher_b = addrs cipher_b in
  let addr_stack:nat64 = addrs stack_b + 0 in
  let regs = if is_win then (
    fun r -> begin match r with
    | Rsp -> addr_stack
    | Rcx -> addr_plain_b
    | Rdx -> addr_mask_b
    | R8 -> addr_cipher_b
    | R9 -> offset
    | _ -> init_regs r end)
  else (
    fun r -> begin match r with
    | Rsp -> addr_stack
    | Rdi -> addr_plain_b
    | Rsi -> addr_mask_b
    | Rdx -> addr_cipher_b
    | Rcx -> offset
    | _ -> init_regs r end)
  in let regs = FunctionalExtensionality.on reg regs
  in let xmms = FunctionalExtensionality.on xmm init_xmms in
  {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem;
      memTaint = create_valid_memtaint mem buffers taint_func}

let create_lemma is_win plain_b mask_b cipher_b offset num_blocks key iv stack_b (h0:HS.mem{pre_cond h0 plain_b mask_b cipher_b (UInt64.uint_to_t offset) num_blocks key iv /\ B.length stack_b == 40 /\ live h0 stack_b /\ buf_disjoint_from stack_b [plain_b;mask_b;cipher_b]}) : Lemma
  (create_initial_trusted_state is_win plain_b mask_b cipher_b offset num_blocks key iv stack_b h0 == state_to_S (create_initial_vale_state is_win plain_b mask_b cipher_b offset num_blocks key iv stack_b h0)) =
    let s_init = create_initial_trusted_state is_win plain_b mask_b cipher_b offset num_blocks key iv stack_b h0 in
    let s0 = create_initial_vale_state is_win plain_b mask_b cipher_b offset num_blocks key iv stack_b h0 in
    let s1 = state_to_S s0 in
    assert (FunctionalExtensionality.feq (regs' s1.TS.state) (regs' s_init.TS.state));
    assert (FunctionalExtensionality.feq (xmms' s1.TS.state) (xmms' s_init.TS.state))

let implies_pre (is_win:bool) (h0:HS.mem) (plain_b:s8) (mask_b:s8) (cipher_b:s8) (offset:nat64) (num_blocks:Ghost.erased (nat64)) (key:Ghost.erased (aes_key_LE AES_128)) (iv:Ghost.erased (quad32))  (stack_b:b8) : Lemma
  (requires pre_cond h0 plain_b mask_b cipher_b (UInt64.uint_to_t offset) num_blocks key iv /\ B.length stack_b == 40 /\ live h0 stack_b /\ buf_disjoint_from stack_b [plain_b;mask_b;cipher_b])
  (ensures (
B.length stack_b == 40 /\ live h0 stack_b /\ buf_disjoint_from stack_b [plain_b;mask_b;cipher_b] /\ (
  let s0 = create_initial_vale_state is_win plain_b mask_b cipher_b offset num_blocks key iv stack_b h0 in
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) plain_b;
  length_t_eq (TBase TUInt128) mask_b;
  length_t_eq (TBase TUInt128) cipher_b;
  va_pre (va_code_gcm_load_xor_stdcall is_win) s0 is_win stack_b plain_b mask_b cipher_b offset (Ghost.reveal num_blocks) (Ghost.reveal key) (Ghost.reveal iv) ))) =
  let va_s0 = create_initial_vale_state is_win plain_b mask_b cipher_b offset num_blocks key iv stack_b h0 in
  assert (Seq.equal
    (buffer128_as_seq (va_get_mem va_s0) plain_b)
    (buffer_to_seq_quad32 plain_b va_s0.mem.hs));
  assert (Seq.equal
    (buffer128_as_seq (va_get_mem va_s0) cipher_b)
    (buffer_to_seq_quad32 cipher_b va_s0.mem.hs));
  let mask128 = BV.mk_buffer_view mask_b Views.view128 in
  assert (Seq.equal (buffer_as_seq (va_get_mem va_s0) mask_b) (BV.as_seq va_s0.mem.hs mask128));
  BV.as_seq_sel h0 mask128 0;   
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) plain_b;
  length_t_eq (TBase TUInt128) mask_b;
  length_t_eq (TBase TUInt128) cipher_b;
  assert(Interop.disjoint stack_b plain_b);
  assert(Interop.disjoint stack_b mask_b);
  assert(Interop.disjoint stack_b cipher_b);
  ()

let implies_post (is_win:bool) (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) (plain_b:s8) (mask_b:s8) (cipher_b:s8) (offset:nat64) (num_blocks:Ghost.erased (nat64)) (key:Ghost.erased (aes_key_LE AES_128)) (iv:Ghost.erased (quad32))  (stack_b:b8) : Lemma
  (requires pre_cond va_s0.mem.hs plain_b mask_b cipher_b (UInt64.uint_to_t offset) num_blocks key iv /\ B.length stack_b == 40 /\ live va_s0.mem.hs stack_b /\ buf_disjoint_from stack_b [plain_b;mask_b;cipher_b]/\
    va_post (va_code_gcm_load_xor_stdcall is_win) va_s0 va_sM va_fM is_win stack_b plain_b mask_b cipher_b offset (Ghost.reveal num_blocks) (Ghost.reveal key) (Ghost.reveal iv) )
  (ensures post_cond va_s0.mem.hs va_sM.mem.hs plain_b mask_b cipher_b (UInt64.uint_to_t offset) num_blocks key iv ) =
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) plain_b;
  length_t_eq (TBase TUInt128) mask_b;
  length_t_eq (TBase TUInt128) cipher_b;
  assert (Seq.equal
    (buffer128_as_seq (va_get_mem va_s0) cipher_b)
    (buffer_to_seq_quad32 cipher_b va_s0.mem.hs));
  assert (Seq.equal
    (buffer128_as_seq (va_get_mem va_sM) cipher_b)
    (buffer_to_seq_quad32 cipher_b va_sM.mem.hs));
  assert (Seq.equal
    (buffer128_as_seq (va_get_mem va_sM) plain_b)
    (buffer_to_seq_quad32 plain_b va_sM.mem.hs));
  let mask128 = BV.mk_buffer_view mask_b Views.view128 in
  assert (Seq.equal (buffer_as_seq (va_get_mem va_s0) mask_b) (BV.as_seq va_s0.mem.hs mask128));
  BV.as_seq_sel va_s0.mem.hs mask128 0;  
  ()

#set-options "--max_fuel 0 --initial_ifuel 1 --max_ifuel 1"

let lemma_ghost_gcm_load_xor_stdcall is_win plain_b mask_b cipher_b offset num_blocks key iv stack_b h0 =
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) plain_b;
  length_t_eq (TBase TUInt128) mask_b;
  length_t_eq (TBase TUInt128) cipher_b;
  implies_pre is_win h0 plain_b mask_b cipher_b offset num_blocks key iv stack_b;
  let s0 = create_initial_trusted_state is_win plain_b mask_b cipher_b offset num_blocks key iv stack_b h0 in
  let s0' = create_initial_vale_state is_win plain_b mask_b cipher_b offset num_blocks key iv stack_b h0 in
  create_lemma is_win plain_b mask_b cipher_b offset num_blocks key iv stack_b h0;
  let s_v, f_v = va_lemma_gcm_load_xor_stdcall (va_code_gcm_load_xor_stdcall is_win) s0' is_win stack_b plain_b mask_b cipher_b offset (Ghost.reveal num_blocks) (Ghost.reveal key) (Ghost.reveal iv) in
  implies_post is_win s0' s_v f_v plain_b mask_b cipher_b offset num_blocks key iv stack_b;
  let s1 = Some?.v (TS.taint_eval_code (va_code_gcm_load_xor_stdcall is_win) f_v s0) in
  assert (state_eq_S s1 (state_to_S s_v));
  assert (FunctionalExtensionality.feq s1.TS.state.BS.regs s_v.regs);
  assert (FunctionalExtensionality.feq s1.TS.state.BS.xmms s_v.xmms);
  assert (M.modifies (M.loc_union (M.loc_buffer stack_b) ( M.loc_buffer cipher_b)) h0 s_v.mem.hs);
  s1, f_v, s_v.mem.hs

#set-options "--max_fuel 0 --max_ifuel 0"

irreducible
let gcm_load_xor_stdcall_aux (plain_b:s8) (mask_b:s8) (cipher_b:s8) (offset:UInt64.t) (num_blocks:Ghost.erased (nat64)) (key:Ghost.erased (aes_key_LE AES_128)) (iv:Ghost.erased (quad32)) (stack_b:b8) : Stack unit
  (fun h -> pre_cond h plain_b mask_b cipher_b offset num_blocks key iv  /\ B.length stack_b == 40 /\ live h stack_b /\ buf_disjoint_from stack_b [plain_b;mask_b;cipher_b])
  (fun h0 _ h1 ->
    post_cond h0 h1 plain_b mask_b cipher_b offset num_blocks key iv  /\
    M.modifies (M.loc_union (M.loc_buffer stack_b) ( M.loc_buffer cipher_b)) h0 h1) =
  if win then
  st_put
    (fun h -> pre_cond h plain_b mask_b cipher_b offset num_blocks key iv /\ B.length stack_b == 40 /\ live h stack_b /\ buf_disjoint_from stack_b [plain_b;mask_b;cipher_b])
    (fun h -> let _, _, h1 =
      lemma_ghost_gcm_load_xor_stdcall true plain_b mask_b cipher_b (UInt64.v offset) num_blocks key iv stack_b h
    in (), h1)
  else st_put
    (fun h -> pre_cond h plain_b mask_b cipher_b offset num_blocks key iv /\ B.length stack_b == 40 /\ live h stack_b /\ buf_disjoint_from stack_b [plain_b;mask_b;cipher_b])
    (fun h -> let _, _, h1 =
      lemma_ghost_gcm_load_xor_stdcall false plain_b mask_b cipher_b (UInt64.v offset) num_blocks key iv stack_b h
    in (), h1)

let gcm_load_xor_stdcall plain_b mask_b cipher_b offset num_blocks key iv  =
  push_frame();
  let (stack_b:b8) = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 40) in
  gcm_load_xor_stdcall_aux plain_b mask_b cipher_b offset num_blocks key iv stack_b;
  pop_frame()
