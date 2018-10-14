module AESEncryptBlockStdcall

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

open Vale_AESEncryptBlockStdcall

#set-options "--initial_fuel 6 --max_fuel 6 --initial_ifuel 0 --max_ifuel 0"
let create_buffer_list (output_b:s8) (input_b:s8) (keys_b:s8) (stack_b:b8)  : (l:list b8{
    l == [stack_b;output_b;input_b;keys_b] /\
  (forall x. {:pattern List.memP x l} List.memP x l <==> (x == output_b \/ x == input_b \/ x == keys_b \/ x == stack_b))}) =
  [stack_b;output_b;input_b;keys_b]

#set-options "--max_fuel 0 --max_ifuel 0"

let create_initial_trusted_state is_win output_b input_b key keys_b stack_b (h0:HS.mem{pre_cond h0 output_b input_b key keys_b /\ B.length stack_b == (if is_win then 256 else 96) /\ live h0 stack_b /\ buf_disjoint_from stack_b [output_b;input_b;keys_b]}) : GTot TS.traceState =
  let taint_func (x:b8) : GTot taint =
    if StrongExcludedMiddle.strong_excluded_middle (x == output_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == input_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == keys_b) then Secret else
    Public in
  let buffers = create_buffer_list output_b input_b keys_b stack_b in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_output_b = addrs output_b in
  let addr_input_b = addrs input_b in
  let addr_keys_b = addrs keys_b in
  let addr_stack:nat64 = addrs stack_b + (if is_win then 224 else 64) in
  let regs = if is_win then (
    fun r -> begin match r with
    | Rsp -> addr_stack
    | Rcx -> addr_output_b
    | Rdx -> addr_input_b
    | R8 -> addr_keys_b
    | _ -> init_regs r end)
  else (
    fun r -> begin match r with
    | Rsp -> addr_stack
    | Rdi -> addr_output_b
    | Rsi -> addr_input_b
    | Rdx -> addr_keys_b
    | _ -> init_regs r end)
  in let regs = FunctionalExtensionality.on reg regs
  in let xmms = FunctionalExtensionality.on xmm init_xmms in
  let (s0:BS.state) = {BS.ok = true; BS.regs = regs; BS.xmms = xmms; BS.flags = 0;
       BS.mem = Interop.down_mem h0 addrs buffers} in
  {TS.state = s0; TS.trace = []; TS.memTaint = create_valid_memtaint mem buffers taint_func}

val lemma_ghost_AESEncryptBlockStdcall: is_win:bool -> output_b:s8 -> input_b:s8 -> key:Ghost.erased (aes_key_LE AES_128) -> keys_b:s8 ->  stack_b:b8 -> (h0:HS.mem{pre_cond h0 output_b input_b key keys_b /\ B.length stack_b == (if is_win then 256 else 96) /\ live h0 stack_b /\ buf_disjoint_from stack_b [output_b;input_b;keys_b]}) ->
  Ghost (TS.traceState * nat * HS.mem)
    (requires True)
    (ensures (fun (s1, f1, h1) ->
      (let s0 = create_initial_trusted_state is_win output_b input_b key keys_b stack_b h0 in
      Some s1 == TS.taint_eval_code (va_code_AESEncryptBlockStdcall is_win) f1 s0 /\
      Interop.correct_down h1 addrs [stack_b;output_b;input_b;keys_b] s1.TS.state.BS.mem /\
      post_cond h0 h1 output_b input_b key keys_b  /\
      calling_conventions is_win s0 s1 /\
      M.modifies (M.loc_union (M.loc_buffer stack_b) ( M.loc_buffer output_b)) h0 h1)
    ))

// ===============================================================================================
//  Everything below this line is untrusted

let create_initial_vale_state is_win output_b input_b key keys_b stack_b (h0:HS.mem{pre_cond h0 output_b input_b key keys_b /\ B.length stack_b == (if is_win then 256 else 96) /\ live h0 stack_b /\ buf_disjoint_from stack_b [output_b;input_b;keys_b]}) : GTot va_state =
  let taint_func (x:b8) : GTot taint =
    if StrongExcludedMiddle.strong_excluded_middle (x == output_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == input_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == keys_b) then Secret else
    Public in
  let buffers = create_buffer_list output_b input_b keys_b stack_b in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_output_b = addrs output_b in
  let addr_input_b = addrs input_b in
  let addr_keys_b = addrs keys_b in
  let addr_stack:nat64 = addrs stack_b + (if is_win then 224 else 64) in
  let regs = if is_win then (
    fun r -> begin match r with
    | Rsp -> addr_stack
    | Rcx -> addr_output_b
    | Rdx -> addr_input_b
    | R8 -> addr_keys_b
    | _ -> init_regs r end)
  else (
    fun r -> begin match r with
    | Rsp -> addr_stack
    | Rdi -> addr_output_b
    | Rsi -> addr_input_b
    | Rdx -> addr_keys_b
    | _ -> init_regs r end)
  in let regs = X64.Vale.Regs.of_fun regs
  in let xmms = X64.Vale.Xmms.of_fun init_xmms in
  {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem;
      memTaint = create_valid_memtaint mem buffers taint_func}

let create_lemma is_win output_b input_b key keys_b stack_b (h0:HS.mem{pre_cond h0 output_b input_b key keys_b /\ B.length stack_b == (if is_win then 256 else 96) /\ live h0 stack_b /\ buf_disjoint_from stack_b [output_b;input_b;keys_b]}) : Lemma
  (create_initial_trusted_state is_win output_b input_b key keys_b stack_b h0 == state_to_S (create_initial_vale_state is_win output_b input_b key keys_b stack_b h0)) =
    let s_init = create_initial_trusted_state is_win output_b input_b key keys_b stack_b h0 in
    let s0 = create_initial_vale_state is_win output_b input_b key keys_b stack_b h0 in
    let s1 = state_to_S s0 in
    assert (FunctionalExtensionality.feq (regs' s1.TS.state) (regs' s_init.TS.state));
    assert (FunctionalExtensionality.feq (xmms' s1.TS.state) (xmms' s_init.TS.state))

let implies_pre (is_win:bool) (h0:HS.mem) (output_b:s8) (input_b:s8) (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:s8)  (stack_b:b8) : Lemma
  (requires pre_cond h0 output_b input_b key keys_b /\ B.length stack_b == (if is_win then 256 else 96) /\ live h0 stack_b /\ buf_disjoint_from stack_b [output_b;input_b;keys_b])
  (ensures (
B.length stack_b == (if is_win then 256 else 96) /\ live h0 stack_b /\ buf_disjoint_from stack_b [output_b;input_b;keys_b] /\ (
  let s0 = create_initial_vale_state is_win output_b input_b key keys_b stack_b h0 in
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) output_b;
  length_t_eq (TBase TUInt128) input_b;
  length_t_eq (TBase TUInt128) keys_b;
  va_pre (va_code_AESEncryptBlockStdcall is_win) s0 is_win stack_b output_b input_b (Ghost.reveal key) keys_b ))) =
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) output_b;
  length_t_eq (TBase TUInt128) input_b;
  length_t_eq (TBase TUInt128) keys_b;
  assert(Interop.disjoint stack_b output_b);
  assert(Interop.disjoint stack_b input_b);
  assert(Interop.disjoint stack_b keys_b);
  ()

let implies_post (is_win:bool) (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) (output_b:s8) (input_b:s8) (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:s8)  (stack_b:b8) : Lemma
  (requires pre_cond va_s0.mem.hs output_b input_b key keys_b /\ B.length stack_b == (if is_win then 256 else 96) /\ live va_s0.mem.hs stack_b /\ buf_disjoint_from stack_b [output_b;input_b;keys_b]/\
    va_post (va_code_AESEncryptBlockStdcall is_win) va_s0 va_sM va_fM is_win stack_b output_b input_b (Ghost.reveal key) keys_b )
  (ensures post_cond va_s0.mem.hs va_sM.mem.hs output_b input_b key keys_b ) =
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) output_b;
  length_t_eq (TBase TUInt128) input_b;
  length_t_eq (TBase TUInt128) keys_b;
  ()

#set-options "--max_fuel 0 --initial_ifuel 1 --max_ifuel 1"

let lemma_ghost_AESEncryptBlockStdcall is_win output_b input_b key keys_b stack_b h0 =
assume False; // TODO
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) output_b;
  length_t_eq (TBase TUInt128) input_b;
  length_t_eq (TBase TUInt128) keys_b;
  implies_pre is_win h0 output_b input_b key keys_b stack_b;
  let s0 = create_initial_trusted_state is_win output_b input_b key keys_b stack_b h0 in
  let s0' = create_initial_vale_state is_win output_b input_b key keys_b stack_b h0 in
  create_lemma is_win output_b input_b key keys_b stack_b h0;
  let s_v, f_v = va_lemma_AESEncryptBlockStdcall (va_code_AESEncryptBlockStdcall is_win) s0' is_win stack_b output_b input_b (Ghost.reveal key) keys_b in
  implies_post is_win s0' s_v f_v output_b input_b key keys_b stack_b;
  let s1 = Some?.v (TS.taint_eval_code (va_code_AESEncryptBlockStdcall is_win) f_v s0) in
  assert (state_eq_S s1 (state_to_S s_v));
  assert (FunctionalExtensionality.feq s1.TS.state.BS.regs (X64.Vale.Regs.to_fun s_v.regs));
  assert (FunctionalExtensionality.feq s1.TS.state.BS.xmms (X64.Vale.Xmms.to_fun s_v.xmms));
  assert (M.modifies (M.loc_union (M.loc_buffer stack_b) ( M.loc_buffer output_b)) h0 s_v.mem.hs);
  s1, f_v, s_v.mem.hs

#set-options "--max_fuel 0 --max_ifuel 0"

irreducible
let aes_encrypt_aux (output_b:b8) (input_b:b8) (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:b8) (stack_b:b8) : Stack unit
  (fun h ->  
    pre_cond h output_b input_b key keys_b /\ 
    B.length stack_b == (if win then 256 else 96) /\ 
    live h stack_b /\ 
    buf_disjoint_from stack_b [output_b;input_b;keys_b])
  (fun h0 _ h1 -> 
    post_cond h0 h1 output_b input_b key keys_b /\
    M.modifies (M.loc_union (M.loc_buffer stack_b) (M.loc_buffer output_b)) h0 h1) =
  if win then
  st_put
    (fun h -> pre_cond h output_b input_b key keys_b /\ B.length stack_b == 256 /\ live h stack_b /\ buf_disjoint_from stack_b [output_b;input_b;keys_b])
    (fun h -> let _, _, h1 =
      lemma_ghost_AESEncryptBlockStdcall true output_b input_b key keys_b stack_b h
    in (), h1)
  else st_put
    (fun h -> pre_cond h output_b input_b key keys_b /\ B.length stack_b == 96 /\ live h stack_b /\ buf_disjoint_from stack_b [output_b;input_b;keys_b])
    (fun h -> let _, _, h1 =
      lemma_ghost_AESEncryptBlockStdcall false output_b input_b key keys_b stack_b h
    in (), h1)    

let aes_EncryptBlockStdcall output_b input_b key keys_b  =
  push_frame();
  let (stack_b:b8) = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t (if win then 256 else 96)) in
  aes_encrypt_aux output_b input_b key keys_b stack_b;
  pop_frame()

