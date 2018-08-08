module Gcm_load_xor_win

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

open Vale_gcm_load_xor_store_buffer_win

#set-options "--initial_fuel 6 --max_fuel 6 --initial_ifuel 2 --max_ifuel 2"
let implies_pre (h0:HS.mem) (plain_b:s8) (mask_b:s8) (cipher_b:s8) (offset:nat64) (num_blocks:Ghost.erased (nat64)) (key:Ghost.erased (aes_key_LE AES_128)) (iv:Ghost.erased (quad32))  (stack_b:b8) : Lemma
  (requires pre_cond h0 plain_b mask_b cipher_b offset num_blocks key iv /\ B.length stack_b == 40 /\ live h0 stack_b /\ buf_disjoint_from stack_b [plain_b;mask_b;cipher_b])
  (ensures (
B.length stack_b == 40 /\ live h0 stack_b /\ buf_disjoint_from stack_b [plain_b;mask_b;cipher_b] /\ (  let taint_func (x:b8) : GTot taint =
    if StrongExcludedMiddle.strong_excluded_middle (x == plain_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == mask_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == cipher_b) then Secret else
    Public in
  let buffers = stack_b::plain_b::mask_b::cipher_b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_plain_b = addrs plain_b in
  let addr_mask_b = addrs mask_b in
  let addr_cipher_b = addrs cipher_b in
  let addr_stack:nat64 = addrs stack_b + 0 in
  let regs = fun r -> begin match r with
    | Rsp -> addr_stack
    | Rcx -> addr_plain_b
    | Rdx -> addr_mask_b
    | R8 -> addr_cipher_b
    | R9 -> offset
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem; memTaint = create_valid_memtaint mem buffers taint_func} in
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) plain_b;
  length_t_eq (TBase TUInt128) mask_b;
  length_t_eq (TBase TUInt128) cipher_b;
  va_pre (va_code_gcm_load_xor_store_buffer_win ()) s0 stack_b plain_b mask_b cipher_b offset (Ghost.reveal num_blocks) (Ghost.reveal key) (Ghost.reveal iv) ))) =
  let taint_func (x:b8) : GTot taint =
    if StrongExcludedMiddle.strong_excluded_middle (x == plain_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == mask_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == cipher_b) then Secret else
    Public in
  let buffers = stack_b::plain_b::mask_b::cipher_b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_plain_b = addrs plain_b in
  let addr_mask_b = addrs mask_b in
  let addr_cipher_b = addrs cipher_b in
  let addr_stack:nat64 = addrs stack_b + 0 in
  let regs = fun r -> begin match r with
    | Rsp -> addr_stack
    | Rcx -> addr_plain_b
    | Rdx -> addr_mask_b
    | R8 -> addr_cipher_b
    | R9 -> offset
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let va_s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem; memTaint = create_valid_memtaint mem buffers taint_func} in
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) plain_b;
  length_t_eq (TBase TUInt128) mask_b;
  length_t_eq (TBase TUInt128) cipher_b;
  assert (Seq.equal
    (buffer128_as_seq (va_get_mem va_s0) plain_b)
    (buffer_to_seq_quad32 plain_b va_s0.mem.hs));
  assert (Seq.equal
    (buffer128_as_seq (va_get_mem va_s0) cipher_b)
    (buffer_to_seq_quad32 cipher_b va_s0.mem.hs));
  let mask128 = BV.mk_buffer_view mask_b Views.view128 in
  assert (Seq.equal (buffer_as_seq (va_get_mem va_s0) mask_b) (BV.as_seq va_s0.mem.hs mask128));
  BV.as_seq_sel h0 mask128 0;
  ()

let implies_post (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) (plain_b:s8) (mask_b:s8) (cipher_b:s8) (offset:nat64) (num_blocks:Ghost.erased (nat64)) (key:Ghost.erased (aes_key_LE AES_128)) (iv:Ghost.erased (quad32))  (stack_b:b8) : Lemma
  (requires pre_cond va_s0.mem.hs plain_b mask_b cipher_b offset num_blocks key iv /\ B.length stack_b == 40 /\ live va_s0.mem.hs stack_b /\ buf_disjoint_from stack_b [plain_b;mask_b;cipher_b]/\
    va_post (va_code_gcm_load_xor_store_buffer_win ()) va_s0 va_sM va_fM stack_b plain_b mask_b cipher_b offset (Ghost.reveal num_blocks) (Ghost.reveal key) (Ghost.reveal iv) )
  (ensures post_cond va_s0.mem.hs va_sM.mem.hs plain_b mask_b cipher_b offset num_blocks key iv ) =
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

val ghost_gcm_load_xor_store_buffer_win: plain_b:s8 -> mask_b:s8 -> cipher_b:s8 -> offset:nat64 -> num_blocks:Ghost.erased (nat64) -> key:Ghost.erased (aes_key_LE AES_128) -> iv:Ghost.erased (quad32) ->  stack_b:b8 -> (h0:HS.mem{pre_cond h0 plain_b mask_b cipher_b offset num_blocks key iv /\ B.length stack_b == 40 /\ live h0 stack_b /\ buf_disjoint_from stack_b [plain_b;mask_b;cipher_b]}) -> GTot (h1:HS.mem{post_cond h0 h1 plain_b mask_b cipher_b offset num_blocks key iv })

let ghost_gcm_load_xor_store_buffer_win plain_b mask_b cipher_b offset num_blocks key iv stack_b h0 =
  let taint_func (x:b8) : GTot taint =
    if StrongExcludedMiddle.strong_excluded_middle (x == plain_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == mask_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == cipher_b) then Secret else
    Public in
  let buffers = stack_b::plain_b::mask_b::cipher_b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_plain_b = addrs plain_b in
  let addr_mask_b = addrs mask_b in
  let addr_cipher_b = addrs cipher_b in
  let addr_stack:nat64 = addrs stack_b + 0 in
  let regs = fun r -> begin match r with
    | Rsp -> addr_stack
    | Rcx -> addr_plain_b
    | Rdx -> addr_mask_b
    | R8 -> addr_cipher_b
    | R9 -> offset
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem; memTaint = create_valid_memtaint mem buffers taint_func} in
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) plain_b;
  length_t_eq (TBase TUInt128) mask_b;
  length_t_eq (TBase TUInt128) cipher_b;
  implies_pre h0 plain_b mask_b cipher_b offset num_blocks key iv stack_b ;
  let s1, f1 = va_lemma_gcm_load_xor_store_buffer_win (va_code_gcm_load_xor_store_buffer_win ()) s0 stack_b plain_b mask_b cipher_b offset (Ghost.reveal num_blocks) (Ghost.reveal key) (Ghost.reveal iv)  in
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
  // Ensures that va_code_gcm_load_xor_store_buffer_win is actually Vale code, and that s1 is the result of executing this code
  assert (va_ensure_total (va_code_gcm_load_xor_store_buffer_win ()) s0 s1 f1);
  implies_post s0 s1 f1 plain_b mask_b cipher_b offset num_blocks key iv stack_b ;
  s1.mem.hs

let gcm_load_xor_store_buffer_win plain_b mask_b cipher_b offset num_blocks key iv  =
  push_frame();
  let (stack_b:b8) = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 40) in
  st_put (fun h -> pre_cond h plain_b mask_b cipher_b (UInt64.v offset) num_blocks key iv /\ B.length stack_b == 40 /\ live h stack_b /\ buf_disjoint_from stack_b [plain_b;mask_b;cipher_b]) (ghost_gcm_load_xor_store_buffer_win plain_b mask_b cipher_b (UInt64.v offset) num_blocks key iv stack_b);
  pop_frame()
