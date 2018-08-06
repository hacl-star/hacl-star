module GCTR_win

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

open Vale_gctr_bytes_extra_buffer_win

#set-options "--initial_fuel 7 --max_fuel 7 --initial_ifuel 2 --max_ifuel 2"
let implies_pre (h0:HS.mem) (plain_b:s8) (num_bytes:nat64) (iv_old:Ghost.erased (quad32)) (iv_b:s8) (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:s8) (cipher_b:s8)  (stack_b:b8) : Lemma
  (requires pre_cond h0 plain_b num_bytes iv_old iv_b key keys_b cipher_b /\ B.length stack_b == 48 /\ live h0 stack_b /\ buf_disjoint_from stack_b [plain_b;iv_b;keys_b;cipher_b])
  (ensures (
B.length stack_b == 48 /\ live h0 stack_b /\ buf_disjoint_from stack_b [plain_b;iv_b;keys_b;cipher_b] /\ (  let taint_func (x:b8) : GTot taint =
    if StrongExcludedMiddle.strong_excluded_middle (x == plain_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == iv_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == keys_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == cipher_b) then Secret else
    Public in
  let buffers = stack_b::plain_b::iv_b::keys_b::cipher_b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_plain_b = addrs plain_b in
  let addr_iv_b = addrs iv_b in
  let addr_keys_b = addrs keys_b in
  let addr_cipher_b = addrs cipher_b in
  let addr_stack:nat64 = addrs stack_b + 0 in
  let regs = fun r -> begin match r with
    | Rsp -> addr_stack
    | Rcx -> addr_plain_b
    | Rdx -> num_bytes
    | R8 -> addr_iv_b
    | R9 -> addr_keys_b
    | _ -> init_regs r end in
  let mem = buffer_write #(TBase TUInt64) stack_b 5 (addrs cipher_b) mem in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem; memTaint = create_valid_memtaint mem buffers taint_func} in
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) plain_b;
  length_t_eq (TBase TUInt128) iv_b;
  length_t_eq (TBase TUInt128) keys_b;
  length_t_eq (TBase TUInt128) cipher_b;
  va_pre (va_code_gctr_bytes_extra_buffer_win ()) s0 stack_b plain_b num_bytes (Ghost.reveal iv_old) iv_b (Ghost.reveal key) keys_b cipher_b ))) =
  let taint_func (x:b8) : GTot taint =
    if StrongExcludedMiddle.strong_excluded_middle (x == plain_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == iv_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == keys_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == cipher_b) then Secret else
    Public in
  let buffers = stack_b::plain_b::iv_b::keys_b::cipher_b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_plain_b = addrs plain_b in
  let addr_iv_b = addrs iv_b in
  let addr_keys_b = addrs keys_b in
  let addr_cipher_b = addrs cipher_b in
  let addr_stack:nat64 = addrs stack_b + 0 in
  let regs = fun r -> begin match r with
    | Rsp -> addr_stack
    | Rcx -> addr_plain_b
    | Rdx -> num_bytes
    | R8 -> addr_iv_b
    | R9 -> addr_keys_b
    | _ -> init_regs r end in
  let mem = buffer_write #(TBase TUInt64) stack_b 5 (addrs cipher_b) mem in
  let xmms = init_xmms in
  let va_s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem; memTaint = create_valid_memtaint mem buffers taint_func} in
  assert (B.disjoint stack_b plain_b);
  assert (B.disjoint stack_b iv_b);
  assert (B.disjoint stack_b keys_b);
  assert (B.disjoint stack_b cipher_b);
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) plain_b;
  length_t_eq (TBase TUInt128) iv_b;
  length_t_eq (TBase TUInt128) keys_b;
  length_t_eq (TBase TUInt128) cipher_b;
  assert (Seq.equal (buffer_to_seq_quad32 cipher_b h0) (buffer128_as_seq (va_get_mem va_s0) cipher_b));
  assert (Seq.equal (buffer_to_seq_quad32 plain_b va_s0.mem.hs) (buffer128_as_seq (va_get_mem va_s0) plain_b));
  assert (Seq.equal (buffer_as_seq (va_get_mem va_s0) iv_b) (buffer128_as_seq (va_get_mem va_s0) iv_b));
  let iv128_b = BV.mk_buffer_view iv_b Views.view128 in
  assert (Seq.equal (buffer_as_seq (va_get_mem va_s0) iv_b) (BV.as_seq h0 iv128_b));
  BV.as_seq_sel h0 iv128_b 0;
  let keys128_b = BV.mk_buffer_view keys_b Views.view128 in
  assert (Seq.equal (buffer_as_seq (va_get_mem va_s0) keys_b) (BV.as_seq h0 keys128_b));
  ()

let implies_post (h0:HS.mem) (va_sM:va_state) (va_fM:va_fuel) (plain_b:s8) (num_bytes:nat64) (iv_old:Ghost.erased (quad32)) (iv_b:s8) (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:s8) (cipher_b:s8)  (stack_b:b8) : Lemma
  (requires pre_cond h0 plain_b num_bytes iv_old iv_b key keys_b cipher_b /\ B.length stack_b == 48 /\ live h0 stack_b /\ buf_disjoint_from stack_b [plain_b;iv_b;keys_b;cipher_b]/\
(  let taint_func (x:b8) : GTot taint =
    if StrongExcludedMiddle.strong_excluded_middle (x == plain_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == iv_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == keys_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == cipher_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == stack_b) then Public else
    Public in
  let buffers = stack_b::plain_b::iv_b::keys_b::cipher_b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_plain_b = addrs plain_b in
  let addr_iv_b = addrs iv_b in
  let addr_keys_b = addrs keys_b in
  let addr_cipher_b = addrs cipher_b in
  let addr_stack:nat64 = addrs stack_b + 0 in
  let regs = fun r -> begin match r with
    | Rsp -> addr_stack
    | Rcx -> addr_plain_b
    | Rdx -> num_bytes
    | R8 -> addr_iv_b
    | R9 -> addr_keys_b
    | _ -> init_regs r end in
  let mem = buffer_write #(TBase TUInt64) stack_b 5 (addrs cipher_b) mem in
  let xmms = init_xmms in
  let va_s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem; memTaint = create_valid_memtaint mem buffers taint_func} in
    va_post (va_code_gctr_bytes_extra_buffer_win ()) va_s0 va_sM va_fM stack_b plain_b num_bytes (Ghost.reveal iv_old) iv_b (Ghost.reveal key) keys_b cipher_b) )
  (ensures post_cond h0 va_sM.mem.hs plain_b num_bytes iv_old iv_b key keys_b cipher_b ) =
  let taint_func (x:b8) : GTot taint =
    if StrongExcludedMiddle.strong_excluded_middle (x == plain_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == iv_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == keys_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == cipher_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == stack_b) then Public else
    Public in
  let buffers = stack_b::plain_b::iv_b::keys_b::cipher_b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_plain_b = addrs plain_b in
  let addr_iv_b = addrs iv_b in
  let addr_keys_b = addrs keys_b in
  let addr_cipher_b = addrs cipher_b in
  let addr_stack:nat64 = addrs stack_b + 0 in
  let regs = fun r -> begin match r with
    | Rsp -> addr_stack
    | Rcx -> addr_plain_b
    | Rdx -> num_bytes
    | R8 -> addr_iv_b
    | R9 -> addr_keys_b
    | _ -> init_regs r end in
  let mem = buffer_write #(TBase TUInt64) stack_b 5 (addrs cipher_b) mem in
  let xmms = init_xmms in
  let va_s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem; memTaint = create_valid_memtaint mem buffers taint_func} in
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) plain_b;
  length_t_eq (TBase TUInt128) iv_b;
  length_t_eq (TBase TUInt128) keys_b;
  length_t_eq (TBase TUInt128) cipher_b;
  assert (Seq.equal (buffer_to_seq_quad32 cipher_b h0) (buffer128_as_seq (va_get_mem va_s0) cipher_b));
  assert (Seq.equal (buffer_to_seq_quad32 cipher_b va_sM.mem.hs) (buffer128_as_seq (va_get_mem va_sM) cipher_b));
  assert (Seq.equal (buffer_to_seq_quad32 plain_b h0) (buffer128_as_seq (va_get_mem va_s0) plain_b));
  ()

val ghost_gctr_bytes_extra_buffer_win: plain_b:s8 -> num_bytes:nat64 -> iv_old:Ghost.erased (quad32) -> iv_b:s8 -> key:Ghost.erased (aes_key_LE AES_128) -> keys_b:s8 -> cipher_b:s8 ->  stack_b:b8 -> (h0:HS.mem{pre_cond h0 plain_b num_bytes iv_old iv_b key keys_b cipher_b /\ B.length stack_b == 48 /\ live h0 stack_b /\ buf_disjoint_from stack_b [plain_b;iv_b;keys_b;cipher_b]}) -> GTot (h1:HS.mem{post_cond h0 h1 plain_b num_bytes iv_old iv_b key keys_b cipher_b  /\ M.modifies (M.loc_union (M.loc_buffer cipher_b) (M.loc_buffer stack_b)) h0 h1})

let ghost_gctr_bytes_extra_buffer_win plain_b num_bytes iv_old iv_b key keys_b cipher_b stack_b h0 =
  let taint_func (x:b8) : GTot taint =
    if StrongExcludedMiddle.strong_excluded_middle (x == plain_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == iv_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == keys_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == cipher_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == stack_b) then Public else
    Public in
  let buffers = stack_b::plain_b::iv_b::keys_b::cipher_b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_plain_b = addrs plain_b in
  let addr_iv_b = addrs iv_b in
  let addr_keys_b = addrs keys_b in
  let addr_cipher_b = addrs cipher_b in
  let addr_stack:nat64 = addrs stack_b + 0 in
  let regs = fun r -> begin match r with
    | Rsp -> addr_stack
    | Rcx -> addr_plain_b
    | Rdx -> num_bytes
    | R8 -> addr_iv_b
    | R9 -> addr_keys_b
    | _ -> init_regs r end in
  let mem = buffer_write #(TBase TUInt64) stack_b 5 (addrs cipher_b) mem in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem; memTaint = create_valid_memtaint mem buffers taint_func} in
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) plain_b;
  length_t_eq (TBase TUInt128) iv_b;
  length_t_eq (TBase TUInt128) keys_b;
  length_t_eq (TBase TUInt128) cipher_b;
  implies_pre h0 plain_b num_bytes iv_old iv_b key keys_b cipher_b stack_b ;
  let s1, f1 = va_lemma_gctr_bytes_extra_buffer_win (va_code_gctr_bytes_extra_buffer_win ()) s0 stack_b plain_b num_bytes (Ghost.reveal iv_old) iv_b (Ghost.reveal key) keys_b cipher_b  in
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
  // Ensures that va_code_gctr_bytes_extra_buffer_win is actually Vale code, and that s1 is the result of executing this code
  assert (va_ensure_total (va_code_gctr_bytes_extra_buffer_win ()) s0 s1 f1);
  implies_post h0 s1 f1 plain_b num_bytes iv_old iv_b key keys_b cipher_b stack_b ;
  s1.mem.hs

let gctr_bytes_extra_buffer_win plain_b num_bytes iv_old iv_b key keys_b cipher_b  =
  push_frame();
  let (stack_b:b8) = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 48) in
  st_put (fun h -> pre_cond h plain_b (UInt64.v num_bytes) iv_old iv_b key keys_b cipher_b /\ B.length stack_b == 48 /\ live h stack_b /\ buf_disjoint_from stack_b [plain_b;iv_b;keys_b;cipher_b]) (ghost_gctr_bytes_extra_buffer_win plain_b (UInt64.v num_bytes) iv_old iv_b key keys_b cipher_b stack_b);
  pop_frame()
