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
open Words.Seq_s
open Words.Seq
open Words.Four_s
open Arch.Types
open Collections.Seqs_s
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
friend SHA_helpers
#set-options "--z3rlimit 60"

open Vale_sha_update_bytes_stdcall

let pre_cond8 (h:HS.mem) (ctx_b:b8) (in_b:b8) (num_val:nat64) (k_b:b8) = 
  live h ctx_b /\ live h in_b /\ live h k_b /\
  disjoint_or_eq ctx_b k_b /\ 
  disjoint_or_eq in_b k_b /\ 
  length k_b % 16 == 0 /\
  length k_b >= 256 /\
  length ctx_b == 32 /\
  length in_b == 64 `op_Multiply` num_val /\
  disjoint ctx_b in_b /\
  sha_enabled /\
  (let k_b128 = BV.mk_buffer_view k_b Views.view128 in
k_reqs (BV.as_seq h k_b128))

let post_cond8 (h:HS.mem) (h':HS.mem) (ctx_b:b8) (in_b:b8) (num_val:nat64) (k_b:b8) = 
  live h ctx_b /\ live h in_b /\ live h k_b /\
  live h' ctx_b /\ live h' in_b /\ live h' k_b /\
  length k_b % 16 == 0 /\
  length k_b >= 256 /\
  length ctx_b == 32 /\
  length ctx_b % 16 == 0 /\  // Why do we need this redundant requirement to satisfy BV.mk_buffer_view?
  length in_b == 64 `op_Multiply` num_val /\
  (let ctx_b128 = BV.mk_buffer_view ctx_b Views.view128 in
  let in_b128 = BV.mk_buffer_view in_b Views.view128 in
  let input_LE = seq_nat8_to_seq_uint8 (le_seq_quad32_to_bytes (BV.as_seq h' in_b128)) in
  let hash_in = le_bytes_to_hash (le_seq_quad32_to_bytes (BV.as_seq h ctx_b128)) in
  let hash_out = le_bytes_to_hash (le_seq_quad32_to_bytes (BV.as_seq h' ctx_b128)) in
  (Seq.length input_LE) % 64 = 0 /\
  hash_out == update_multi_transparent hash_in input_LE
)

#set-options "--initial_fuel 6 --max_fuel 6 --initial_ifuel 0 --max_ifuel 0"
let create_buffer_list (ctx_b:b8) (in_b:b8) (k_b:b8) (stack_b:b8)  : (l:list b8{
    l == [stack_b;ctx_b;in_b;k_b] /\
  (forall x. {:pattern List.memP x l} List.memP x l <==> (x == ctx_b \/ x == in_b \/ x == k_b \/ x == stack_b))}) =
  [stack_b;ctx_b;in_b;k_b]

#set-options "--max_fuel 0 --max_ifuel 0"

let create_initial_trusted_state is_win ctx_b in_b num_val k_b stack_b (h0:HS.mem{pre_cond8 h0 ctx_b in_b num_val k_b /\ B.length stack_b == (if is_win then 264 else 104) /\ live h0 stack_b /\ buf_disjoint_from stack_b [ctx_b;in_b;k_b]}) : GTot TS.traceState =
  let taint_func (x:b8) : GTot taint =
    if StrongExcludedMiddle.strong_excluded_middle (x == ctx_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == in_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == k_b) then Secret else
    Public in
  let buffers = create_buffer_list ctx_b in_b k_b stack_b in
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
  in let regs = FunctionalExtensionality.on reg regs
  in let xmms = FunctionalExtensionality.on xmm init_xmms in
  let (s0:BS.state) = {BS.ok = true; BS.regs = regs; BS.xmms = xmms; BS.flags = 0;
       BS.mem = Interop.down_mem h0 addrs buffers} in
  {TS.state = s0; TS.trace = []; TS.memTaint = create_valid_memtaint mem buffers taint_func}

val lemma_ghost_sha_update_bytes_stdcall: is_win:bool -> ctx_b:b8 -> in_b:b8 -> num_val:nat64 -> k_b:b8 ->  stack_b:b8 -> (h0:HS.mem{pre_cond8 h0 ctx_b in_b num_val k_b /\ B.length stack_b == (if is_win then 264 else 104) /\ live h0 stack_b /\ buf_disjoint_from stack_b [ctx_b;in_b;k_b]}) ->
  Ghost (TS.traceState * nat * HS.mem)
    (requires True)
    (ensures (fun (s1, f1, h1) ->
      (let s0 = create_initial_trusted_state is_win ctx_b in_b num_val k_b stack_b h0 in
      Some s1 == TS.taint_eval_code (va_code_sha_update_bytes_stdcall is_win) f1 s0 /\
      Interop.correct_down h1 addrs [stack_b;ctx_b;in_b;k_b] s1.TS.state.BS.mem /\
      post_cond8 h0 h1 ctx_b in_b num_val k_b  /\
      calling_conventions is_win s0 s1 /\
      M.modifies (M.loc_union (M.loc_buffer stack_b) ( M.loc_buffer ctx_b)) h0 h1)
    ))

// ===============================================================================================
//  Everything below this line is untrusted

let create_initial_vale_state is_win ctx_b in_b num_val k_b stack_b (h0:HS.mem{pre_cond8 h0 ctx_b in_b num_val k_b /\ B.length stack_b == (if is_win then 264 else 104) /\ live h0 stack_b /\ buf_disjoint_from stack_b [ctx_b;in_b;k_b]}) : GTot va_state =
  let taint_func (x:b8) : GTot taint =
    if StrongExcludedMiddle.strong_excluded_middle (x == ctx_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == in_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == k_b) then Secret else
    Public in
  let buffers = create_buffer_list ctx_b in_b k_b stack_b in
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
  in let regs = X64.Vale.Regs.of_fun regs
  in let xmms = X64.Vale.Xmms.of_fun init_xmms in
  {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem;
      memTaint = create_valid_memtaint mem buffers taint_func}

let create_lemma is_win ctx_b in_b num_val k_b stack_b (h0:HS.mem{pre_cond8 h0 ctx_b in_b num_val k_b /\ B.length stack_b == (if is_win then 264 else 104) /\ live h0 stack_b /\ buf_disjoint_from stack_b [ctx_b;in_b;k_b]}) : Lemma
  (create_initial_trusted_state is_win ctx_b in_b num_val k_b stack_b h0 == state_to_S (create_initial_vale_state is_win ctx_b in_b num_val k_b stack_b h0)) =
    let s_init = create_initial_trusted_state is_win ctx_b in_b num_val k_b stack_b h0 in
    let s0 = create_initial_vale_state is_win ctx_b in_b num_val k_b stack_b h0 in
    let s1 = state_to_S s0 in
    assert (FunctionalExtensionality.feq (regs' s1.TS.state) (regs' s_init.TS.state));
    assert (FunctionalExtensionality.feq (xmms' s1.TS.state) (xmms' s_init.TS.state))

let implies_pre_aux (b:b8) (n:nat64) : Lemma
  (requires length b == 64 `op_Multiply` n)
  (ensures buffer_length #(X64.Memory.TBase X64.Memory.TUInt128) b == 4 `op_Multiply` n) = 
length_t_eq (TBase TUInt128) b

let implies_pre (is_win:bool) (h0:HS.mem) (ctx_b:b8) (in_b:b8) (num_val:nat64) (k_b:b8)  (stack_b:b8) : Lemma
  (requires pre_cond8 h0 ctx_b in_b num_val k_b /\ B.length stack_b == (if is_win then 264 else 104) /\ live h0 stack_b /\ buf_disjoint_from stack_b [ctx_b;in_b;k_b])
  (ensures (
B.length stack_b == (if is_win then 264 else 104) /\ live h0 stack_b /\ buf_disjoint_from stack_b [ctx_b;in_b;k_b] /\ (
  let s0 = create_initial_vale_state is_win ctx_b in_b num_val k_b stack_b h0 in
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) ctx_b;
  length_t_eq (TBase TUInt128) in_b;
  length_t_eq (TBase TUInt128) k_b;
  va_pre (va_code_sha_update_bytes_stdcall is_win) s0 is_win stack_b ctx_b in_b num_val k_b ))) =
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) ctx_b;
  length_t_eq (TBase TUInt128) in_b;
  length_t_eq (TBase TUInt128) k_b;
  assert(Interop.disjoint stack_b ctx_b);
  assert(Interop.disjoint stack_b in_b);
  assert(Interop.disjoint stack_b k_b);
  let s0 = create_initial_vale_state is_win ctx_b in_b num_val k_b stack_b h0 in  
  let k_b128 = BV.mk_buffer_view k_b Views.view128 in
  let t = TBase TUInt128 in
  implies_pre_aux in_b num_val;
  assert (Seq.equal
    (buffer_as_seq #t s0.mem k_b)
    (BV.as_seq h0 k_b128));  
  ()

let implies_post (is_win:bool) (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) (ctx_b:b8) (in_b:b8) (num_val:nat64) (k_b:b8)  (stack_b:b8) : Lemma
  (requires pre_cond8 va_s0.mem.hs ctx_b in_b num_val k_b /\ B.length stack_b == (if is_win then 264 else 104) /\ live va_s0.mem.hs stack_b /\ buf_disjoint_from stack_b [ctx_b;in_b;k_b]/\
    va_post (va_code_sha_update_bytes_stdcall is_win) va_s0 va_sM va_fM is_win stack_b ctx_b in_b num_val k_b )
  (ensures post_cond8 va_s0.mem.hs va_sM.mem.hs ctx_b in_b num_val k_b ) =
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) ctx_b;
  length_t_eq (TBase TUInt128) in_b;
  length_t_eq (TBase TUInt128) k_b;
  let ctx_b128 = BV.mk_buffer_view ctx_b Views.view128 in
  let in_b128 = BV.mk_buffer_view in_b Views.view128 in
  let t = TBase TUInt128 in  
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

#set-options "--max_fuel 0 --initial_ifuel 1 --max_ifuel 1"

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
  assert (FunctionalExtensionality.feq s1.TS.state.BS.regs (X64.Vale.Regs.to_fun s_v.regs));
  assert (FunctionalExtensionality.feq s1.TS.state.BS.xmms (X64.Vale.Xmms.to_fun s_v.xmms));
  assert (M.modifies (M.loc_union (M.loc_buffer stack_b) ( M.loc_buffer ctx_b)) h0 s_v.mem.hs);
  (s1, f_v, s_v.mem.hs)

#set-options "--max_fuel 0 --max_ifuel 0"
(*
let nat32_to_nat8s (v:UInt32.t) : GTot (s:Seq.lseq UInt8.t 4{
  v == UInt32.uint_to_t (Views_s.nat8s_to_nat32
    (UInt8.v (Seq.index s 0))
    (UInt8.v (Seq.index s 1))
    (UInt8.v (Seq.index s 2))
    (UInt8.v (Seq.index s 3)))}) =
  Views.put32_def v

let seq32_to_8 (s:Seq.seq UInt32.t) : GTot (s':Seq.seq UInt8.t{
  Seq.length s' = 4 `op_Multiply` Seq.length s /\
  (forall (i:nat{i < Seq.length s}). 
  Seq.index s i == UInt32.uint_to_t (Views_s.nat8s_to_nat32
    (UInt8.v (Seq.index s' (4 `op_Multiply` i)))
    (UInt8.v (Seq.index s' (4 `op_Multiply` i + 1)))
    (UInt8.v (Seq.index s' (4 `op_Multiply` i + 2)))
    (UInt8.v (Seq.index s' (4 `op_Multiply` i + 3)))
    ))}) =
  let n = Seq.length s in
  let rec aux (i:nat{i <= n}) : GTot (s':Seq.lseq UInt8.t (4 `op_Multiply` (n - i)){
    (forall (j:nat{j < n - i}). 
    Seq.index s (i + j) == UInt32.uint_to_t (Views_s.nat8s_to_nat32
    (UInt8.v (Seq.index s' (4 `op_Multiply` j)))
    (UInt8.v (Seq.index s' (4 `op_Multiply` j + 1)))
    (UInt8.v (Seq.index s' (4 `op_Multiply` j + 2)))
    (UInt8.v (Seq.index s' (4 `op_Multiply` j + 3)))
    ))}) 
    (decreases %[n - i]) =
    if i = Seq.length s then Seq.empty
    else begin
      let s_aux = aux (i+1) in
      let s' = Seq.append (nat32_to_nat8s (Seq.index s i)) s_aux in
      let aux2 (j:nat{j < n-i /\ j > 0}) : Lemma (
        Seq.index s (i + j) == UInt32.uint_to_t (Views_s.nat8s_to_nat32
          (UInt8.v (Seq.index s' (4 `op_Multiply` j)))
          (UInt8.v (Seq.index s' (4 `op_Multiply` j + 1)))
          (UInt8.v (Seq.index s' (4 `op_Multiply` j + 2)))
          (UInt8.v (Seq.index s' (4 `op_Multiply` j + 3)))
        )) =
        assert (Seq.index s' (4 `op_Multiply` j) == Seq.index s_aux (4 `op_Multiply` (j-1)));
        assert (Seq.index s' (4 `op_Multiply` j + 1) == Seq.index s_aux (4 `op_Multiply` (j-1) + 1));
        assert (Seq.index s' (4 `op_Multiply` j + 2) == Seq.index s_aux (4 `op_Multiply` (j-1) + 2));
        assert (Seq.index s' (4 `op_Multiply` j + 3) == Seq.index s_aux (4 `op_Multiply` (j-1) + 3))
      in Classical.forall_intro aux2;
      s'
    end
  in aux 0
*)

let b32_to_b8 (b32:uint32_p) (b8:b8) (h0:HS.mem) : Ghost HS.mem
  (requires live h0 b32 /\ live h0 b8 /\ length b8 == 4 `op_Multiply` length b32 /\
    length b8 % 16 == 0 /\ M.loc_disjoint (M.loc_buffer b8) (M.loc_buffer b32))
  (ensures fun h1 ->
    M.modifies (M.loc_buffer b8) h0 h1 /\
    (let b128_8 = BV.mk_buffer_view b8 Views.view128 in
    let b128_32 = BV.mk_buffer_view b32 Views.view32_128 in
    BV.length_eq b128_8;
    BV.length_eq b128_32;
    BV.get_view_mk_buffer_view b8 Views.view128;
    BV.get_view_mk_buffer_view b32 Views.view32_128;
    BV.as_buffer_mk_buffer_view b8 Views.view128;
    BV.as_buffer_mk_buffer_view b32 Views.view32_128;
    BV.as_seq h1 b128_8 == BV.as_seq h0 b128_32)) =
  admit()
(*  
  let h1 = B.g_upd_seq b8 (seq32_to_8 (B.as_seq h0 b32)) h0 in
  B.g_upd_seq_as_seq b8 (seq32_to_8 (B.as_seq h0 b32)) h0;
  let b128_8 = BV.mk_buffer_view b8 Views.view128 in
  let b128_32 = BV.mk_buffer_view b32 Views.view32_128 in
  BV.length_eq b128_8;
  BV.length_eq b128_32;
  BV.get_view_mk_buffer_view b8 Views.view128;
  BV.get_view_mk_buffer_view b32 Views.view32_128;
  BV.as_buffer_mk_buffer_view b8 Views.view128;
  BV.as_buffer_mk_buffer_view b32 Views.view32_128;
  let s8 = BV.as_seq h1 b128_8 in
  let s32 = BV.as_seq h0 b128_32 in
  let aux (i:nat{i < Seq.length s8}) : Lemma
    (Seq.index s8 i == Seq.index s32 i) =
    BV.get_sel h1 b128_8 i;
    BV.as_seq_sel h1 b128_8 i;
    BV.get_sel h0 b128_32 i;
    BV.as_seq_sel h0 b128_32 i;
    Opaque_s.reveal_opaque Views.get128_def;
    Opaque_s.reveal_opaque Views.get32_128_def
  in Classical.forall_intro aux;
  assert (Seq.equal
    (BV.as_seq h1 b128_8)
    (BV.as_seq h0 b128_32));
  h1
*)

(*
let seq8_to_32 (s:Seq.seq UInt8.t{Seq.length s % 16 = 0}) : GTot (s':Seq.seq UInt32.t{
  Seq.length s == 4 `op_Multiply` Seq.length s' /\
  (forall (i:nat{i < Seq.length s'}).
    UInt32.v (Seq.index s' i) == Views_s.nat8s_to_nat32
      (UInt8.v (Seq.index s (4 `op_Multiply` i)))
      (UInt8.v (Seq.index s (4 `op_Multiply` i + 1)))
      (UInt8.v (Seq.index s (4 `op_Multiply` i + 2)))
      (UInt8.v (Seq.index s (4 `op_Multiply` i + 3))))}) =
  let n = Seq.length s `op_Division` 4 in
  let rec aux (i:nat{i <= n}) (accu:Seq.lseq UInt32.t i) : Ghost (Seq.lseq UInt32.t n)
    (requires
      (forall (j:nat{j < Seq.length accu}).
    UInt32.v (Seq.index accu j) == Views_s.nat8s_to_nat32
      (UInt8.v (Seq.index s (4 `op_Multiply` j)))
      (UInt8.v (Seq.index s (4 `op_Multiply` j + 1)))
      (UInt8.v (Seq.index s (4 `op_Multiply` j + 2)))
      (UInt8.v (Seq.index s (4 `op_Multiply` j + 3)))))
    (ensures fun s' ->
      (forall (j:nat{j < n}).
    UInt32.v (Seq.index s' j) == Views_s.nat8s_to_nat32
      (UInt8.v (Seq.index s (4 `op_Multiply` j)))
      (UInt8.v (Seq.index s (4 `op_Multiply` j + 1)))
      (UInt8.v (Seq.index s (4 `op_Multiply` j + 2)))
      (UInt8.v (Seq.index s (4 `op_Multiply` j + 3))))) 
    (decreases %[n-i]) =
    if i = n then accu else
    aux (i+1) (Seq.append 
      accu 
      (Seq.create 1 (UInt32.uint_to_t (Views_s.nat8s_to_nat32
        (UInt8.v (Seq.index s (4 `op_Multiply` i)))
        (UInt8.v (Seq.index s (4 `op_Multiply` i + 1)))
        (UInt8.v (Seq.index s (4 `op_Multiply` i + 2)))
        (UInt8.v (Seq.index s (4 `op_Multiply` i + 3)))))))
  in aux 0 Seq.empty
*)
let b8_to_b32 (b32:uint32_p) (b8:b8) (h0:HS.mem) : Ghost HS.mem
  (requires live h0 b32 /\ live h0 b8 /\ length b8 == 4 `op_Multiply` length b32 /\
    length b8 % 16 == 0 /\ M.loc_disjoint (M.loc_buffer b8) (M.loc_buffer b32))
  (ensures fun h1 ->
    M.modifies (M.loc_buffer b32) h0 h1 /\
    (let b128_8 = BV.mk_buffer_view b8 Views.view128 in
    let b128_32 = BV.mk_buffer_view b32 Views.view32_128 in
    BV.length_eq b128_8;
    BV.length_eq b128_32;
    BV.get_view_mk_buffer_view b8 Views.view128;
    BV.get_view_mk_buffer_view b32 Views.view32_128;
    BV.as_buffer_mk_buffer_view b8 Views.view128;
    BV.as_buffer_mk_buffer_view b32 Views.view32_128;
    BV.as_seq h0 b128_8 == BV.as_seq h1 b128_32)) =
  admit()
(*  
  let h1 = B.g_upd_seq b32 (seq8_to_32 (B.as_seq h0 b8)) h0 in
  B.g_upd_seq_as_seq b32 (seq8_to_32 (B.as_seq h0 b8)) h0;
  let b128_8 = BV.mk_buffer_view b8 Views.view128 in
  let b128_32 = BV.mk_buffer_view b32 Views.view32_128 in
  BV.length_eq b128_8;
  BV.length_eq b128_32;
  BV.get_view_mk_buffer_view b8 Views.view128;
  BV.get_view_mk_buffer_view b32 Views.view32_128;
  BV.as_buffer_mk_buffer_view b8 Views.view128;
  BV.as_buffer_mk_buffer_view b32 Views.view32_128;
  let s8 = BV.as_seq h0 b128_8 in
  let s32 = BV.as_seq h1 b128_32 in
  let aux (i:nat{i < Seq.length s8}) : Lemma
    (Seq.index s8 i == Seq.index s32 i) =
    BV.get_sel h0 b128_8 i;
    BV.as_seq_sel h0 b128_8 i;
    BV.get_sel h1 b128_32 i;
    BV.as_seq_sel h1 b128_32 i;
    Opaque_s.reveal_opaque Views.get128_def;
    Opaque_s.reveal_opaque Views.get32_128_def
  in Classical.forall_intro aux;
  assert (Seq.equal
    (BV.as_seq h0 b128_8)
    (BV.as_seq h1 b128_32));
  h1
*)

(* Lemmas to simplify the post condition and remove Vale-specific functions *)

let simplify_bytes_hash_aux (b:B.buffer UInt32.t) (h:HS.mem) : Lemma
  (requires B.live h b /\ B.length b % 4 == 0)
  (ensures (BV.length (BV.mk_buffer_view b Views.view32_128) == B.length b / 4))
  =
  BV.as_buffer_mk_buffer_view b Views.view32_128;
  BV.get_view_mk_buffer_view b Views.view32_128;
  BV.length_eq (BV.mk_buffer_view b Views.view32_128)

let simplify_bytes_hash_aux2 (b:B.buffer UInt32.t) (h:HS.mem) (i:nat{i < B.length b}) : Lemma
  (requires B.live h b /\ B.length b % 4 == 0)
  (ensures (let b128 = BV.mk_buffer_view b Views.view32_128 in
    let s = BV.as_seq h b128 in
    simplify_bytes_hash_aux b h;
    UInt32.uint_to_t (four_select (Seq.index s (i/4)) (i%4)) == Seq.index (B.as_seq h b) i)) =
  let b128 = BV.mk_buffer_view b Views.view32_128 in
  let s = BV.as_seq h b128 in
  simplify_bytes_hash_aux b h;
  let i' = i/4 in
  BV.as_seq_sel h b128 i';
  BV.get_sel h b128 i';
  assert (Seq.index s i' == 
     Views.get32_128 (Seq.slice (B.as_seq h b) (i' `op_Multiply` 4) (i' `op_Multiply` 4 + 4)));
  Opaque_s.reveal_opaque Views.get32_128_def

let simplify_bytes_hash (b:B.buffer UInt32.t) (h:HS.mem) : Lemma
  (requires B.live h b /\ B.length b == 8 /\ B.length b % 4 == 0)
  (ensures (
    let b128 = BV.mk_buffer_view b Views.view32_128 in
    le_bytes_to_hash (le_seq_quad32_to_bytes (BV.as_seq h b128)) == B.as_seq h b
  )) =
  let s_init = B.as_seq h b in
  let b128 = BV.mk_buffer_view b Views.view32_128 in
  let s = BV.as_seq h b128 in
  let s' = le_seq_quad32_to_bytes s in
  let s_f = le_bytes_to_hash s' in
  simplify_bytes_hash_aux b h;
  lemma_le_seq_quad32_to_bytes_length s;
  Opaque_s.reveal_opaque le_seq_quad32_to_bytes_def;
  let s_map = seq_map UInt32.uint_to_t (seq_four_to_seq_LE s) in
  assert (Seq.equal s_f s_map);
  let aux (i:nat{i < Seq.length s_map}) : Lemma (Seq.index s_map i == Seq.index s_init i) = 
    assert (Seq.index s_map i = UInt32.uint_to_t (four_select (Seq.index s (i / 4)) (i % 4)));
    simplify_bytes_hash_aux2 b h i
  in Classical.forall_intro aux;
  assert (Seq.equal s_map s_init)

let simplify_quad_aux (b:B.buffer UInt8.t) (h:HS.mem) : Lemma
  (requires B.live h b /\ B.length b % 16 == 0)
  (ensures (BV.length (BV.mk_buffer_view b Views.view128) == B.length b / 16))
  =
  BV.as_buffer_mk_buffer_view b Views.view128;
  BV.get_view_mk_buffer_view b Views.view128;
  BV.length_eq (BV.mk_buffer_view b Views.view128)

#reset-options "--z3rlimit 60"
let simplify_quad_bytes (b:B.buffer UInt8.t) (h:HS.mem) : Lemma
  (requires B.length b % 16 == 0 /\ B.live h b)
  (ensures (let b128 = BV.mk_buffer_view b Views.view128 in
    seq_nat8_to_seq_uint8 (le_seq_quad32_to_bytes (BV.as_seq h b128)) == B.as_seq h b)) =
  let s_init = B.as_seq h b in
  let b128 = BV.mk_buffer_view b Views.view128 in
  let s = BV.as_seq h b128 in
  let s' = le_seq_quad32_to_bytes s in
  Opaque_s.reveal_opaque le_seq_quad32_to_bytes_def;
  assert (s' == seq_four_to_seq_LE (seq_map (nat_to_four 8) (seq_four_to_seq_LE s)));
  let s_f = seq_nat8_to_seq_uint8 s' in
  simplify_quad_aux b h;
  lemma_le_seq_quad32_to_bytes_length s;
  let aux (i:nat{i < Seq.length s_f}) : Lemma (Seq.index s_init i == Seq.index s_f i) = 
    let i' = i/16 in
    BV.as_seq_sel h b128 i';
    BV.get_sel h b128 i'; 
    assert (Seq.index s i' == Views.get128 (Seq.slice s_init (i' `op_Multiply` 16) (i' `op_Multiply` 16 + 16)));
    Opaque_s.reveal_opaque Views.get128_def;
    let s_slice = seq_uint8_to_seq_nat8 (Seq.slice s_init (i' `op_Multiply` 16) (i' `op_Multiply` 16 +16)) in
    Opaque_s.reveal_opaque le_bytes_to_quad32_def;
    le_quad32_to_bytes_to_quad32 s_slice
  in Classical.forall_intro aux;
  assert (Seq.equal s_f s_init)

let post_cond8_post_cond (h h' h0 h1:HS.mem)(ctx_b:uint32_p) (in_b:b8) (num_val:UInt64.t) (k_b:uint32_p) (ctx_b8:b8) (k_b8:b8) (stack_b:b8) : Lemma
  (requires 
    pre_cond h ctx_b in_b num_val k_b /\
    post_cond8 h0 h1 ctx_b8 in_b (UInt64.v num_val) k_b8 /\
    M.modifies (M.loc_union (M.loc_buffer stack_b) (M.loc_buffer ctx_b8)) h0 h1 /\
    M.modifies (M.loc_union (M.loc_buffer ctx_b8) (M.loc_buffer k_b8)) h h0 /\
    M.modifies (M.loc_buffer ctx_b) h1 h' /\
    (let ctx_b128 = BV.mk_buffer_view ctx_b Views.view32_128 in
    let ctx_b128_8 = BV.mk_buffer_view ctx_b8 Views.view128 in
    BV.length ctx_b128 == BV.length ctx_b128_8 /\
    BV.as_seq h ctx_b128 == BV.as_seq h0 ctx_b128_8 /\
    BV.as_seq h' ctx_b128 == BV.as_seq h1 ctx_b128_8)
    )
  (ensures post_cond h h' ctx_b in_b num_val k_b) =
  simplify_bytes_hash ctx_b h;
  simplify_bytes_hash ctx_b h';
  simplify_quad_bytes in_b h'

let ghost_sha_update
  (ctx_b:uint32_p) 
  (in_b:b8) 
  (num_val:UInt64.t) 
  (k_b:uint32_p)
  (stack_b:b8)
  (ctx_b8:b8)
  (k_b8:b8)
  (h0:HS.mem{
    pre_cond h0 ctx_b in_b num_val k_b /\ 
    B.length stack_b == (if win then 264 else 104) /\ 
    live h0 stack_b /\ 
    M.loc_disjoint (M.loc_buffer stack_b) (M.loc_buffer ctx_b) /\
    M.loc_disjoint (M.loc_buffer stack_b) (M.loc_buffer in_b) /\
    M.loc_disjoint (M.loc_buffer stack_b) (M.loc_buffer k_b) /\
    B.length ctx_b8 == 4 `op_Multiply` B.length ctx_b /\
    B.length k_b8 == 4 `op_Multiply` B.length k_b /\
    live h0 k_b8 /\
    live h0 ctx_b8 /\
    M.loc_disjoint (M.loc_buffer ctx_b8) (M.loc_buffer ctx_b) /\
    M.loc_disjoint (M.loc_buffer ctx_b8) (M.loc_buffer in_b) /\
    M.loc_disjoint (M.loc_buffer ctx_b8) (M.loc_buffer k_b) /\
    M.loc_disjoint (M.loc_buffer ctx_b8) (M.loc_buffer stack_b) /\
    M.loc_disjoint (M.loc_buffer ctx_b8) (M.loc_buffer k_b8) /\
    M.loc_disjoint (M.loc_buffer k_b8) (M.loc_buffer ctx_b) /\    
    M.loc_disjoint (M.loc_buffer k_b8) (M.loc_buffer in_b) /\    
    M.loc_disjoint (M.loc_buffer k_b8) (M.loc_buffer k_b) /\    
    M.loc_disjoint (M.loc_buffer k_b8) (M.loc_buffer stack_b)
  })
  : GTot (h1:HS.mem{
    post_cond h0 h1 ctx_b in_b num_val k_b /\
    M.modifies (M.loc_union
      (M.loc_union (M.loc_buffer stack_b) (M.loc_buffer ctx_b8))
      (M.loc_union (M.loc_buffer ctx_b) (M.loc_buffer k_b8))) h0 h1}) =
  let h_init = h0 in
  let h0 = b32_to_b8 ctx_b ctx_b8 h0 in
  let h0 = b32_to_b8 k_b k_b8 h0 in
  let in_b128 = BV.mk_buffer_view in_b Views.view128 in
  let ctx_b128 = BV.mk_buffer_view ctx_b Views.view32_128 in
  let ctx_b128_8 = BV.mk_buffer_view ctx_b8 Views.view128 in  
  let num_val = UInt64.v num_val in
  let _, _, h1 = lemma_ghost_sha_update_bytes_stdcall win ctx_b8 in_b num_val k_b8 stack_b h0 in
  let h_f = b8_to_b32 ctx_b ctx_b8 h1 in
  post_cond8_post_cond h_init h_f h0 h1 ctx_b in_b (UInt64.uint_to_t num_val) k_b ctx_b8 k_b8 stack_b;
  h_f

let sha_update_bytes_stdcall_aux 
  (ctx_b:uint32_p)
  (in_b:b8)
  (num_val:UInt64.t)
  (k_b:uint32_p)
  (stack_b:b8)
  (ctx_b8:b8)
  (k_b8:b8) :
  Stack unit
  (requires fun h0 ->
    pre_cond h0 ctx_b in_b num_val k_b /\ 
    B.length stack_b == (if win then 264 else 104) /\ 
    live h0 stack_b /\ 
    M.loc_disjoint (M.loc_buffer stack_b) (M.loc_buffer ctx_b) /\
    M.loc_disjoint (M.loc_buffer stack_b) (M.loc_buffer in_b) /\
    M.loc_disjoint (M.loc_buffer stack_b) (M.loc_buffer k_b) /\
    B.length ctx_b8 == 4 `op_Multiply` B.length ctx_b /\
    B.length k_b8 == 4 `op_Multiply` B.length k_b /\
    live h0 k_b8 /\
    live h0 ctx_b8 /\
    M.loc_disjoint (M.loc_buffer ctx_b8) (M.loc_buffer ctx_b) /\
    M.loc_disjoint (M.loc_buffer ctx_b8) (M.loc_buffer in_b) /\
    M.loc_disjoint (M.loc_buffer ctx_b8) (M.loc_buffer k_b) /\
    M.loc_disjoint (M.loc_buffer ctx_b8) (M.loc_buffer stack_b) /\
    M.loc_disjoint (M.loc_buffer ctx_b8) (M.loc_buffer k_b8) /\
    M.loc_disjoint (M.loc_buffer k_b8) (M.loc_buffer ctx_b) /\    
    M.loc_disjoint (M.loc_buffer k_b8) (M.loc_buffer in_b) /\    
    M.loc_disjoint (M.loc_buffer k_b8) (M.loc_buffer k_b) /\    
    M.loc_disjoint (M.loc_buffer k_b8) (M.loc_buffer stack_b))
  (ensures fun h0 _ h1 ->
    post_cond h0 h1 ctx_b in_b num_val k_b /\
    M.modifies (M.loc_union
      (M.loc_union (M.loc_buffer stack_b) (M.loc_buffer ctx_b8))
      (M.loc_union (M.loc_buffer ctx_b) (M.loc_buffer k_b8))) h0 h1
  ) =
  st_put
    (fun h0 ->   
    pre_cond h0 ctx_b in_b num_val k_b /\ 
    B.length stack_b == (if win then 264 else 104) /\ 
    live h0 stack_b /\ 
    M.loc_disjoint (M.loc_buffer stack_b) (M.loc_buffer ctx_b) /\
    M.loc_disjoint (M.loc_buffer stack_b) (M.loc_buffer in_b) /\
    M.loc_disjoint (M.loc_buffer stack_b) (M.loc_buffer k_b) /\
    B.length ctx_b8 == 4 `op_Multiply` B.length ctx_b /\
    B.length k_b8 == 4 `op_Multiply` B.length k_b /\
    live h0 k_b8 /\
    live h0 ctx_b8 /\
    M.loc_disjoint (M.loc_buffer ctx_b8) (M.loc_buffer ctx_b) /\
    M.loc_disjoint (M.loc_buffer ctx_b8) (M.loc_buffer in_b) /\
    M.loc_disjoint (M.loc_buffer ctx_b8) (M.loc_buffer k_b) /\
    M.loc_disjoint (M.loc_buffer ctx_b8) (M.loc_buffer stack_b) /\
    M.loc_disjoint (M.loc_buffer ctx_b8) (M.loc_buffer k_b8) /\
    M.loc_disjoint (M.loc_buffer k_b8) (M.loc_buffer ctx_b) /\    
    M.loc_disjoint (M.loc_buffer k_b8) (M.loc_buffer in_b) /\    
    M.loc_disjoint (M.loc_buffer k_b8) (M.loc_buffer k_b) /\    
    M.loc_disjoint (M.loc_buffer k_b8) (M.loc_buffer stack_b))
    (fun h -> let h1 = ghost_sha_update ctx_b in_b num_val k_b stack_b ctx_b8 k_b8 h in (), h1)

#reset-options "--z3rlimit 120 --z3refresh"
let sha256_update ctx_b in_b num_val k_b =
  push_frame();
  let (stack_b:b8) = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t (if win then 264 else 104)) in
  let (ctx_b8:b8) = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 32) in
  let (k_b8:b8) = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 256) in
  let h0:HS.mem = HyperStack.ST.get() in
  sha_update_bytes_stdcall_aux ctx_b in_b num_val k_b stack_b ctx_b8 k_b8;
  pop_frame();
  admit()
