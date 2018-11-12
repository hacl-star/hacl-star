module ModularInteropTest

module LB = LowStar.Buffer
module LBV = LowStar.BufferView
module LM = LowStar.Modifies
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module TS = X64.Taint_Semantics_s
module MS = X64.Memory_s
module M = X64.Memory
module BS = X64.Bytes_Semantics_s
module I = Interop
module IA = Interop_assumptions
module VS = X64.Vale.State
module V = X64.Vale.Decls
module X = Vale_memcpy
open FStar.Mul
open X64.Machine_s
open ModularInterop

let code : V.va_code = X.va_code_memcpy IA.win

let pre : vale_pre =
  fun
    (win:bool)
    (dst:M.buffer64)
    (src:M.buffer64)
    (va_s0:V.va_state)
    (stack_b:M.buffer64) -> X.va_pre code va_s0 win stack_b dst src

//TBD: Auto-gen, permute arguments
let post : vale_post =
  fun
    (win:bool)
    (dst:M.buffer64)
    (src:M.buffer64)
    (va_s0:V.va_state)
    (stack_b:M.buffer64)
    (va_sM:V.va_state)
    (va_fM:V.va_fuel) -> X.va_post code va_s0 va_sM va_fM win stack_b dst src

let pre_cond (h:HS.mem) (dst:b8) (src:b8) =
  LB.live h dst /\
  LB.live h src /\
  I.bufs_disjoint [dst; src] /\
  LB.length dst % 8 == 0 /\
  LB.length src % 8 == 0 /\
  LB.length dst == 16 /\
  LB.length src == 16

let post_cond (h:HS.mem) (h':HS.mem) (dst:b8) (src:b8) =
  LB.live h dst /\
  LB.live h src /\
  LB.live h' dst /\
  LB.live h' src /\
  LB.length dst % 8 == 0 /\
  LB.length src % 8 == 0 /\
  ( let dst_b = LBV.mk_buffer_view dst Views.view64 in
    let src_b = LBV.mk_buffer_view src Views.view64 in
    Seq.equal (LBV.as_seq h' dst_b) (LBV.as_seq h' src_b))

let full_post_cond (h:HS.mem) (h':HS.mem) (dst:b8) (src:b8)  =
  LB.modifies (LB.loc_union (LB.loc_buffer dst) (LB.loc_buffer src)) h h' /\ // REVIEW: maybe support more fine-grained modifies
  post_cond h h' dst src

let lem_memcpy (win:bool)
               (x0:M.buffer64)
               (x1:M.buffer64)
               (va_s0:V.va_state)
               (stack_b:M.buffer64)
  : Ghost (V.va_state & V.va_fuel)
      (requires (pre win x0 x1 va_s0 stack_b))
      (ensures (fun (va_s1, f) ->
        VS.eval_reg (register_of_arg_i win 0) va_s0 == M.buffer_addr x0 va_s0.VS.mem /\
        VS.eval_reg (register_of_arg_i win 1) va_s0 == M.buffer_addr x1 va_s0.VS.mem /\
        V.eval_code code va_s0 f va_s1 /\
        // TODO: saved registers
        V.modifies_mem (M.loc_union (M.loc_buffer x0) (M.loc_buffer x1)) va_s0.VS.mem va_s1.VS.mem /\
        post win x0 x1 va_s0 stack_b va_s1 f))
  =
  let (va_s1, f) = X.va_lemma_memcpy code va_s0 win stack_b x0 x1 in
  (va_s1, f)

let v:vale_sig code pre post = lem_memcpy

(*
open X64.Vale.Decls
open Test.Vale_memcpy
open X64.Memory
let assert_pre
    (x0 x1:M.buffer64)
    (hs_mem:HS.mem)
    (s0:V.va_state)
    (sb:stack_buffer)
  : Lemma
    (requires
      pre_cond hs_mem (to_b8 x0) (to_b8 x1) /\
      low_assumptions hs_mem s0.VS.mem x0 x1 /\
      s0.VS.ok /\
      M.buffer_readable s0.VS.mem x0 /\
      M.buffer_readable s0.VS.mem x1 /\
      M.buffer_length sb >= 3 /\
      M.locs_disjoint ([M.loc_buffer sb; M.loc_buffer x0; M.loc_buffer x1]) /\
      VS.eval_reg (register_of_arg_i IA.win 0) s0 == M.buffer_addr x0 s0.VS.mem /\
      VS.eval_reg (register_of_arg_i IA.win 1) s0 == M.buffer_addr x1 s0.VS.mem /\
      M.valid_taint_buf64 x0 s0.VS.mem s0.VS.memTaint Secret /\ // TODO: generalize this
      M.valid_taint_buf64 x1 s0.VS.mem s0.VS.memTaint Secret /\ // TODO: generalize this
      V.valid_stack_slots s0.VS.mem (VS.eval_reg Rsp s0) sb 3 s0.VS.memTaint
    )
    (ensures True)
  =
  let dst = x0 in
  let src = x1 in
  let va_s0 = s0 in
  let stack_b = sb in
  let win = IA.win in
  let va_b0 = code in
  assert (LB.live hs_mem (to_b8 x0));
  assert (LB.live hs_mem (to_b8 x1));

let t64 = M.TBase M.TUInt64 in

assert (va_require_total va_b0 (va_code_memcpy win) va_s0);
assert (va_get_ok va_s0);
assert (locs_disjoint ([loc_buffer #t64 stack_b; loc_buffer #t64 dst; loc_buffer #t64 src]));
assert (buffer_readable #t64 (va_get_mem va_s0) stack_b);
assert (buffer_readable #t64 (va_get_mem va_s0) dst);
assert (buffer_readable #t64 (va_get_mem va_s0) src);
assert (valid_taint_buf64 stack_b (va_get_mem va_s0) (va_get_memTaint va_s0) Public);
assert (valid_taint_buf64 dst (va_get_mem va_s0) (va_get_memTaint va_s0) Secret);
assert (valid_taint_buf64 src (va_get_mem va_s0) (va_get_memTaint va_s0) Secret);
assert (buffer_length #t64 src == 2);
assert (buffer_length #t64 src == 2);
assert (buffer_length #t64 dst == 2);
assert (buffer_length #t64 stack_b >= 3);
assert (valid_stack_slots (va_get_mem va_s0) (va_get_reg Rsp va_s0) stack_b 3 (va_get_memTaint va_s0));
assert (win ==> va_get_reg Rcx va_s0 == buffer_addr dst (va_get_mem va_s0));
assert (win ==> va_get_reg Rdx va_s0 == buffer_addr src (va_get_mem va_s0));
assert (~win ==> va_get_reg Rdi va_s0 == buffer_addr dst (va_get_mem va_s0));
assert (~win ==> va_get_reg Rsi va_s0 == buffer_addr src (va_get_mem va_s0));

  assert (Test.Vale_memcpy.va_req_memcpy code va_s0 win stack_b dst src);
  assert (X.va_pre code s0 IA.win sb dst src);
  assert (pre IA.win x0 x1 s0 sb);
  ()
*)

#reset-options "--z3rlimit 40"
let memcpy
    (dst:M.buffer64)
    (src:M.buffer64)
  : HST.Stack unit
      (requires (fun h -> pre_cond h (to_b8 dst) (to_b8 src)))
      (ensures (fun h0 _ h1 -> full_post_cond h0 h1 (to_b8 dst) (to_b8 src)))
  =
//  let x0 = dst in
//  let x1 = src in
//  let h0 = HST.get () in
//  assert (LB.loc_disjoint (LB.loc_buffer (to_b8 x0)) (LB.loc_buffer (to_b8 x1)));
//  assert (to_low_pre pre x0 x1 h0);
  wrap code pre post v dst src;
  ()

