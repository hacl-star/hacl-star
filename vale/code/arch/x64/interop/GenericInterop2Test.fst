module GenericInterop2Test

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
open X64.Interop_s
open GenericInterop2
friend X64.Memory
module MM = X64.Memory
module IS = X64.Interop_s


open Vale_memcpy

let c : va_code = va_code_memcpy win

//TBD: Auto-generated for a specific vale arity
[@reduce]
unfold
let dom : l:list vale_type{List.Tot.length l < max_arity win} =
  let d = [VT_Buffer TUInt64; VT_Buffer TUInt64;] in
  assert_norm (List.Tot.length d < max_arity win);
  d

//TBD: Auto-gen, wrapper application
let memcpy_raw_s : IS.as_lowstar_sig (lower_code c) dom
    = IS.wrap (lower_code c) dom

//TBD: Auto-generated to permute arguments
let lem_memcpy (va_b0:va_code)
               (win:bool)
               (dst:buffer64)
               (src:buffer64)
               (va_s0:va_state)
               (stack_b:buffer64)
  : Ghost (va_state & va_fuel)
            (requires va_pre va_b0 va_s0 win stack_b dst src )
            (ensures (fun (va_sM, va_fM) ->
              X64.Vale.Decls.eval_code va_b0 va_s0 va_fM va_sM /\
              vale_calling_conventions win va_s0 va_sM /\
              va_post va_b0 va_s0 va_sM va_fM win stack_b dst src
            ))
  =
let (va_s1, f) = Vale_memcpy.va_lemma_memcpy va_b0 va_s0 win stack_b dst src in
(va_s1, f)

//TBD: Auto-gen, permute arguments
[@reduce]
let pre : vale_pre dom =
  fun (va_b0:va_code)
    (win:bool)
    (dst:buffer64)
    (src:buffer64)
    (va_s0:va_state)
    (stack_b:buffer64) -> va_pre va_b0 va_s0 win stack_b dst src

//TBD: Auto-gen, permute arguments
[@reduce]
let post : vale_post dom =
  fun (va_b0:va_code)
    (win:bool)
    (dst:buffer64)
    (src:buffer64)
    (va_s0:va_state)
    (stack_b:buffer64)
    (va_sM:va_state)
    (va_fM:va_fuel) -> va_post va_b0 va_s0 va_sM va_fM win stack_b dst src

//TBD: Auto-gen, wrapper application
let memcpy_wrapped : normal (as_lowstar_sig c dom pre post)
    = elim_lowstar_sig (wrap c [VT_Buffer TUInt64; VT_Buffer TUInt64;] pre post lem_memcpy memcpy_raw_s)

//TBD: Auto-gen, creation of initial state for a given arity (dom)
[@reduce]
unfold
let create_memcpy_initial_state
        (dst:buffer64)
        (src:buffer64)
        (h0:HS.mem)
        (stack:b8 {normal (mem_roots_p h0 [stack; to_b8 src; to_b8 dst])}) =
    elim_normal (mem_roots_p h0 [stack; to_b8 src; to_b8 dst]);
    normal
      (elim_down_nil [to_b8 src; to_b8 dst]
        (elim_down_cons _ _ [to_b8 dst]
          (elim_down_cons _ _ []
            (create_vale_initial_state win dom)
            dst)
        src)
        h0
        stack)

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 40"

//TBD: Auto-gen, from the definition of pre
[@reduce]
let lift_vale_pre
      (va_b0:va_code)
      (dst:buffer64)
      (src:buffer64)
      (h0:HS.mem) =
  let dst' = to_b8 dst in
  let src' = to_b8 src in
     disjoint_or_eq src' dst' /\
     live h0 src' /\
     live h0 dst' /\
     (elim_normal (disjoint_or_eq_l [src'; dst']);
      elim_normal (live_l h0 [src'; dst']);
      pre_in_prestate_ctx h0 [src'; dst'] (create_memcpy_initial_state dst src) (pre va_b0 win dst src))

//TBD: Auto-gen, from the definition of post
[@reduce]
let lift_vale_post
      (va_b0:va_code)
      (dst:buffer (TBase (TUInt64)))
      (src:buffer (TBase (TUInt64)))
      (h0:HS.mem)
      (h1:HS.mem) =
  let dst' = to_b8 dst in
  let src' = to_b8 src in
     disjoint_or_eq src' dst' /\
     live h0 src' /\
     live h0 dst' /\
     (elim_normal (disjoint_or_eq_l [src'; dst']);
      elim_normal (live_l h0 [src'; dst']);
      post_in_poststate_ctx
                    va_b0
                    h0
                    [src'; dst']
                    (create_memcpy_initial_state dst src)
                    (post va_b0 win dst src)
                    h1)

//TBD: Auto-gen, putting pieces together
val memcpy_wrapped_annot :
  _:unit ->
  dst:buffer (TBase (TUInt64)) ->
  src:buffer (TBase (TUInt64)) ->
  _:unit ->
  FStar.HyperStack.ST.Stack
    unit
    (requires (fun h0 -> normal (lift_vale_pre c dst src h0)))
    (ensures (fun h0 _ h1 -> normal (lift_vale_post c dst src h0 h1)))
let memcpy_wrapped_annot = memcpy_wrapped

////////////////////////////////////////////////////////////////////////////////
// MANUAL PROOF
////////////////////////////////////////////////////////////////////////////////
let pre_cond (h:HS.mem) (dst:b8) (src:b8) =
  live h dst /\
  live h src /\
  bufs_disjoint [dst;src] /\
  length dst % 8 == 0 /\
  length src % 8 == 0 /\
  length dst == 16 /\
  length src == 16

let post_cond (h:HS.mem) (h':HS.mem) (dst:b8) (src:b8) =
  live h dst /\
  live h src /\
  live h' dst /\
  live h' src /\
  length dst % 8 == 0 /\
  length src % 8 == 0 /\
  (let dst_b = BV.mk_buffer_view dst Views.view64 in
   let src_b = BV.mk_buffer_view src Views.view64 in
   Seq.equal (BV.as_seq h' dst_b) (BV.as_seq h' src_b))

let full_post_cond (h:HS.mem) (h':HS.mem) (dst:b8) (src:b8)  =
  post_cond h h' dst src  /\
  M.modifies (M.loc_buffer dst) h h'

open Test.Vale_memcpy

// TODO: Prove these two lemmas if they are not proven automatically
let implies_pre (dst:buffer64) (src:buffer64) (h0:HS.mem)  : Lemma
  (requires pre_cond h0 (to_b8 dst) (to_b8 src))
  (ensures (normal (lift_vale_pre (Vale_memcpy.va_code_memcpy win) dst src h0))) =
let va_b0 = c in
let dst' = to_b8 dst in
let src' = to_b8 src in
assert (disjoint_or_eq src' dst');
assert (live h0 src');
assert (live h0 dst');
elim_normal (disjoint_or_eq_l [src'; dst']); 
elim_normal (live_l h0 [src'; dst']); 
let f (push_h0:HS.mem) (alloc_push_h0:HS.mem) (b:stack_buffer)
  : Lemma
    (requires prestate_hyp h0 [src'; dst'] push_h0 alloc_push_h0 (to_b8 b))
    (ensures pre va_b0 win dst src (create_memcpy_initial_state dst src alloc_push_h0 (to_b8 b)) b) =
  let init = create_memcpy_initial_state dst src alloc_push_h0 (to_b8 b) in
  let va_s0 = init in
  let (stack_b:buffer64) = b in
  let t64 = MM.TBase MM.TUInt64 in

assert (va_require_total va_b0 (va_code_memcpy win) va_s0);
assert (va_get_ok va_s0);
assume (locs_disjoint ([loc_buffer #t64 stack_b; loc_buffer #t64 dst; loc_buffer #t64 src]));
assume (buffer_readable #t64 (va_get_mem va_s0) stack_b);
assume (buffer_readable #t64 (va_get_mem va_s0) dst);
assume (buffer_readable #t64 (va_get_mem va_s0) src);
assume (valid_taint_buf64 stack_b (va_get_mem va_s0) (va_get_memTaint va_s0) Public);
assume (valid_taint_buf64 dst (va_get_mem va_s0) (va_get_memTaint va_s0) Secret);
assume (valid_taint_buf64 src (va_get_mem va_s0) (va_get_memTaint va_s0) Secret);
assume (buffer_length #t64 src == 2);
assume (buffer_length #t64 src == 2);
assume (buffer_length #t64 dst == 2);
assume (buffer_length #t64 stack_b >= 3);
assume (valid_stack_slots (va_get_mem va_s0) (va_get_reg Rsp va_s0) stack_b 0 (va_get_memTaint va_s0));
assume (win ==> va_get_reg Rcx va_s0 == buffer_addr dst (va_get_mem va_s0));
assume (win ==> va_get_reg Rdx va_s0 == buffer_addr src (va_get_mem va_s0));
assume (~win ==> va_get_reg Rdi va_s0 == buffer_addr dst (va_get_mem va_s0));
assume (~win ==> va_get_reg Rsi va_s0 == buffer_addr src (va_get_mem va_s0));

  assert (va_req_memcpy va_b0 va_s0 win stack_b dst src);
  assert (va_pre c init win b dst src);
  assert (pre c win dst src init b);
  ()
  in

  assume False

let implies_post (dst src:buffer64) (h0 h1:HS.mem) : Lemma
  (requires normal (lift_vale_post (Vale_memcpy.va_code_memcpy win) dst src h0 h1))
  (ensures full_post_cond h0 h1 (to_b8 dst) (to_b8 src))
  = admit()

val memcpy: dst:buffer64 -> src:buffer64 -> Stack unit
        (requires (fun h -> pre_cond h (to_b8 dst) (to_b8 src)))
        (ensures (fun h0 _ h1 -> full_post_cond h0 h1 (to_b8 dst) (to_b8 src)))
let memcpy dst src =
  let h0 = get () in
  implies_pre dst src h0;
  memcpy_wrapped () dst src ();
  let h1 = get () in
  implies_post dst src h0 h1
