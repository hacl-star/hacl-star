module Vale.AsLowStar.Wrapper
open Interop.Base
module B = LowStar.Buffer
module BS = X64.Bytes_Semantics_s
module BV = LowStar.BufferView
module HS = FStar.HyperStack
module LU = LowStar.Util
module ME = X64.Memory
module TS = X64.Taint_Semantics_s
module MS = X64.Machine_s
module IA = Interop.Assumptions
module IM = Interop.Mem
module V = X64.Vale.Decls
module VS = X64.Vale.State
module IX64 = Interop.X64
module VSig = Vale.AsLowStar.ValeSig
module LSig = Vale.AsLowStar.LowStarSig
// open Vale.AsLowStar.Signature
// open Vale.AsLowStar.Util
// friend X64.Interop_s
// friend X64.Memory
// friend X64.Vale.Decls
// friend X64.Vale.StateLemmas
// friend X64.Memory_Sems
// module B = LowStar.Buffer
// module BV = LowStar.BufferView
// module HS = FStar.HyperStack
// module IA = Interop_assumptions
// module IS = X64.Interop_s
// module ME = X64.Memory
// module MS = X64.Machine_s
// module V = X64.Vale.Decls
// module VS = X64.Vale.State
// module VSig = Vale.AsLowStar.ValeSig
// module LSig = Vale.AsLowStar.LowStarSig
// module TS = X64.Taint_Semantics_s
module SL = X64.Vale.StateLemmas
// module BS = X64.Bytes_Semantics_s
// module MS = X64.Memory_Sems
module VL = X64.Vale.Lemmas

[@reduce]
let create_initial_vale_state
       (args:IX64.arity_ok arg)
  : IX64.state_builder_t args V.va_state =
  fun h0 stack ->
    let t_state, mem = IX64.create_initial_trusted_state args h0 stack in
    let open VS in
    { ok = true;
      regs = X64.Vale.Regs.of_fun t_state.TS.state.BS.regs;
      xmms = X64.Vale.Xmms.of_fun t_state.TS.state.BS.xmms;
      flags = 0; // REVIEW
      mem = mem;
      memTaint = TS.(t_state.memTaint) }

let lemma_create_initial_vale_state_core
    (args:IX64.arity_ok arg)
    (h0:HS.mem)
    (stack:IM.b8{mem_roots_p h0 (IX64.arg_of_b8 stack::args)})
  : Lemma
      (ensures (
        let s = create_initial_vale_state args h0 stack in
        Interop.Adapters.hs_of_mem VS.(s.mem) == h0
      ))
  = Interop.Adapters.mk_mem_injective (IX64.arg_of_b8 stack::args) h0

let core_create_lemma
    (args:IX64.arity_ok arg)
    (h0:HS.mem)
    (stack:b8{mem_roots_p h0 (IX64.arg_of_b8 stack::args)})
  : Lemma
      (ensures (let va_s = create_initial_vale_state args h0 stack in
                fst (IX64.create_initial_trusted_state args h0 stack) == SL.state_to_S va_s /\
                LSig.mem_correspondence args h0 va_s /\
                LSig.mk_vale_disjointness args /\
                LSig.mk_readable args va_s /\
                LSig.vale_pre_hyp args va_s))
  = admit() //needs the definition of SL.state_to_S; not sure why its hidden in StateLemma

let frame_mem_correspondence_back
       (args:list arg)
       (h0:mem_roots args)
       (h1:mem_roots args)
       (va_s:V.va_state)
       (l:B.loc)
 : Lemma
     (requires
       LSig.mem_correspondence args h1 va_s /\
       B.modifies l h0 h1 /\
       B.loc_disjoint (LSig.mk_modifies_loc args) l)
     (ensures
       LSig.mem_correspondence args h0 va_s)
 = admit()


let frame_mem_correspondence
       (args:list arg)
       (h0:HS.mem)
       (h1:HS.mem)
       (va_s:V.va_state)
       (l:B.loc)
 : Lemma
     (requires
       LSig.mem_correspondence args h0 va_s /\
       B.modifies l h0 h1 /\
       B.loc_disjoint (LSig.mk_modifies_loc args) l)
     (ensures
       LSig.mem_correspondence args h1 va_s)
 = admit()

let args_fp (args:list arg)
            (h0:mem_roots args)
            (h1:HS.mem{HS.fresh_frame h0 h1})
   : Lemma (B.loc_disjoint (LSig.mk_modifies_loc args) (B.loc_regions false (Set.singleton (HS.get_tip h1))))
   = admit()

module ST = FStar.HyperStack.ST
assume
val fuel_eq : squash (V.va_fuel == nat)


let eval_code_ts (c:TS.tainted_code)
                 (s0:TS.traceState)
                 (f0:nat)
                 (s1:TS.traceState) : Type0 =
  VL.state_eq_opt (TS.taint_eval_code c f0 s0) (Some s1)

let eval_code_rel (c:TS.tainted_code)
                  (va_s0 va_s1:_) (f:V.va_fuel)
  : Lemma
     (requires (V.eval_code c va_s0 f va_s1))
     (ensures (eval_code_ts c (SL.state_to_S va_s0) (coerce f) (SL.state_to_S va_s1)))
  = admit()

assume
val increase_fuel (c:TS.tainted_code)
                  (s0:TS.traceState)
                  (f0:nat)
                  (sN:TS.traceState)
                  (fN:nat) : Lemma
  (requires eval_code_ts c s0 f0 sN /\ f0 <= fN)
  (ensures eval_code_ts c s0 fN sN)

let fuel_irrelevance (c:TS.tainted_code)
                     (s0:TS.traceState)
                     (f1:nat)
                     (s1:TS.traceState)
                     (f2:nat)
                     (s2:TS.traceState)
  : Lemma
  (requires eval_code_ts c s0 f1 s1 /\
            eval_code_ts c s0 f2 s2)
  (ensures  VL.state_eq_opt (Some s1) (Some s2))
  = if f1 <= f2 then increase_fuel c s0 f1 s1 f2
    else increase_fuel c s0 f2 s2 f1

////////////////////////////////////////////////////////////////////////////////

let mem_correspondence_refl (args:list arg)
                            (va_s:V.va_state)
 : Lemma (ensures LSig.mem_correspondence args (Interop.Adapters.hs_of_mem va_s.VS.mem) va_s)
 = admit()

let state_to_S_mem
      (va_s:_)
      (s:_)
      (mem:ME.mem)
 : Lemma
     (requires (
       let open Interop.Adapters in
       VL.state_eq_S (SL.state_to_S va_s) s /\
       IM.down_mem
         (hs_of_mem mem)
         IA.addrs
         (ptrs_of_mem mem) == s.TS.state.BS.mem))
     (ensures
       va_s.VS.mem == mem)
 = admit()

let vale_lemma_as_prediction
          (code:V.va_code)
          (args:IX64.arity_ok arg)
          (num_stack_slots:nat)
          (pre:VSig.vale_pre_tl [])
          (post:VSig.vale_post_tl [])
          (v:VSig.vale_sig_tl args (coerce code) pre post)
          (h0:mem_roots args{LSig.(to_low_pre pre args (vale_pre_hyp args) (mem_correspondence args) num_stack_slots h0)})
   : s0:TS.traceState ->
     push_h0:mem_roots args ->
     alloc_push_h0:mem_roots args ->
     sb:IX64.stack_buffer{mem_roots_p alloc_push_h0 (IX64.arg_of_b8 sb::args)} ->
     Ghost (nat & ME.mem)
       (requires IX64.prediction_pre (coerce code) args h0 s0 push_h0 alloc_push_h0 sb)
       (ensures (fun (fuel, final_mem) ->
                Some? (TS.taint_eval_code (coerce code) fuel s0) /\ (
                let sN = Some?.v (TS.taint_eval_code (coerce code) fuel s0) in
                let va_s0 = create_initial_vale_state args alloc_push_h0 sb in
                elim_nil pre va_s0 sb /\
                (let va_s1, f = VSig.elim_vale_sig_nil v va_s0 sb in
                 coerce f == fuel /\
                 VL.state_eq_opt (Some (SL.state_to_S va_s1)) (Some sN)) /\
                IX64.calling_conventions s0 sN)))
   = fun s0 push_h0 alloc_push_h0 sb ->
       let va_s0 = create_initial_vale_state args alloc_push_h0 sb in
       core_create_lemma args alloc_push_h0 sb;
       assert (SL.state_to_S va_s0 == s0);
       B.fresh_frame_modifies h0 push_h0;
       assert (B.modifies B.loc_none h0 alloc_push_h0);
       assert (LSig.mem_correspondence args alloc_push_h0 va_s0);
       frame_mem_correspondence_back args h0 alloc_push_h0 va_s0 B.loc_none;
       assert (LSig.mem_correspondence args h0 va_s0);
       assert (va_s0.VS.ok);
       assert (LSig.vale_pre_hyp args va_s0);
       assume (V.valid_stack_slots
                va_s0.VS.mem
                (VS.eval_reg MS.Rsp va_s0)
                (as_vale_buffer sb)
                num_stack_slots
                va_s0.VS.memTaint);
       assert (elim_nil pre va_s0 sb);
       let va_s1, f = VSig.elim_vale_sig_nil v va_s0 sb in
       assert (V.eval_code (coerce code) va_s0 f va_s1);
       eval_code_rel (coerce code) va_s0 va_s1 f;
       let Some s1 = TS.taint_eval_code (coerce code) (coerce f) s0 in
       assert (VL.state_eq_opt (Some (SL.state_to_S va_s1)) (Some s1));
       assert (IX64.calling_conventions s0 s1);
       coerce f, va_s1.VS.mem

let lowstar_lemma_base
          (code:V.va_code)
          (args:IX64.arity_ok arg)
          (num_stack_slots:nat)
          (pre:VSig.vale_pre_tl [])
          (post:VSig.vale_post_tl [])
          (v:VSig.vale_sig_tl args (coerce code) pre post)
          (h0:mem_roots args)
          (predict:IX64.prediction (coerce code) args h0)
          (ret:IX64.as_lowstar_sig_ret args)
          (h1:mem_roots args)
  : Lemma
      (requires (LSig.(to_low_pre pre args (vale_pre_hyp args) (mem_correspondence args) num_stack_slots h0 /\
                 IX64.as_lowstar_sig_post (coerce code) args h0 predict ret h1)))
      (ensures LSig.(to_low_post post args (mk_modifies_loc args) (mem_correspondence args) h0 () h1))
  = let open LSig in
    let open IX64 in
    let As_lowstar_sig_ret push_h0 alloc_push_h0 stack_buf fuel final_mem = ret in
    let s0 = fst (create_initial_trusted_state args alloc_push_h0 stack_buf) in
    let Some s1 = TS.taint_eval_code (coerce code) fuel s0 in
    assert (IM.down_mem (Interop.Adapters.hs_of_mem final_mem)
                        (IA.addrs)
                        (Interop.Adapters.ptrs_of_mem final_mem) == s1.TS.state.BS.mem);
    let va_s0 = create_initial_vale_state args alloc_push_h0 stack_buf in
    core_create_lemma args alloc_push_h0 stack_buf;
    assert (SL.state_to_S va_s0 == s0);
    B.fresh_frame_modifies h0 push_h0;
    assert (B.modifies B.loc_none h0 alloc_push_h0);
    assert (mem_correspondence args alloc_push_h0 va_s0);
    frame_mem_correspondence_back args h0 alloc_push_h0 va_s0 B.loc_none;
    assert (mem_correspondence args h0 va_s0);
    assert (va_s0.VS.ok);
    assert (vale_pre_hyp args va_s0);
    assume (V.valid_stack_slots
              va_s0.VS.mem
              (VS.eval_reg MS.Rsp va_s0)
              (as_vale_buffer stack_buf)
              num_stack_slots
              va_s0.VS.memTaint);
    assert (elim_nil pre va_s0 stack_buf);
    let va_s1, f = VSig.elim_vale_sig_nil v va_s0 stack_buf in
    assert (V.eval_code (coerce code) va_s0 f va_s1);
    eval_code_rel (coerce code) va_s0 va_s1 f;
    let Some s1' = TS.taint_eval_code (coerce code) (coerce f) s0 in
    fuel_irrelevance (coerce code) s0 fuel s1 (coerce f) s1';
    assert (VL.state_eq_opt (Some (SL.state_to_S va_s1)) (Some s1));
    assert (VSig.vale_calling_conventions va_s0 va_s1);
    assert (elim_nil post va_s0 stack_buf va_s1 f);
    assert (ME.modifies (VSig.fp_of_args args) va_s0.VS.mem va_s1.VS.mem);
    let h1_pre_pop = Interop.Adapters.hs_of_mem final_mem in
    assert (IM.down_mem h1_pre_pop (IA.addrs) (Interop.Adapters.ptrs_of_mem final_mem) == s1.TS.state.BS.mem);
    assume (va_s1.VS.mem == final_mem);
    mem_correspondence_refl args va_s1;
    assert (HS.poppable h1_pre_pop);
    assert (h1 == HS.pop h1_pre_pop);
    args_fp args h0 push_h0;
    assert (HS.get_tip push_h0 == HS.get_tip h1_pre_pop);
    B.popped_modifies h1_pre_pop h1;
    frame_mem_correspondence args h1_pre_pop h1 va_s1 (B.loc_regions false (Set.singleton (HS.get_tip h1_pre_pop)))

let rec lowstar_lemma
          (dom:list td)
          (code:V.va_code)
          (args:list arg{List.length args + List.length dom < IX64.max_arity})
          (num_stack_slots:nat)
          (pre:VSig.vale_pre_tl dom)
          (post:VSig.vale_post_tl dom)
          (v:VSig.vale_sig_tl args (coerce code) pre post)
    : lowstar_lemma_typ code args num_stack_slots pre post
    = match dom with
      | [] ->
        lowstar_lemma_base code args num_stack_slots pre post v
      | hd::tl ->
        fun (x:td_as_type hd) ->
          lowstar_lemma
            tl
            code
            ((| hd, x |) :: args)
            num_stack_slots
            (elim_1 pre x)
            (elim_1 post x)
            (VSig.elim_vale_sig_cons hd tl args pre post v x)

// let rec wrap_aux
//          (code:V.va_code)
//          (dom:list td)
//          (args:list arg{List.length args + List.length dom < IX64.max_arity})
//          (num_stack_slots:nat)
//          (pre:VSig.vale_pre_tl dom)
//          (post:VSig.vale_post_tl dom)
//          (v:VSig.vale_sig_tl args code pre post)
//     : LSig.as_lowstar_sig_tl args num_stack_slots pre post
//     = match dom with
//       | [] ->
//         let code : TS.tainted_code = coerce code in
//         let f : LSig.as_lowstar_sig_tl #[] args num_stack_slots pre post =
//           fun () ->
//             let h0 = ST.get () in
//             let f_predict
//                 (s0:TS.traceState)
//                 (push_h0:mem_roots args)
//                 (alloc_push_h0:mem_roots args)
//                 (b:IX64.stack_buffer{mem_roots_p alloc_push_h0 (IX64.arg_of_b8 b::args)})
//               : Ghost (nat & ME.mem)
//                   (requires IX64.prediction_pre code args h0 s0 push_h0 alloc_push_h0 b)
//                   (ensures IX64.prediction_post code args h0 s0 push_h0 alloc_push_h0 b)
//                 = admit()
//                 // let va_s0 = elim_down_nil acc v_down alloc_push_h0 b in
//                 // let va_s1, fuel = elim_vale_sig_nil pre post v va_s0 (to_b8 b) in
//                 // (fuel, va_s1.mem)
//             in
//             let predict : IX64.prediction code args h0 = f_predict in
//             let IX64.As_lowstar_sig_ret push_h0 alloc_push_h0 b fuel final_mem =
//               IX64.wrap code args h0 predict
//             in
//             admit()
//             // let h1 = get () in
//             // assert (
//             //   let initial_state = elim_down_nil acc v_down alloc_push_h0 b in
//             //   let (final, fuel) = elim_vale_sig_nil pre post v initial_state b in
//             //   eval_code code initial_state fuel final
//             // );
//             // ()
//         in
//         f <: LSig.as_lowstar_sig_tl #[] args num_stack_slots pre post
//       | hd::tl ->
//         let f (x:td_as_type hd) =
//           wrap_aux
//               code
//               tl
//               ((|hd,x|)::args)
//               num_stack_slots
//               (elim_1 pre x)
//               (elim_1 post x)
//               (VSig.elim_vale_sig_cons hd tl args pre post v x)
//         in
//         f


// let wrap
//     (code:V.va_code)
//     (dom:IX64.arity_ok td)
//     (num_stack_slots:nat)
//     (pre:VSig.vale_pre dom)
//     (post:VSig.vale_post dom)
//     (v:VSig.vale_sig pre post)
//   : LSig.as_lowstar_sig code dom num_stack_slots pre post
//   = wrap_aux code dom [] num_stack_slots (pre code) (post code) (v code IA.win)


let test (l:B.loc) = assert (B.loc_disjoint l B.loc_none)
let frame_mem_correspondence_pop
       (args:list arg)
       (h:HS.mem)
       (va_s:V.va_state)
 : Lemma
     (requires
       LSig.mem_correspondence args h va_s /\
       B.loc_disjoint (LSig.mk_modifies_loc args)
                      (B.loc_regions false (Set.singleton (HS.get_tip h))) /\
       HS.poppable h)
     (ensures
       LSig.mem_correspondence args (HS.pop h) va_s)
 = admit()

module ST = FStar.HyperStack.ST
let test (x:B.buffer bool)
         (h:HS.mem{ B.live h x /\
                    B.loc_disjoint (B.loc_buffer x)
                                   (B.loc_regions false (Set.singleton (HS.get_tip h))) /\
                    HS.poppable h }) =
    B.popped_modifies h (HS.pop h);
//    assume (B.modifies (B.loc_regions false (Set.singleton (HS.get_tip h))) h (HS.pop h)); //need this
    assert (B.live (HS.pop h) x)


        ST.equal_domains h1 h2 /\ HS.poppable h2})
   : Lemma (B.loc_disjoint (B.loc_regions false (Set.singleton (HS.get_tip h1)))
                           (B.loc_buffer x) /\
            B.loc_disjoint (B.loc_regions false (Set.singleton (HS.get_tip h2)))
                           (B.loc_buffer x) /\
            B.live h2 x)

let test (x:B.buffer bool)
         (h0:HS.mem{B.live h0 x})
         (h1:HS.mem{HS.fresh_frame h0 h1})
         (h2:HS.mem{ST.equal_domains h1 h2 /\ HS.poppable h2})
   : Lemma (B.loc_disjoint (B.loc_regions false (Set.singleton (HS.get_tip h1)))
                           (B.loc_buffer x) /\
            B.loc_disjoint (B.loc_regions false (Set.singleton (HS.get_tip h2)))
                           (B.loc_buffer x) /\
            B.live h2 x)
            // B.live (HS.pop h2) x)
   = ()
//                          B.loc_none)= ()
