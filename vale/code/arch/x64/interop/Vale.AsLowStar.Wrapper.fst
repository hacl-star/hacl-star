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
module SL = X64.Vale.StateLemmas
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

// assume
// val increase_fuel (c:TS.tainted_code)
//                   (s0:TS.traceState)
//                   (f0:nat)
//                   (sN:TS.traceState)
//                   (fN:nat) : Lemma
//   (requires eval_code_ts c s0 f0 sN /\ f0 <= fN)
//   (ensures eval_code_ts c s0 fN sN)

// let fuel_irrelevance (c:TS.tainted_code)
//                      (s0:TS.traceState)
//                      (f1:nat)
//                      (s1:TS.traceState)
//                      (f2:nat)
//                      (s2:TS.traceState)
//   : Lemma
//   (requires eval_code_ts c s0 f1 s1 /\
//             eval_code_ts c s0 f2 s2)
//   (ensures  VL.state_eq_opt (Some s1) (Some s2))
//   = if f1 <= f2 then increase_fuel c s0 f1 s1 f2
//     else increase_fuel c s0 f2 s2 f1

////////////////////////////////////////////////////////////////////////////////

let mem_correspondence_refl (args:list arg)
                            (va_s:V.va_state)
 : Lemma (ensures LSig.mem_correspondence args (Interop.Adapters.hs_of_mem va_s.VS.mem) va_s)
 = admit()

////////////////////////////////////////////////////////////////////////////////

let prediction_rel
          (code:V.va_code)
          (args:IX64.arity_ok arg)
          (num_stack_slots:nat)
          (pre:VSig.vale_pre_tl [])
          (post:VSig.vale_post_tl [])
          (v:VSig.vale_sig_tl args (coerce code) pre post)
          (h0:mem_roots args{LSig.(to_low_pre pre args num_stack_slots h0)})
          (s0:TS.traceState)
          (push_h0:mem_roots args)
          (alloc_push_h0:mem_roots args)
          (sb:IX64.stack_buffer{mem_roots_p alloc_push_h0 (IX64.arg_of_b8 sb::args)})
          (fuel_mem:(nat & ME.mem))
          (s1:TS.traceState) : prop =
    let va_s0 = create_initial_vale_state args alloc_push_h0 sb in
    LSig.mem_correspondence args h0 va_s0 /\
    elim_nil pre va_s0 sb /\
    (let va_s1, f = VSig.elim_vale_sig_nil v va_s0 sb in
     coerce f == fst fuel_mem /\
     va_s1.VS.mem == snd fuel_mem /\
     VL.state_eq_opt (Some (SL.state_to_S va_s1)) (Some s1))

let pop_is_popped (m:HS.mem{HS.poppable m})
  : Lemma (HS.popped m (HS.pop m))
  = ()

#set-options "--z3rlimit_factor 2"
let vale_lemma_as_prediction
          (code:V.va_code)
          (args:IX64.arity_ok arg)
          (num_stack_slots:nat)
          (pre:VSig.vale_pre_tl [])
          (post:VSig.vale_post_tl [])
          (v:VSig.vale_sig_tl args (coerce code) pre post)
          (h0:mem_roots args{LSig.(to_low_pre pre args num_stack_slots h0)})
   : IX64.prediction (coerce code) args h0 (prediction_rel code args num_stack_slots pre post v h0)
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
       assert (ME.modifies (VSig.mloc_args args) va_s0.VS.mem va_s1.VS.mem);
       let h1 = (Interop.Adapters.hs_of_mem va_s1.VS.mem) in
       let final_mem = va_s1.VS.mem in
       assume (B.modifies (loc_args args) alloc_push_h0 h1);
       assume (FStar.HyperStack.ST.equal_domains alloc_push_h0 h1);
       assume (IM.down_mem h1
                           (IA.addrs)
                           (Interop.Adapters.ptrs_of_mem final_mem) == s1.TS.state.BS.mem);
       let h1_pre_pop = Interop.Adapters.hs_of_mem final_mem in
       assert (IM.down_mem h1_pre_pop (IA.addrs) (Interop.Adapters.ptrs_of_mem final_mem) == s1.TS.state.BS.mem);
       assert (va_s1.VS.mem == final_mem);
       mem_correspondence_refl args va_s1;
       assert (HS.poppable h1_pre_pop);
       let h2 = HS.pop h1_pre_pop in
       args_fp args h0 push_h0;
       assert (HS.get_tip push_h0 == HS.get_tip h1_pre_pop);
       pop_is_popped h1_pre_pop;
       assert (HS.popped h1_pre_pop h2);
       B.popped_modifies h1_pre_pop h2;
       frame_mem_correspondence args h1_pre_pop h2 va_s1 (B.loc_regions false (Set.singleton (HS.get_tip h1_pre_pop)));
       assert (B.modifies (loc_args args) alloc_push_h0 h1_pre_pop);
       assume (B.modifies (loc_args args) h0 h2);
       assume (mem_roots_p h2 args);
       assert (LSig.(to_low_post post args h0 () h2));
       coerce f, va_s1.VS.mem

let lowstar_lemma_post
          (code:V.va_code)
          (args:IX64.arity_ok arg)
          (num_stack_slots:nat)
          (pre:VSig.vale_pre_tl [])
          (post:VSig.vale_post_tl [])
          (v:VSig.vale_sig_tl args (coerce code) pre post)
          (h0:mem_roots args{LSig.(to_low_pre pre args num_stack_slots h0)})
          (predict: IX64.prediction (coerce code) args h0 (prediction_rel code args num_stack_slots pre post v h0))
          (ret:IX64.as_lowstar_sig_ret args)
          (h1:mem_roots args)
  : Lemma
      (requires (IX64.as_lowstar_sig_post (coerce code) args h0 predict ret h1))
      (ensures LSig.(to_low_post post args h0 () h1))
  = let open LSig in
    let open IX64 in
    let As_lowstar_sig_ret push_h0 alloc_push_h0 stack_buf fuel final_mem = ret in
    let s0 = fst (create_initial_trusted_state args alloc_push_h0 stack_buf) in
    let Some s1 = TS.taint_eval_code (coerce code) fuel s0 in
    let va_s0 = create_initial_vale_state args alloc_push_h0 stack_buf in
    let va_s1, f = VSig.elim_vale_sig_nil v va_s0 stack_buf in
    assert (V.eval_code (coerce code) va_s0 f va_s1);
    assert (VL.state_eq_opt (Some (SL.state_to_S va_s1)) (Some s1));
    assert (VSig.vale_calling_conventions va_s0 va_s1);
    assert (elim_nil post va_s0 stack_buf va_s1 f);
    assert (ME.modifies (VSig.mloc_args args) va_s0.VS.mem va_s1.VS.mem);
    let h1_pre_pop = Interop.Adapters.hs_of_mem final_mem in
    assert (IM.down_mem h1_pre_pop (IA.addrs) (Interop.Adapters.ptrs_of_mem final_mem) == s1.TS.state.BS.mem);
    assert (va_s1.VS.mem == final_mem);
    mem_correspondence_refl args va_s1;
    assert (HS.poppable h1_pre_pop);
    assert (h1 == HS.pop h1_pre_pop);
    args_fp args h0 push_h0;
    assert (HS.get_tip push_h0 == HS.get_tip h1_pre_pop);
    B.popped_modifies h1_pre_pop h1;
    frame_mem_correspondence args h1_pre_pop h1 va_s1 (B.loc_regions false (Set.singleton (HS.get_tip h1_pre_pop)));
    assert (B.modifies (loc_args args) alloc_push_h0 h1_pre_pop);
    assume (B.modifies (loc_args args) h0 h1)

[@reduce]
let rec lowstar_typ
          (#dom:list td)
          (code:V.va_code)
          (args:list arg{List.length args + List.length dom < IX64.max_arity})
          (num_stack_slots:nat)
          (pre:VSig.vale_pre_tl dom)
          (post:VSig.vale_post_tl dom)
    : Type =
    let open FStar.HyperStack.ST in
    match dom with
    | [] ->
      unit ->
      Stack unit
        (requires (fun h0 ->
          mem_roots_p h0 args /\
          LSig.to_low_pre pre args num_stack_slots h0))
        (ensures (fun h0 _ h1 ->
          mem_roots_p h1 args /\
          LSig.to_low_post post args h0 () h1))

    | hd::tl ->
      x:td_as_type hd ->
      lowstar_typ
        #tl
        code
        ((| hd, x |)::args)
        num_stack_slots
        (elim_1 pre x)
        (elim_1 post x)

let rec wrap (#dom:list td)
             (code:V.va_code)
             (args:list arg{List.length args + List.length dom < IX64.max_arity})
             (num_stack_slots:nat)
             (pre:VSig.vale_pre_tl dom)
             (post:VSig.vale_post_tl dom)
             (v:VSig.vale_sig_tl args (coerce code) pre post)
    : lowstar_typ code args num_stack_slots pre post =
    match dom with
    | [] ->
      let f :
        unit ->
        ST.Stack unit
          (requires (fun h0 ->
            mem_roots_p h0 args /\
            LSig.to_low_pre pre args num_stack_slots h0))
          (ensures (fun h0 _ h1 ->
            mem_roots_p h1 args /\
            LSig.to_low_post post args h0 () h1)) =
         fun () ->
           let h0 = ST.get () in
           let prediction = vale_lemma_as_prediction code args num_stack_slots pre post v h0 in
           let ix64_ret = IX64.wrap (coerce code) args h0 prediction in
           let h1 = ST.get() in
           assume (mem_roots_p h1 args);
           lowstar_lemma_post code args num_stack_slots pre post v h0 prediction ix64_ret h1
      in
      f <: lowstar_typ #[] code args num_stack_slots pre post
    | hd::tl ->
      fun (x:td_as_type hd) ->
        wrap
          code
          ((| hd, x |) :: args)
          num_stack_slots
          (elim_1 pre x)
          (elim_1 post x)
          (VSig.elim_vale_sig_cons hd tl args pre post v x)
