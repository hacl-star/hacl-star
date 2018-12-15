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

////////////////////////////////////////////////////////////////////////////////

let mem_correspondence_refl (args:list arg)
                            (va_s:V.va_state)
 : Lemma (ensures LSig.mem_correspondence args (Interop.Adapters.hs_of_mem va_s.VS.mem) va_s)
 = admit()

////////////////////////////////////////////////////////////////////////////////

let prediction_pre_rel
          (num_stack_slots:nat)
          (pre:VSig.vale_pre_tl [])
          (code:V.va_code)
          (args:IX64.arity_ok arg)
   : IX64.prediction_pre_rel_t code args
   = fun (h0:mem_roots args) ->
      LSig.(to_low_pre pre args num_stack_slots h0)

let prediction_post_rel
          (num_stack_slots:nat)
          (post:VSig.vale_post_tl [])
          (code:V.va_code)
          (args:IX64.arity_ok arg)
   : IX64.prediction_post_rel_t code args
   = fun (h0:mem_roots args)
       (s0:TS.traceState)
       (push_h0:mem_roots args)
       (alloc_push_h0:mem_roots args)
       (sb:IX64.stack_buffer{mem_roots_p alloc_push_h0 (IX64.arg_of_b8 sb::args)})
       (fuel_mem:(nat & ME.mem))
       (s1:TS.traceState) ->
    let open Interop.Adapters in
    let h1_pre_pop = hs_of_mem (snd fuel_mem) in
    HS.poppable h1_pre_pop /\ (
    let h1 = HS.pop h1_pre_pop in
    mem_roots_p h1 args /\
    LSig.(to_low_post post args h0 () h1))

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
   : IX64.prediction
             (coerce code)
             args
             (prediction_pre_rel num_stack_slots pre (coerce code) args)
             (prediction_post_rel num_stack_slots post (coerce code) args)
   = fun h0 s0 push_h0 alloc_push_h0 sb ->
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

[@reduce]
let rec lowstar_typ
          (#dom:list td)
          (code:V.va_code)
          (args:list arg{IX64.arity_ok_2 dom args})
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

#set-options "--initial_ifuel 1"
let rec wrap (#dom:list td)
             (code:V.va_code)
             (args:list arg{IX64.arity_ok_2 dom args})
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
           let prediction =
             vale_lemma_as_prediction _ _ num_stack_slots _ _ v in
           let _ = IX64.wrap_variadic (coerce code) args prediction in
           ()
      in
      f <: lowstar_typ #[] code args num_stack_slots pre post
    | hd::tl ->
      fun (x:td_as_type hd) ->
        wrap
          code
          IX64.(x ++ args)
          num_stack_slots
          (elim_1 pre x)
          (elim_1 post x)
          (VSig.elim_vale_sig_cons hd tl args pre post v x)

// ////////////////////////////////////////////////////////////////////////////////
// //Wrap abstract
// ////////////////////////////////////////////////////////////////////////////////
let rec pre_rel_generic
      (n:nat)
      (code:V.va_code)
      (dom:list td)
      (args:list arg{IX64.arity_ok_2 dom args})
      (pre:VSig.vale_pre_tl dom)
   : IX64.rel_gen_t code dom args (IX64.prediction_pre_rel_t (coerce code))
   = match dom with
     | [] ->
       prediction_pre_rel n pre (coerce code) args
     | hd::tl ->
       fun (x:td_as_type hd) ->
       pre_rel_generic n code tl IX64.(x ++ args) (elim_1 pre x)

let rec post_rel_generic
      (n:nat)
      (code:V.va_code)
      (dom:list td)
      (args:list arg{IX64.arity_ok_2 dom args})
      (post:VSig.vale_post_tl dom)
   : IX64.rel_gen_t code dom args (IX64.prediction_post_rel_t (coerce code))
   = match dom with
     | [] ->
       prediction_post_rel n post (coerce code) args
     | hd::tl ->
       fun (x:td_as_type hd) ->
       post_rel_generic n code tl IX64.(x ++ args) (elim_1 post x)

let rec mk_prediction
       (code:V.va_code)
       (dom:list td)
       (args:list arg{IX64.arity_ok_2 dom args})
       (n:nat)
       (pre:VSig.vale_pre_tl dom)
       (post:VSig.vale_post_tl dom)
       (v:VSig.vale_sig_tl args (coerce code) pre post)
   :  IX64.prediction_t
          (coerce code)
          dom
          args
          (pre_rel_generic n code dom args pre)
          (post_rel_generic n code dom args post)
   = let open IX64 in
     match dom with
     | [] ->
       vale_lemma_as_prediction _ _ n _ _ v
     | hd::tl ->
       fun (x:td_as_type hd) ->
        mk_prediction
          code
          tl
          (x ++ args)
          n
          (elim_1 pre x)
          (elim_1 post x)
          (VSig.elim_vale_sig_cons hd tl args pre post v x)

////////////////////////////////////////////////////////////////////////////////
//test
////////////////////////////////////////////////////////////////////////////////

let t = TD_Buffer ME.TUInt64
unfold let dom : (x:list td {List.length x == 2}) =
  let y = [t; t] in
  assert_norm (List.length y = 2);
  y

assume val pre : VSig.vale_pre dom
assume val post : VSig.vale_post dom
assume val n : nat
assume val v: VSig.vale_sig pre post
assume val c: V.va_code
open Interop.X64

let call_c
  : as_lowstar_sig_t c dom [] _ _ (mk_prediction c dom [] n (pre c) (post c) (v c IA.win))
  = IX64.wrap c dom (mk_prediction c dom [] n (pre c) (post c) (v c IA.win))
