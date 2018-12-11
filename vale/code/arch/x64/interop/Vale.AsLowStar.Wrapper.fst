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
friend X64.Memory
friend X64.Vale.Decls
friend X64.Vale.StateLemmas
friend X64.Memory_Sems
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
// module SL = X64.Vale.StateLemmas
// module BS = X64.Bytes_Semantics_s
// module MS = X64.Memory_Sems


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
    (stack:ME.b8{mem_roots_p h0 (IX64.arg_of_b8 stack::args)})
  : Lemma
      (ensures (
        let s = create_initial_vale_state args h0 stack in
        VS.(ME.(s.mem.hs)) == h0
      ))
  = admit()

// let core_create_lemma
//     (acc:list ME.b8)
//     (regs:IS.registers)
//     (xmms:IS.xmms_t)
//     (taint:IS.taint_map)
//     (h0:HS.mem)
//     (stack:ME.b8{IS.mem_roots_p h0 (stack::acc)})
//   : Lemma
//       (ensures (fst (IS.create_initial_trusted_state_core acc regs xmms taint h0 stack) ==
//                 SL.state_to_S (create_initial_vale_state_core acc regs xmms taint h0 stack)))
//   =
//     let s_init, mem = IS.create_initial_trusted_state_core acc regs xmms taint h0 stack in
//     let s0 = create_initial_vale_state_core acc regs xmms taint h0 stack in
//     let s1 = SL.state_to_S s0 in
//     assert (FunctionalExtensionality.feq (SL.regs' s1.TS.state) (SL.regs' s_init.TS.state));
//     assert (FunctionalExtensionality.feq (SL.xmms' s1.TS.state) (SL.xmms' s_init.TS.state))

// [@IS.reduce]
// let initial_vale_state_t (dom:list IS.vale_type) (acc:list ME.b8) =
//   IS.initial_state_t dom acc V.va_state

// [@IS.reduce]
// let create_vale_initial_state_t (dom:list IS.vale_type)
//                                 (acc:list ME.b8)
//     = IS.n_dep_arrow
//           dom
//           (initial_vale_state_t dom acc)

// [@IS.reduce]
// let create_vale_initial_state
//       (dom:sig_arity_ok)
//     : create_vale_initial_state_t dom []
//     = IS.create_initial_state_aux
//           dom
//           IA.win
//           0
//           IA.init_regs
//           IA.init_xmms
//           []
//           IS.init_taint
//           create_initial_vale_state_core

// [@IS.reduce]
// let elim_down_nil (acc:list ME.b8)
//                   (down:create_vale_initial_state_t [] acc)
//     : h0:HS.mem -> stack:ME.b8{IS.mem_roots_p h0 (stack::acc)} -> GTot V.va_state =
//     down

// [@IS.reduce]
// let elim_down_cons (hd:IS.vale_type)
//                    (tl:list IS.vale_type)
//                    (acc:list ME.b8)
//                    (down:create_vale_initial_state_t (hd::tl) acc)
//                    (x:IS.vale_type_as_type hd)
//     : create_vale_initial_state_t tl (IS.maybe_cons_buffer hd x acc) =
//     IS.elim_dep_arrow_cons hd tl down x

// let rec n_dep_arrow_equiv (dom:list IS.vale_type)
//                           (acc:list ME.b8)
//                           (f:IS.create_trusted_initial_state_t dom acc)
//                           (g:create_vale_initial_state_t dom acc) =
//     match dom with
//     | [] ->
//       forall h0 (stack:ME.b8{IS.mem_roots_p h0 (stack::acc)}).
//         fst (IS.elim_down_nil acc f h0 stack) == SL.state_to_S (elim_down_nil acc g h0 stack)

//     | hd::tl ->
//       forall (x:IS.vale_type_as_type hd).
//         n_dep_arrow_equiv tl (IS.maybe_cons_buffer hd x acc)
//                              (IS.elim_down_cons hd tl acc f x)
//                              (elim_down_cons hd tl acc g x)

// let rec equiv_create_trusted_and_vale_state
//           (dom:list IS.vale_type)
//           (i:nat{i + List.length dom < IS.max_arity IA.win})
//           (regs:_)
//           (xmms:_)
//           (acc:list ME.b8)
//           (taint:_)
//     : Lemma (n_dep_arrow_equiv
//                   dom
//                   acc
//                   (IS.create_initial_state_aux
//                       dom
//                       IA.win
//                       i
//                       regs
//                       xmms
//                       acc
//                       taint
//                       IS.create_initial_trusted_state_core)
//                   (IS.create_initial_state_aux
//                       dom
//                       IA.win
//                       i
//                       regs
//                       xmms
//                       acc
//                       taint
//                       create_initial_vale_state_core))
//      = match dom with
//        | [] ->
//          FStar.Classical.forall_intro_2 (core_create_lemma acc regs xmms taint)
//        | hd::tl ->
//          let aux (x:IS.vale_type_as_type hd)
//            : Lemma (n_dep_arrow_equiv
//                       tl
//                       (IS.maybe_cons_buffer hd x acc)
//                       (IS.create_initial_state_aux
//                            tl
//                            IA.win
//                            (i + 1)
//                            (IS.update_regs x IA.win i regs)
//                            xmms
//                            (IS.maybe_cons_buffer hd x acc)
//                            (IS.update_taint_map x taint)
//                            IS.create_initial_trusted_state_core)
//                       (IS.create_initial_state_aux
//                            tl
//                            IA.win
//                            (i + 1)
//                            (IS.update_regs x IA.win i regs)
//                            xmms
//                            (IS.maybe_cons_buffer hd x acc)
//                            (IS.update_taint_map x taint)
//                            create_initial_vale_state_core))
//          =
//            equiv_create_trusted_and_vale_state
//                 tl
//                 (i + 1)
//                 (IS.update_regs x IA.win i regs)
//                 xmms
//                 (IS.maybe_cons_buffer hd x acc)
//                 (IS.update_taint_map x taint)
//           in
//           FStar.Classical.forall_intro aux

// let rec wrap_tl
//          (code:V.va_code)
//          (dom:list IS.vale_type)
//          (acc:list ME.b8)
//          (args:LSig.lowstar_args{List.length args + List.length dom < IS.max_arity IA.win})
//          (num_stack_slots:nat)
//          (fp:ME.loc)
//          (v_down:create_vale_initial_state_t dom acc)
//          (t_down:IS.create_trusted_initial_state_t dom acc{n_dep_arrow_equiv dom acc t_down v_down})
//          (pre:VSig.vale_pre_tl dom)
//          (post:VSig.vale_post_tl dom)
//          (v:VSig.vale_sig_tl fp code IA.win pre post)
//          (t_low:IS.as_lowstar_sig_tl code dom acc t_down)
//     : LSig.as_lowstar_sig_tl args num_stack_slots pre post
//     = admit()

// let wrap
//     (code:V.va_code)
//     (dom:sig_arity_ok)
//     (num_stack_slots:nat)
//     (pre:VSig.vale_pre dom)
//     (post:VSig.vale_post dom)
//     (v:VSig.vale_sig pre post)
//   : LSig.as_lowstar_sig code dom num_stack_slots pre post
//   = let is_wrapper = IS.wrap code dom in
//     equiv_create_trusted_and_vale_state dom 0 IA.init_regs IA.init_xmms [] IS.init_taint;
//     wrap_tl
//       code
//       dom
//       []
//       []
//       num_stack_slots
//       ME.loc_none
//       (create_vale_initial_state dom)
//       (IS.create_trusted_initial_state IA.win dom)
//       (pre code IA.win)
//       (post code IA.win)
//       (v code IA.win)
//       is_wrapper
