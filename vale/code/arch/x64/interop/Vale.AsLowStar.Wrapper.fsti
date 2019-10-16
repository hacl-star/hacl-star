module Vale.AsLowStar.Wrapper
open Vale.X64.MemoryAdapters
open Vale.Interop.Base
module B = LowStar.Buffer
module BS = Vale.X64.Machine_Semantics_s
module UV = LowStar.BufferView.Up
module DV = LowStar.BufferView.Down
module HS = FStar.HyperStack
module ME = Vale.X64.Memory
module SI = Vale.X64.Stack_i
module MS = Vale.X64.Machine_s
module IA = Vale.Interop.Assumptions
module I = Vale.Interop
module V = Vale.X64.Decls
module VS = Vale.X64.State
module IX64 = Vale.Interop.X64
module VSig = Vale.AsLowStar.ValeSig
module LSig = Vale.AsLowStar.LowStarSig
module SL = Vale.X64.StateLemmas
module VL = Vale.X64.Lemmas
module ST = FStar.HyperStack.ST
open FStar.Mul
open FStar.Calc

[@__reduce__]
let prediction_pre_rel
    (#max_arity:nat)
    (#arg_reg:IX64.arg_reg_relation max_arity)
    (pre:VSig.vale_pre_tl [])
    (code:V.va_code)
    (args:IX64.arg_list)
  : IX64.prediction_pre_rel_t code args
  =
  fun (h0:mem_roots args) ->
    LSig.(to_low_pre #max_arity #arg_reg pre args h0)

[@__reduce__]
let prediction_post_rel
    (#max_arity:nat)
    (post:VSig.vale_post_tl [])
    (code:V.va_code)
    (args:IX64.arg_list)
  : IX64.prediction_post_rel_t code args
  =
  fun
    (h0:mem_roots args)
    (_s0:BS.machine_state)
    (rax_fuel_mem:(UInt64.t & nat & interop_heap))
    (s1:BS.machine_state) ->
  let rax, fuel, mem = rax_fuel_mem in
  exists h1.
    h1 == hs_of_mem mem /\
    mem_roots_p h1 args /\
    LSig.(to_low_post post args h0 rax h1)

val vale_lemma_as_prediction
    (#max_arity:nat)
    (#arg_reg:IX64.arg_reg_relation max_arity)
    (#regs_modified:MS.reg_64 -> bool)
    (#xmms_modified:MS.reg_xmm -> bool)
    (code:V.va_code)
    (args:IX64.arg_list)
    (pre:VSig.vale_pre_tl [])
    (post:VSig.vale_post_tl [])
    (v:VSig.vale_sig_tl regs_modified xmms_modified args (coerce code) pre post)
  : IX64.prediction
      max_arity
      arg_reg
      regs_modified
      xmms_modified
      (coerce code)
      args
      (prediction_pre_rel #max_arity #arg_reg pre (coerce code) args)
      (prediction_post_rel #max_arity post (coerce code) args)

// ////////////////////////////////////////////////////////////////////////////////
// //Wrap abstract
// ////////////////////////////////////////////////////////////////////////////////
[@__reduce__]
let rec pre_rel_generic
    (#max_arity:nat)
    (#arg_reg:IX64.arg_reg_relation max_arity)
    (code:V.va_code)
    (dom:list td)
    (args:list arg{List.length dom + List.length args <= 20})
    (pre:VSig.vale_pre_tl dom)
  : IX64.rel_gen_t code dom args (IX64.prediction_pre_rel_t (coerce code))
  =
  match dom with
  | [] ->
    prediction_pre_rel #max_arity #arg_reg pre (coerce code) args
  | hd::tl ->
    fun (x:td_as_type hd) ->
    pre_rel_generic #max_arity #arg_reg code tl IX64.(x ++ args) (elim_1 pre x)

[@__reduce__]
let rec post_rel_generic
    (#max_arity:nat)
    (code:V.va_code)
    (dom:list td)
    (args:list arg{List.length dom + List.length args <= 20})
    (post:VSig.vale_post_tl dom)
  : IX64.rel_gen_t code dom args (IX64.prediction_post_rel_t (coerce code))
  =
  match dom with
  | [] ->
    prediction_post_rel #max_arity post (coerce code) args
  | hd::tl ->
    fun (x:td_as_type hd) ->
    post_rel_generic #max_arity code tl IX64.(x ++ args) (elim_1 post x)

let rec mk_prediction
    (#max_arity:nat)
    (#arg_reg:IX64.arg_reg_relation max_arity)
    (#regs_modified:MS.reg_64 -> bool)
    (#xmms_modified:MS.reg_xmm -> bool)
    (code:V.va_code)
    (dom:list td)
    (args:list arg{List.length dom + List.length args <= 20})
    (#pre:VSig.vale_pre_tl dom)
    (#post:VSig.vale_post_tl dom)
    (v:VSig.vale_sig_tl regs_modified xmms_modified args (coerce code) pre post)
  : IX64.prediction_t
      max_arity
      arg_reg
      regs_modified
      xmms_modified
      (coerce code)
      dom
      args
      (pre_rel_generic #max_arity #arg_reg code dom args pre)
      (post_rel_generic #max_arity code dom args post)
  =
  let open IX64 in
  match dom with
  | [] ->
    vale_lemma_as_prediction #max_arity #arg_reg _ _ _ _ v
  | hd::tl ->
    fun (x:td_as_type hd) ->
    mk_prediction
      #max_arity
      #arg_reg
      code
      tl
      (x ++ args)
      #(elim_1 pre x)
      #(elim_1 post x)
      (VSig.elim_vale_sig_cons hd tl args pre post v x)
