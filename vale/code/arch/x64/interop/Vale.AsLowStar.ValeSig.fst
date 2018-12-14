module Vale.AsLowStar.ValeSig
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

assume
val code_equiv : squash (V.va_code == TS.tainted_code)

[@reduce]
let vale_pre_tl (dom:list td) =
    n_arrow dom (V.va_state -> IX64.stack_buffer -> prop)

[@reduce]
let vale_pre (dom:list td) =
    code:V.va_code ->
    vale_pre_tl dom

[@reduce]
let vale_post_tl (dom:list td) =
    n_arrow dom
               (s0:V.va_state -> sb:IX64.stack_buffer -> s1:V.va_state -> f:V.va_fuel -> prop)

[@reduce]
let vale_post (dom:list td) =
    code:V.va_code ->
    vale_post_tl dom

let vale_save_reg (r:MS.reg) (s0 s1:V.va_state) =
  VS.eval_reg r s0 == VS.eval_reg r s1

let vale_save_xmm (r:MS.xmm) (s0 s1:V.va_state) =
  VS.eval_xmm r s0 == VS.eval_xmm r s1

let vale_calling_conventions (s0 s1:V.va_state) =
  let open MS in
  vale_save_reg Rbx s0 s1 /\
  (IA.win ==> vale_save_reg Rsi s0 s1) /\
  (IA.win ==> vale_save_reg Rdi s0 s1) /\
  vale_save_reg Rbp s0 s1 /\
  (IA.win ==> vale_save_reg Rsp s0 s1) /\ // TODO: also needed for !IA.win
  vale_save_reg R12 s0 s1 /\
  vale_save_reg R13 s0 s1 /\
  vale_save_reg R14 s0 s1 /\
  vale_save_reg R15 s0 s1 /\
  (IA.win ==>
    vale_save_xmm 6 s0 s1 /\
    vale_save_xmm 7 s0 s1 /\
    vale_save_xmm 8 s0 s1 /\
    vale_save_xmm 9 s0 s1 /\
    vale_save_xmm 10 s0 s1 /\
    vale_save_xmm 11 s0 s1 /\
    vale_save_xmm 12 s0 s1 /\
    vale_save_xmm 13 s0 s1 /\
    vale_save_xmm 14 s0 s1 /\
    vale_save_xmm 15 s0 s1
  ) /\
  s1.VS.ok


[@reduce]
let arg_mloc (x:arg) : GTot ME.loc =
    match x with
    | (|TD_Buffer td, x|) -> ME.loc_buffer (as_vale_buffer #(ME.TBase td) x)
    | _ -> ME.loc_none

[@reduce]
let mloc_args (args:list arg) : GTot ME.loc =
    BigOps.foldr_gtot (BigOps.map_gtot arg_mloc args) ME.loc_union ME.loc_none

unfold
let vale_sig_nil (args:list arg)
                 (code:V.va_code)
                 (pre:vale_pre_tl [])
                 (post:vale_post_tl []) =
    va_s0:V.va_state ->
    stack_b:IX64.stack_buffer ->
    Ghost (V.va_state & V.va_fuel)
     (requires
       elim_nil pre va_s0 stack_b)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       vale_calling_conventions va_s0 va_s1 /\
       elim_nil post va_s0 stack_b va_s1 f /\
       ME.modifies (mloc_args args) va_s0.VS.mem va_s1.VS.mem))

[@reduce]
let rec vale_sig_tl (#dom:list td)
                    (args:list arg)
                    (code:V.va_code)
                    (pre:vale_pre_tl dom)
                    (post:vale_post_tl dom)
  : Type =
    match dom with
    | [] ->
      vale_sig_nil args code pre post

    | hd::tl ->
      x:td_as_type hd ->
      vale_sig_tl #tl ((|hd,x|)::args) code (elim_1 pre x) (elim_1 post x)


[@reduce]
let elim_vale_sig_nil #code
                       (#args:list arg)
                       (#pre:vale_pre_tl [])
                       (#post:vale_post_tl [])
                       (v:vale_sig_tl #[] args code pre post)
    : vale_sig_nil args code pre post
    = v

[@reduce]
let elim_vale_sig_cons #code
                       (hd:td)
                       (tl:list td)
                       (args:list arg)
                       (pre:vale_pre_tl (hd::tl))
                       (post:vale_post_tl (hd::tl))
                       (v:vale_sig_tl args code pre post)
    : x:td_as_type hd
    -> vale_sig_tl ((|hd, x|)::args) code (elim_1 pre x) (elim_1 post x)
    = v

[@reduce]
let vale_sig (#dom:list td)
             (pre:vale_pre dom)
             (post:vale_post dom)
  : Type =
    code:V.va_code ->
    win:bool ->
    vale_sig_tl
      []
      code
      (pre code)
      (post code)
