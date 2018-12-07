module Vale.AsLowStar.ValeSig
open Vale.AsLowStar.Signature
open Vale.AsLowStar.Util
module B = LowStar.Buffer
module BV = LowStar.BufferView
module HS = FStar.HyperStack
module IA = Interop_assumptions
module IS = X64.Interop_s
module ME = X64.Memory
module MS = X64.Machine_s
module V = X64.Vale.Decls
module VS = X64.Vale.State

[@IS.reduce]
let vale_pre_tl (dom:sig) =
    IS.n_arrow dom (V.va_state -> IS.stack_buffer -> prop)

[@IS.reduce]
let vale_pre (dom:sig) =
    code:V.va_code ->
    win:bool ->
    vale_pre_tl dom

[@IS.reduce]
let vale_post_tl (dom:sig) =
    IS.n_arrow dom
               (s0:V.va_state -> sb:IS.stack_buffer -> s1:V.va_state -> f:V.va_fuel -> prop)

[@IS.reduce]
let vale_post (dom:sig) =
    code:V.va_code ->
    win:bool ->
    vale_post_tl dom

let vale_save_reg (r:MS.reg) (s0 s1:V.va_state) =
  VS.eval_reg r s0 == VS.eval_reg r s1

let vale_save_xmm (r:MS.xmm) (s0 s1:V.va_state) =
  VS.eval_xmm r s0 == VS.eval_xmm r s1

let vale_calling_conventions (win:bool) (s0 s1:V.va_state) =
  let open MS in
  vale_save_reg Rbx s0 s1 /\
  (win ==> vale_save_reg Rsi s0 s1) /\
  (win ==> vale_save_reg Rdi s0 s1) /\
  vale_save_reg Rbp s0 s1 /\
  (win ==> vale_save_reg Rsp s0 s1) /\ // TODO: also needed for !win
  vale_save_reg R12 s0 s1 /\
  vale_save_reg R13 s0 s1 /\
  vale_save_reg R14 s0 s1 /\
  vale_save_reg R15 s0 s1 /\
  (win ==>
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

let maybe_cons_buffer_fp
       (#t:IS.vale_type)
       (x:IS.vale_type_as_type t)
       (loc: ME.loc) =
    match t with
    | IS.VT_Base _ -> loc
    | IS.VT_Buffer bt -> ME.loc_union (ME.loc_buffer #(ME.TBase bt) x) loc

[@IS.reduce]
let rec vale_sig_tl (#dom:sig)
                    (fp:ME.loc)
                    (code:V.va_code)
                    (win:bool)
                    (pre:vale_pre_tl dom)
                    (post:vale_post_tl dom)
  : Type =
    match dom with
    | [] ->
      va_s0:V.va_state ->
      stack_b:IS.stack_buffer ->
      Ghost (V.va_state & V.va_fuel)
            (requires (IS.elim_nil pre va_s0 stack_b))
            (ensures (fun (va_s1, f) ->
                       V.eval_code code va_s0 f va_s1 /\
                       vale_calling_conventions win va_s0 va_s1 /\
                       IS.elim_nil post va_s0 stack_b va_s1 f /\
                       ME.modifies fp va_s0.VS.mem va_s1.VS.mem))

    | hd::tl ->
      x:IS.vale_type_as_type hd ->
      vale_sig_tl #tl (maybe_cons_buffer_fp x fp) code win (IS.elim_1 pre x) (IS.elim_1 post x)

[@IS.reduce]
let elim_vale_sig_cons #code
                       (hd:IS.vale_type)
                       (tl:sig)
                       (fp:ME.loc)
                       (pre:vale_pre_tl (hd::tl))
                       (post:vale_post_tl (hd::tl))
                       (v:vale_sig_tl fp code IA.win pre post)
    : x:IS.vale_type_as_type hd
    -> vale_sig_tl (maybe_cons_buffer_fp x fp) code IA.win (IS.elim_1 pre x) (IS.elim_1 post x)
    = v

[@IS.reduce]
let vale_sig (#dom:sig)
             (pre:vale_pre dom)
             (post:vale_post dom)
  : Type =
    code:V.va_code ->
    win:bool ->
    vale_sig_tl
      ME.loc_none
      code
      win
      (pre code win)
      (post code win)
