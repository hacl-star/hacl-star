module Vale.AsLowStar.ValeSig
open FStar.Mul
open Vale.Arch.HeapImpl
open Vale.Interop.Base
module B = LowStar.Buffer
module BS = Vale.X64.Machine_Semantics_s
module BV = LowStar.BufferView
module HS = FStar.HyperStack
module ME = Vale.X64.Memory
module MS = Vale.X64.Machine_s
module IA = Vale.Interop.Assumptions
module V = Vale.X64.Decls
module VS = Vale.X64.State
module IX64 = Vale.Interop.X64
module List = FStar.List.Tot
module Map16 = Vale.Lib.Map16
open Vale.X64.MemoryAdapters

[@__reduce__]
let vale_pre_tl (dom:list td) =
    n_arrow dom (V.va_state -> prop)

[@__reduce__]
let vale_pre (dom:list td) =
    code:V.va_code ->
    vale_pre_tl dom

[@__reduce__]
let vale_post_tl (dom:list td) =
    n_arrow dom
            (s0:V.va_state -> s1:V.va_state -> f:V.va_fuel -> prop)

[@__reduce__]
let vale_post (dom:list td) =
    code:V.va_code ->
    vale_post_tl dom

let vale_save_reg (r:MS.reg_64) (s0 s1:V.va_state) =
  VS.eval_reg_64 r s0 == VS.eval_reg_64 r s1

let vale_save_xmm (r:MS.reg_xmm) (s0 s1:V.va_state) =
  VS.eval_reg_xmm r s0 == VS.eval_reg_xmm r s1

let vale_calling_conventions
  (s0 s1:V.va_state)
  (regs_modified:MS.reg_64 -> bool)
  (xmms_modified:MS.reg_xmm -> bool) =
  let open MS in
  s1.VS.vs_ok /\
  vale_save_reg MS.rRsp s0 s1 /\
  (forall (r:MS.reg_64).
    not (regs_modified r) ==> vale_save_reg r s0 s1) /\
  (forall (x:MS.reg_xmm).
    not (xmms_modified x) ==> vale_save_xmm x s0 s1)

[@__reduce__]
let modified_arg_mloc (x:arg) : GTot ME.loc =
    match x with
    | (|TD_Buffer src t {modified=true}, x|) -> ME.loc_buffer (as_vale_buffer #src #t x)
    | _ -> ME.loc_none

[@__reduce__]
let mloc_modified_args (args:list arg) : GTot ME.loc =
    List.fold_right_gtot (List.map_gtot modified_arg_mloc args) ME.loc_union ME.loc_none

let state_of (x:(V.va_state & V.va_fuel)) = fst x
let fuel_of (x:(V.va_state & V.va_fuel)) = snd x
let sprop = VS.vale_state -> prop


[@__reduce__]
let readable_one (s:ME.vale_heap) (arg:arg) : prop =
  match arg with
  | (|TD_Buffer src bt _, x |) ->
    ME.buffer_readable s (as_vale_buffer #src #bt x) /\
    ME.buffer_writeable (as_vale_buffer #src #bt x)
    /\ True //promote to prop
  | (|TD_ImmBuffer src bt _, x |) ->
    ME.buffer_readable s (as_vale_immbuffer #src #bt x) /\
    True
  | _ -> True

[@__reduce__]
let readable (args:list arg) (s:ME.vale_heap) : prop =
    BigOps.big_and' (readable_one s) args


[@__reduce__]
let disjoint_or_eq_1 (a:arg) (b:arg) =
    match a, b with
    | (| TD_Buffer srcx tx {strict_disjointness=true}, xb |), (| TD_Buffer srcy ty _, yb |)
    | (| TD_Buffer srcx tx _, xb |), (| TD_Buffer srcy ty {strict_disjointness=true}, yb |) ->
      ME.loc_disjoint (ME.loc_buffer (as_vale_buffer #srcx #tx xb)) (ME.loc_buffer (as_vale_buffer #srcy #ty yb))
    | (| TD_ImmBuffer srcx tx {strict_disjointness=true}, xb |), (| TD_ImmBuffer srcy ty _, yb |)
    | (| TD_ImmBuffer srcx tx _, xb |), (| TD_ImmBuffer srcy ty {strict_disjointness=true}, yb |) ->
      ME.loc_disjoint (ME.loc_buffer (as_vale_immbuffer #srcx #tx xb)) (ME.loc_buffer (as_vale_immbuffer #srcy #ty yb))
    // An immutable buffer and a trivial buffer should not be equal
    | (| TD_ImmBuffer srcx tx _, xb |), (| TD_Buffer srcy ty _, yb |) ->
      ME.loc_disjoint (ME.loc_buffer (as_vale_immbuffer #srcx #tx xb)) (ME.loc_buffer (as_vale_buffer #srcy #ty yb))
    | (| TD_Buffer srcx tx _, xb |), (| TD_ImmBuffer srcy ty _, yb |) ->
      ME.loc_disjoint (ME.loc_buffer (as_vale_buffer #srcx #tx xb)) (ME.loc_buffer (as_vale_immbuffer #srcy #ty yb))
    | (| TD_Buffer srcx tx _, xb |), (| TD_Buffer srcy ty _, yb |) ->
      ME.loc_disjoint (ME.loc_buffer (as_vale_buffer #srcx #tx xb)) (ME.loc_buffer (as_vale_buffer #srcy #ty yb)) \/
      eq3 xb yb
    | (| TD_ImmBuffer srcx tx _, xb |), (| TD_ImmBuffer srcy ty _, yb |) ->
      ME.loc_disjoint (ME.loc_buffer (as_vale_immbuffer #srcx #tx xb)) (ME.loc_buffer (as_vale_immbuffer #srcy #ty yb)) \/
      eq3 xb yb
    | _ -> True

[@__reduce__]
let disjoint_or_eq (l:list arg) =
  BigOps.pairwise_and' disjoint_or_eq_1  l

[@__reduce__] unfold
let vale_sig_nil
                 (regs_modified:MS.reg_64 -> bool)
                 (xmms_modified:MS.reg_xmm -> bool)
                 (args:list arg)
                 (code:V.va_code)
                 (pre:vale_pre_tl [])
                 (post:vale_post_tl []) =
    va_s0:V.va_state ->
    Ghost (V.va_state & V.va_fuel)
     (requires
       elim_nil pre va_s0)
     (ensures (fun r ->
       let va_s1 = state_of r in
       let f = fuel_of r in
       V.eval_code code va_s0 f va_s1 /\
       vale_calling_conventions va_s0 va_s1 regs_modified xmms_modified /\
       elim_nil post va_s0 va_s1 f /\
       readable args (ME.get_vale_heap va_s1.VS.vs_heap) /\
       ME.modifies (mloc_modified_args args) (VS.vs_get_vale_heap va_s0) (VS.vs_get_vale_heap va_s1)))

[@__reduce__]
let rec vale_sig_tl (regs_modified:MS.reg_64 -> bool)
                    (xmms_modified:MS.reg_xmm -> bool)
                    (#dom:list td)
                    (args:list arg)
                    (code:V.va_code)
                    (pre:vale_pre_tl dom)
                    (post:vale_post_tl dom)
  : Type =
    match dom with
    | [] ->
      vale_sig_nil regs_modified xmms_modified args code pre post

    | hd::tl ->
      x:td_as_type hd ->
      vale_sig_tl regs_modified xmms_modified #tl ((|hd,x|)::args) code (elim_1 pre x) (elim_1 post x)

[@__reduce__]
let elim_vale_sig_nil  #code
                       (#regs_modified:MS.reg_64 -> bool)
                       (#xmms_modified:MS.reg_xmm -> bool)
                       (#args:list arg)
                       (#pre:vale_pre_tl [])
                       (#post:vale_post_tl [])
                       (v:vale_sig_tl regs_modified xmms_modified #[] args code pre post)
    : vale_sig_nil regs_modified xmms_modified args code pre post
    = v

[@__reduce__]
let elim_vale_sig_cons #code
                       (#regs_modified:MS.reg_64 -> bool)
                       (#xmms_modified:MS.reg_xmm -> bool)
                       (hd:td)
                       (tl:list td)
                       (args:list arg)
                       (pre:vale_pre_tl (hd::tl))
                       (post:vale_post_tl (hd::tl))
                       (v:vale_sig_tl regs_modified xmms_modified args code pre post)
    : x:td_as_type hd
    -> vale_sig_tl regs_modified xmms_modified ((|hd, x|)::args) code (elim_1 pre x) (elim_1 post x)
    = v

[@__reduce__]
let vale_sig (#dom:list td)
             (regs_modified:MS.reg_64 -> bool)
             (xmms_modified:MS.reg_xmm -> bool)
             (pre:vale_pre dom)
             (post:vale_post dom)
  : Type =
    code:V.va_code ->
    win:bool ->
    vale_sig_tl
      regs_modified
      xmms_modified
      []
      code
      (pre code)
      (post code)

[@__reduce__]
let vale_sig_stdcall #dom = vale_sig #dom IX64.regs_modified_stdcall IX64.xmms_modified_stdcall

[@__reduce__]
let vale_calling_conventions_stdcall (s0 s1:VS.vale_state) =
  vale_calling_conventions s0 s1 IX64.regs_modified_stdcall IX64.xmms_modified_stdcall
