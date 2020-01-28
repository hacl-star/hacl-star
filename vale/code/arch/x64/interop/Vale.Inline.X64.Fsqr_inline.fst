module Vale.Inline.X64.Fsqr_inline

open FStar.Mul
open FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer
module DV = LowStar.BufferView.Down
open Vale.Def.Types_s

open Vale.Interop.Base
module IX64 = Vale.Interop.X64
module VSig = Vale.AsLowStar.ValeSig
module LSig = Vale.AsLowStar.LowStarSig
module ME = Vale.X64.Memory
module V = Vale.X64.Decls
module IA = Vale.Interop.Assumptions
module W = Vale.AsLowStar.Wrapper
open Vale.X64.MemoryAdapters
module VS = Vale.X64.State
module MS = Vale.X64.Machine_s
open Vale.AsLowStar.MemoryHelpers
module PR = Vale.X64.Print_Inline_s

module FU = Vale.Curve25519.X64.FastUtil
module FH = Vale.Curve25519.X64.FastHybrid
module FW = Vale.Curve25519.X64.FastWide

let uint64 = UInt64.t

(* A little utility to trigger normalization in types *)
let as_t (#a:Type) (x:normal a) : a = x
let as_normal_t (#a:Type) (x:a) : normal a = x

[@__reduce__]
let b64 = buf_t TUInt64 TUInt64
[@__reduce__]
let t64_mod = TD_Buffer TUInt64 TUInt64 default_bq
[@__reduce__]
let t64_no_mod = TD_Buffer TUInt64 TUInt64 ({modified=false; strict_disjointness=false; taint=MS.Secret})
[@__reduce__]
let tuint64 = TD_Base TUInt64

[@__reduce__]
let fsqr_dom: IX64.arity_ok 3 td =
  let y = [t64_mod; t64_no_mod; t64_mod] in
  assert_norm (List.length y = 3);
  y

(* Need to rearrange the order of arguments *)
[@__reduce__]
let fsqr_pre : VSig.vale_pre fsqr_dom =
  fun (c:V.va_code)
    (out:b64)
    (f1:b64)
    (tmp:b64)
    (va_s0:V.va_state) ->
      FW.va_req_Fsqr c va_s0
        (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out)

[@__reduce__]
let fsqr_post : VSig.vale_post fsqr_dom =
  fun (c:V.va_code)
    (out:b64)
    (f1:b64)
    (tmp:b64)
    (va_s0:V.va_state)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      FW.va_ens_Fsqr c va_s0 (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out) va_s1 f

let fsqr_regs_modified: MS.reg_64 -> bool = fun (r:MS.reg_64) ->
  let open MS in
  if r = rRax || r = rRbx || r = rRcx || r = rRdx || r = rRdi || r = rRsi || r = rR8 || r = rR9 || r = rR10 || r = rR11 || r = rR12 || r = rR13 || r = rR14 || r = rR15 then true
  else false

let fsqr_xmms_modified = fun _ -> false

#set-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0"

[@__reduce__]
let fsqr_lemma'
    (code:V.va_code)
    (_win:bool)
    (out:b64)
    (f1:b64)
    (tmp:b64)
    (va_s0:V.va_state)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       fsqr_pre code out f1 tmp va_s0)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions va_s0 va_s1 fsqr_regs_modified fsqr_xmms_modified /\
       fsqr_post code out f1 tmp va_s0 va_s1 f /\
       ME.buffer_readable (VS.vs_get_vale_heap va_s1) (as_vale_buffer out) /\
       ME.buffer_readable (VS.vs_get_vale_heap va_s1) (as_vale_buffer f1) /\
       ME.buffer_readable (VS.vs_get_vale_heap va_s1) (as_vale_buffer tmp) /\
       ME.buffer_writeable (as_vale_buffer out) /\
       ME.buffer_writeable (as_vale_buffer f1) /\
       ME.buffer_writeable (as_vale_buffer tmp) /\
       ME.modifies (ME.loc_union (ME.loc_buffer (as_vale_buffer out))
                   (ME.loc_union (ME.loc_buffer (as_vale_buffer tmp))
                                 ME.loc_none)) (VS.vs_get_vale_heap va_s0) (VS.vs_get_vale_heap va_s1)
 )) =
   let va_s1, f = FW.va_lemma_Fsqr code va_s0 (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 out;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 f1;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 tmp;
   (va_s1, f)

(* Prove that fsqr_lemma' has the required type *)
let fsqr_lemma = as_t #(VSig.vale_sig fsqr_regs_modified fsqr_xmms_modified fsqr_pre fsqr_post) fsqr_lemma'
let code_Fsqr = FW.va_code_Fsqr ()

let of_reg (r:MS.reg_64) : option (IX64.reg_nat 3) = match r with
  | 1 -> Some 0 // rbx
  | 4 -> Some 1 // rsi
  | 5 -> Some 2 // rdi
  | _ -> None

let of_arg (i:IX64.reg_nat 3) : MS.reg_64 = match i with
  | 0 -> MS.rRbx
  | 1 -> MS.rRsi
  | 2 -> MS.rRdi

let arg_reg : IX64.arg_reg_relation 3 = IX64.Rel of_reg of_arg

(* Here's the type expected for the fsqr wrapper *)
[@__reduce__]
let lowstar_Fsqr_t =
  assert_norm (List.length fsqr_dom + List.length ([]<:list arg) <= 3);
  IX64.as_lowstar_sig_t_weak
    3
    arg_reg
    fsqr_regs_modified
    fsqr_xmms_modified
    code_Fsqr
    fsqr_dom
    []
    _
    _
    // The boolean here doesn't matter
    (W.mk_prediction code_Fsqr fsqr_dom [] (fsqr_lemma code_Fsqr IA.win))

(* And here's the fsqr wrapper itself *)
let lowstar_Fsqr : lowstar_Fsqr_t  =
  assert_norm (List.length fsqr_dom + List.length ([]<:list arg) <= 3);
  IX64.wrap_weak
    3
    arg_reg
    fsqr_regs_modified
    fsqr_xmms_modified
    code_Fsqr
    fsqr_dom
    (W.mk_prediction code_Fsqr fsqr_dom [] (fsqr_lemma code_Fsqr IA.win))

let lowstar_Fsqr_normal_t : normal lowstar_Fsqr_t
  = as_normal_t #lowstar_Fsqr_t lowstar_Fsqr

open Vale.AsLowStar.MemoryHelpers

let fsqr out f1 tmp =
    DV.length_eq (get_downview tmp);
    DV.length_eq (get_downview f1);
    DV.length_eq (get_downview out);
    as_vale_buffer_len #TUInt64 #TUInt64 tmp;
    as_vale_buffer_len #TUInt64 #TUInt64 f1;
    as_vale_buffer_len #TUInt64 #TUInt64 out;
    let (x, _) = lowstar_Fsqr_normal_t out f1 tmp () in
    ()

let fsqr_comments : list string = 
  ["Computes the square of a field element: out <- f * f";
   "Uses the 8-element buffer tmp for intermediate results"]

let fsqr_names (n:nat) =
  match n with
  | 0 -> "out"
  | 1 -> "f"
  | 2 -> "tmp"
  | _ -> ""

let fsqr_code_inline () : FStar.All.ML int =
  PR.print_inline "fsqr" 0 None (List.length fsqr_dom) fsqr_dom fsqr_names code_Fsqr of_arg fsqr_regs_modified fsqr_comments

(* Need to rearrange the order of arguments *)
[@__reduce__]
let fsqr2_pre : VSig.vale_pre fsqr_dom =
  fun (c:V.va_code)
    (out:b64)
    (f1:b64)
    (tmp:b64)
    (va_s0:V.va_state) ->
      FW.va_req_Fsqr2 c va_s0
        (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out)

[@__reduce__]
let fsqr2_post : VSig.vale_post fsqr_dom =
  fun (c:V.va_code)
    (out:b64)
    (f1:b64)
    (tmp:b64)
    (va_s0:V.va_state)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      FW.va_ens_Fsqr2 c va_s0 (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out) va_s1 f

#set-options "--z3rlimit 200"

[@__reduce__]
let fsqr2_lemma'
    (code:V.va_code)
    (_win:bool)
    (out:b64)
    (f1:b64)
    (tmp:b64)
    (va_s0:V.va_state)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       fsqr2_pre code out f1 tmp va_s0)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions va_s0 va_s1 fsqr_regs_modified fsqr_xmms_modified /\
       fsqr2_post code out f1 tmp va_s0 va_s1 f /\
       ME.buffer_readable (VS.vs_get_vale_heap va_s1) (as_vale_buffer out) /\
       ME.buffer_readable (VS.vs_get_vale_heap va_s1) (as_vale_buffer f1) /\
       ME.buffer_readable (VS.vs_get_vale_heap va_s1) (as_vale_buffer tmp) /\
       ME.buffer_writeable (as_vale_buffer out) /\
       ME.buffer_writeable (as_vale_buffer f1) /\
       ME.buffer_writeable (as_vale_buffer tmp) /\
       ME.modifies (ME.loc_union (ME.loc_buffer (as_vale_buffer out))
                   (ME.loc_union (ME.loc_buffer (as_vale_buffer tmp))
                                 ME.loc_none)) (VS.vs_get_vale_heap va_s0) (VS.vs_get_vale_heap va_s1)
 )) =
   let va_s1, f = FW.va_lemma_Fsqr2 code va_s0 (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 out;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 f1;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 tmp;
   (va_s1, f)

(* Prove that fsqr2_lemma' has the required type *)
let fsqr2_lemma = as_t #(VSig.vale_sig fsqr_regs_modified fsqr_xmms_modified fsqr2_pre fsqr2_post) fsqr2_lemma'
let code_Fsqr2 = FW.va_code_Fsqr2 ()

(* Here's the type expected for the fsqr2 wrapper *)
[@__reduce__]
let lowstar_Fsqr2_t =
  assert_norm (List.length fsqr_dom + List.length ([]<:list arg) <= 3);
  IX64.as_lowstar_sig_t_weak
    3
    arg_reg
    fsqr_regs_modified
    fsqr_xmms_modified
    code_Fsqr2
    fsqr_dom
    []
    _
    _
    (W.mk_prediction code_Fsqr2 fsqr_dom [] (fsqr2_lemma code_Fsqr2 IA.win))

(* And here's the fsqr2 wrapper itself *)
let lowstar_Fsqr2 : lowstar_Fsqr2_t  =
  assert_norm (List.length fsqr_dom + List.length ([]<:list arg) <= 3);
  IX64.wrap_weak
    3
    arg_reg
    fsqr_regs_modified
    fsqr_xmms_modified
    code_Fsqr2
    fsqr_dom
    (W.mk_prediction code_Fsqr2 fsqr_dom [] (fsqr2_lemma code_Fsqr2 IA.win))

let lowstar_Fsqr2_normal_t : normal lowstar_Fsqr2_t
  = as_normal_t #lowstar_Fsqr2_t lowstar_Fsqr2

open Vale.AsLowStar.MemoryHelpers

let fsqr2 out f1 tmp =
    DV.length_eq (get_downview tmp);
    DV.length_eq (get_downview f1);
    DV.length_eq (get_downview out);
    let (x, _) = lowstar_Fsqr2_normal_t out f1 tmp () in
    ()

let fsqr2_comments : list string = 
  ["Computes two field squarings:";
   "  out[0] <- f[0] * f[0]";
   "  out[1] <- f[1] * f[1]";
   "Uses the 16-element buffer tmp for intermediate results"
  ]

let fsqr2_names (n:nat) : string =
  match n with
  | 0 -> "out"
  | 1 -> "f"
  | 2 -> "tmp"
  | _ -> ""

let fsqr2_code_inline () : FStar.All.ML int =
  PR.print_inline "fsqr2" 0 None (List.length fsqr_dom) fsqr_dom fsqr2_names code_Fsqr2 of_arg fsqr_regs_modified fsqr2_comments
