module Vale.Inline.X64.Fmul_inline

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
let fmul_dom: IX64.arity_ok 4 td =
  let y = [t64_mod; t64_no_mod; t64_no_mod; t64_mod] in
  assert_norm (List.length y = 4);
  y

(* Need to rearrange the order of arguments *)
[@__reduce__]
let fmul_pre : VSig.vale_pre fmul_dom =
  fun (c:V.va_code)
    (out:b64)
    (f1:b64)
    (f2:b64)
    (tmp:b64)
    (va_s0:V.va_state) ->
      FW.va_req_Fmul c va_s0
        (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out) (as_vale_buffer f2)

[@__reduce__]
let fmul_post : VSig.vale_post fmul_dom =
  fun (c:V.va_code)
    (out:b64)
    (f1:b64)
    (f2:b64)
    (tmp:b64)
    (va_s0:V.va_state)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      FW.va_ens_Fmul c va_s0 (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out) (as_vale_buffer f2) va_s1 f

let fmul_regs_modified: MS.reg_64 -> bool = fun (r:MS.reg_64) ->
  let open MS in
  if r = rRax || r = rRcx || r = rRdx || r = rRdi || r = rRsi || r = rR8 || r = rR9 || r = rR10 || r = rR11 || r = rR12 || r = rR13 || r = rR14 || r = rR15 then true
  else false

let fmul_xmms_modified = fun _ -> false

#set-options "--z3rlimit 200"

[@__reduce__]
let fmul_lemma'
    (code:V.va_code)
    (_win:bool)
    (out:b64)
    (f1:b64)
    (f2:b64)
    (tmp:b64)
    (va_s0:V.va_state)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       fmul_pre code out f1 f2 tmp va_s0)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions va_s0 va_s1 fmul_regs_modified fmul_xmms_modified /\
       fmul_post code out f1 f2 tmp va_s0 va_s1 f /\
       ME.buffer_readable (VS.vs_get_vale_heap va_s1) (as_vale_buffer out) /\
       ME.buffer_readable (VS.vs_get_vale_heap va_s1) (as_vale_buffer f1) /\
       ME.buffer_readable (VS.vs_get_vale_heap va_s1) (as_vale_buffer f2) /\
       ME.buffer_readable (VS.vs_get_vale_heap va_s1) (as_vale_buffer tmp) /\
       ME.buffer_writeable (as_vale_buffer out) /\
       ME.buffer_writeable (as_vale_buffer f1) /\
       ME.buffer_writeable (as_vale_buffer f2) /\
       ME.buffer_writeable (as_vale_buffer tmp) /\
       ME.modifies (ME.loc_union (ME.loc_buffer (as_vale_buffer out))
                   (ME.loc_union (ME.loc_buffer (as_vale_buffer tmp))
                                 ME.loc_none)) (VS.vs_get_vale_heap va_s0) (VS.vs_get_vale_heap va_s1)
 )) =
   let va_s1, f = FW.va_lemma_Fmul code va_s0 (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out) (as_vale_buffer f2) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 out;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 f1;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 f2;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 tmp;
   (va_s1, f)

(* Prove that fmul_lemma' has the required type *)
let fmul_lemma = as_t #(VSig.vale_sig fmul_regs_modified fmul_xmms_modified fmul_pre fmul_post) fmul_lemma'
let code_Fmul = FW.va_code_Fmul ()

let fmul_of_reg (r:MS.reg_64) : option (IX64.reg_nat 4) = match r with
  | 15 -> Some 0 // r15
  | 4 -> Some 1 // rsi
  | 2 -> Some 2 // rcx
  | 5 -> Some 3 // rdi
  | _ -> None

let fmul_of_arg (i:IX64.reg_nat 4) : MS.reg_64 = match i with
  | 0 -> MS.rR15
  | 1 -> MS.rRsi
  | 2 -> MS.rRcx
  | 3 -> MS.rRdi

let fmul_arg_reg : IX64.arg_reg_relation 4 = IX64.Rel fmul_of_reg fmul_of_arg

(* Here's the type expected for the fmul wrapper *)
[@__reduce__] noextract
let lowstar_fmul_t =
  assert_norm (List.length fmul_dom + List.length ([]<:list arg) <= 4);
  IX64.as_lowstar_sig_t_weak
    4
    fmul_arg_reg
    fmul_regs_modified
    fmul_xmms_modified
    code_Fmul
    fmul_dom
    []
    _
    _
    (W.mk_prediction code_Fmul fmul_dom [] (fmul_lemma code_Fmul IA.win))

(* And here's the fmul wrapper itself *)
let lowstar_fmul : lowstar_fmul_t  =
  assert_norm (List.length fmul_dom + List.length ([]<:list arg) <= 4);
  IX64.wrap_weak
    4
    fmul_arg_reg
    fmul_regs_modified
    fmul_xmms_modified
    code_Fmul
    fmul_dom
    (W.mk_prediction code_Fmul fmul_dom [] (fmul_lemma code_Fmul IA.win))

let lowstar_fmul_normal_t : normal lowstar_fmul_t
  = as_normal_t #lowstar_fmul_t lowstar_fmul

open Vale.AsLowStar.MemoryHelpers

#push-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 200"

let math_aux (n:nat) : Lemma ((n*8)/8 = n) = ()

let fmul out f1 f2 tmp =
    DV.length_eq (get_downview out);
    DV.length_eq (get_downview f1);
    DV.length_eq (get_downview tmp);
    DV.length_eq (get_downview f2);
    math_aux (B.length tmp);
    math_aux (B.length out);
    Vale.AsLowStar.MemoryHelpers.as_vale_buffer_len #TUInt64 #TUInt64 tmp;
    Vale.AsLowStar.MemoryHelpers.as_vale_buffer_len #TUInt64 #TUInt64 out;
    let (x, _) = lowstar_fmul_normal_t out f1 f2 tmp () in
    ()

#pop-options

let fmul_comments : list string =
  ["Computes a field multiplication: out <- f1 * f2";
   "Uses the 8-element buffer tmp for intermediate results"]

let fmul_names (n:nat) =
  match n with
  | 0 -> "out"
  | 1 -> "f1"
  | 2 -> "f2"
  | 3 -> "tmp"
  | _ -> ""

let fmul_code_inline () : FStar.All.ML int =
  PR.print_inline "fmul" 0 None (List.length fmul_dom) fmul_dom fmul_names code_Fmul fmul_of_arg fmul_regs_modified fmul_comments

(* Need to rearrange the order of arguments *)
[@__reduce__]
let fmul2_pre : VSig.vale_pre fmul_dom =
  fun (c:V.va_code)
    (out:b64)
    (f1:b64)
    (f2:b64)
    (tmp:b64)
    (va_s0:V.va_state) ->
      FW.va_req_Fmul2 c va_s0
        (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out) (as_vale_buffer f2)

[@__reduce__]
let fmul2_post : VSig.vale_post fmul_dom =
  fun (c:V.va_code)
    (out:b64)
    (f1:b64)
    (f2:b64)
    (tmp:b64)
    (va_s0:V.va_state)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      FW.va_ens_Fmul2 c va_s0 (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out) (as_vale_buffer f2) va_s1 f

#set-options "--z3rlimit 200"

[@__reduce__]
let fmul2_lemma'
    (code:V.va_code)
    (_win:bool)
    (out:b64)
    (f1:b64)
    (f2:b64)
    (tmp:b64)
    (va_s0:V.va_state)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       fmul2_pre code out f1 f2 tmp va_s0)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions va_s0 va_s1 fmul_regs_modified fmul_xmms_modified /\
       fmul2_post code out f1 f2 tmp va_s0 va_s1 f /\
       ME.buffer_readable (VS.vs_get_vale_heap va_s1) (as_vale_buffer out) /\
       ME.buffer_readable (VS.vs_get_vale_heap va_s1) (as_vale_buffer f1) /\
       ME.buffer_readable (VS.vs_get_vale_heap va_s1) (as_vale_buffer f2) /\
       ME.buffer_readable (VS.vs_get_vale_heap va_s1) (as_vale_buffer tmp) /\
       ME.buffer_writeable (as_vale_buffer out) /\
       ME.buffer_writeable (as_vale_buffer f1) /\
       ME.buffer_writeable (as_vale_buffer f2) /\
       ME.buffer_writeable (as_vale_buffer tmp) /\
       ME.modifies (ME.loc_union (ME.loc_buffer (as_vale_buffer out))
                   (ME.loc_union (ME.loc_buffer (as_vale_buffer tmp))
                                 ME.loc_none)) (VS.vs_get_vale_heap va_s0) (VS.vs_get_vale_heap va_s1)
 )) =
   let va_s1, f = FW.va_lemma_Fmul2 code va_s0 (as_vale_buffer tmp) (as_vale_buffer f1) (as_vale_buffer out) (as_vale_buffer f2) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 out;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 f1;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 f2;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 tmp;
   (va_s1, f)

(* Prove that fmul2_lemma' has the required type *)
let fmul2_lemma = as_t #(VSig.vale_sig fmul_regs_modified fmul_xmms_modified fmul2_pre fmul2_post) fmul2_lemma'
let code_Fmul2 = FW.va_code_Fmul2 ()

(* Here's the type expected for the fmul wrapper *)
[@__reduce__]
let lowstar_fmul2_t =
  assert_norm (List.length fmul_dom + List.length ([]<:list arg) <= 4);
  IX64.as_lowstar_sig_t_weak
    4
    fmul_arg_reg
    fmul_regs_modified
    fmul_xmms_modified
    code_Fmul2
    fmul_dom
    []
    _
    _
    (W.mk_prediction code_Fmul2 fmul_dom [] (fmul2_lemma code_Fmul2 IA.win))

(* And here's the fmul2 wrapper itself *)
let lowstar_fmul2 : lowstar_fmul2_t  =
  assert_norm (List.length fmul_dom + List.length ([]<:list arg) <= 4);
  IX64.wrap_weak
    4
    fmul_arg_reg
    fmul_regs_modified
    fmul_xmms_modified
    code_Fmul2
    fmul_dom
    (W.mk_prediction code_Fmul2 fmul_dom [] (fmul2_lemma code_Fmul2 IA.win))

let lowstar_fmul2_normal_t : normal lowstar_fmul2_t
  = as_normal_t #lowstar_fmul2_t lowstar_fmul2

#push-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 200"

let fmul2 out f1 f2 tmp =
    DV.length_eq (get_downview out);
    DV.length_eq (get_downview f1);
    DV.length_eq (get_downview tmp);
    DV.length_eq (get_downview f2);
    let (x, _) = lowstar_fmul2_normal_t out f1 f2 tmp () in
    ()

#pop-options

let fmul2_comments : list string = [
  "Computes two field multiplications:";
  "  out[0] <- f1[0] * f2[0]";
  "  out[1] <- f1[1] * f2[1]";
  "Uses the 16-element buffer tmp for intermediate results:"]

let fmul2_names (n:nat) =
  match n with
  | 0 -> "out"
  | 1 -> "f1"
  | 2 -> "f2"
  | 3 -> "tmp"
  | _ -> ""

let fmul2_code_inline () : FStar.All.ML int =
  PR.print_inline "fmul2" 0 None (List.length fmul_dom) fmul_dom fmul2_names code_Fmul2 fmul_of_arg fmul_regs_modified fmul2_comments

[@__reduce__]
let fmul1_dom: IX64.arity_ok 3 td =
  let y = [t64_mod; t64_no_mod; tuint64] in
  assert_norm (List.length y = 3);
  y

(* Need to rearrange the order of arguments *)
[@__reduce__]
let fmul1_pre : VSig.vale_pre fmul1_dom =
  fun (c:V.va_code)
    (out:b64)
    (f1:b64)
    (f2:uint64)
    (va_s0:V.va_state) ->
      FH.va_req_Fmul1 c va_s0
        (as_vale_buffer out) (as_vale_buffer f1) (UInt64.v f2)

[@__reduce__]
let fmul1_post : VSig.vale_post fmul1_dom =
  fun (c:V.va_code)
    (out:b64)
    (f1:b64)
    (f2:uint64)
    (va_s0:V.va_state)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      FH.va_ens_Fmul1 c va_s0 (as_vale_buffer out) (as_vale_buffer f1) (UInt64.v f2) va_s1 f

#set-options "--z3rlimit 200"

let fmul1_regs_modified: MS.reg_64 -> bool = fun (r:MS.reg_64) ->
  let open MS in
  if r = rRax || r = rRcx || r = rRdx || r = rR8 || r = rR9 || r = rR10 || r = rR11 || r = rR12 || r = rR13 then true
  else false

let fmul1_xmms_modified = fun _ -> false

[@__reduce__]
let fmul1_lemma'
    (code:V.va_code)
    (_win:bool)
    (out:b64)
    (f1:b64)
    (f2:uint64)
    (va_s0:V.va_state)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       fmul1_pre code out f1 f2 va_s0)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions va_s0 va_s1 fmul1_regs_modified fmul1_xmms_modified /\
       fmul1_post code out f1 f2 va_s0 va_s1 f /\
       ME.buffer_readable (VS.vs_get_vale_heap va_s1) (as_vale_buffer f1) /\
       ME.buffer_readable (VS.vs_get_vale_heap va_s1) (as_vale_buffer out) /\
       ME.buffer_writeable (as_vale_buffer out) /\
       ME.buffer_writeable (as_vale_buffer f1) /\
       ME.modifies (ME.loc_union (ME.loc_buffer (as_vale_buffer out))
                                 ME.loc_none) (VS.vs_get_vale_heap va_s0) (VS.vs_get_vale_heap va_s1)
 )) =
   let va_s1, f = FH.va_lemma_Fmul1 code va_s0 (as_vale_buffer out) (as_vale_buffer f1) (UInt64.v f2) in
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 out;
   Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt64 ME.TUInt64 f1;
   (va_s1, f)

(* Prove that fmul1_lemma' has the required type *)
let fmul1_lemma = as_t #(VSig.vale_sig fmul1_regs_modified fmul1_xmms_modified fmul1_pre fmul1_post) fmul1_lemma'

let code_Fmul1 = FH.va_code_Fmul1 ()

let of_reg (r:MS.reg_64) : option (IX64.reg_nat 3) = match r with
  | 5 -> Some 0 // rdi
  | 4 -> Some 1 // rsi
  | 3 -> Some 2 // rdx
  | _ -> None

let of_arg (i:IX64.reg_nat 3) = match i with
  | 0 -> MS.rRdi
  | 1 -> MS.rRsi
  | 2 -> MS.rRdx

let arg_reg : IX64.arg_reg_relation 3 = IX64.Rel of_reg of_arg

(* Here's the type expected for the fmul1 wrapper *)
[@__reduce__]
let lowstar_fmul1_t =
  assert_norm (List.length fmul1_dom + List.length ([]<:list arg) <= 3);
  IX64.as_lowstar_sig_t_weak
    3
    arg_reg
    fmul1_regs_modified
    fmul1_xmms_modified
    code_Fmul1
    fmul1_dom
    []
    _
    _
    // The boolean here doesn't matter
    (W.mk_prediction code_Fmul1 fmul1_dom [] (fmul1_lemma code_Fmul1 IA.win))

(* And here's the fmul1 wrapper itself *)
let lowstar_fmul1 : lowstar_fmul1_t  =
  assert_norm (List.length fmul1_dom + List.length ([]<:list arg) <= 3);
  IX64.wrap_weak
    3
    arg_reg
    fmul1_regs_modified
    fmul1_xmms_modified
    code_Fmul1
    fmul1_dom
    (W.mk_prediction code_Fmul1 fmul1_dom [] (fmul1_lemma code_Fmul1 IA.win))

let lowstar_fmul1_normal_t : normal lowstar_fmul1_t
  = as_normal_t #lowstar_fmul1_t lowstar_fmul1

open Vale.AsLowStar.MemoryHelpers

let fmul_scalar out f1 f2
  = DV.length_eq (get_downview out);
    DV.length_eq (get_downview f1);
    let (x, _) = lowstar_fmul1_normal_t out f1 f2 () in
    ()

let fmul1_comments : list string = 
  ["Computes the field multiplication of four-element f1 with value in f2"; "Requires f2 to be smaller than 2^17"]

let fmul1_names (n:nat) =
  match n with
  | 0 -> "out"
  | 1 -> "f1"
  | 2 -> "f2"
  | _ -> ""

let fmul1_code_inline () : FStar.All.ML int =
  PR.print_inline "fmul_scalar" 0 None (List.length fmul1_dom) fmul1_dom fmul1_names code_Fmul1 of_arg fmul1_regs_modified fmul1_comments
