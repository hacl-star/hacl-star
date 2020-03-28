module Vale.AsLowStar.Test
open FStar.Mul
open Vale.Interop.Base
module ME = Vale.X64.Memory
module IA = Vale.Interop.Assumptions
module V = Vale.X64.Decls
module IX64 = Vale.Interop.X64
module VSig = Vale.AsLowStar.ValeSig
module LSig = Vale.AsLowStar.LowStarSig
module W = Vale.AsLowStar.Wrapper
module VS = Vale.X64.State
module MS = Vale.X64.Machine_s
(* A little utility to trigger normalization in types *)
let as_t (#a:Type) (x:normal a) : a = x
let as_normal_t (#a:Type) (x:a) : normal a = x

////////////////////////////////////////////////////////////////////////////////
//First a little standalone, toy experiment
[@__reduce__]
let b64 = buf_t TUInt8 TUInt64
[@__reduce__]
let ib64 = ibuf_t TUInt8 TUInt64
[@__reduce__]
let t64_mod = TD_Buffer TUInt8 TUInt64 default_bq
[@__reduce__]
let t64_no_mod = TD_Buffer TUInt8 TUInt64 ({modified=false; strict_disjointness=false; taint=MS.Secret})
[@__reduce__]
let t64_imm = TD_ImmBuffer TUInt8 TUInt64 ({modified=false; strict_disjointness=false; taint=MS.Secret})

[@__reduce__]
let (dom : list td{List.length dom <= 20}) =
  let y = [t64_mod;t64_imm] in
  assert_norm (List.length y = 2);
  y

assume val pre : VSig.vale_pre dom
assume val post : VSig.vale_post dom
assume val v: VSig.vale_sig_stdcall pre post
assume val c: V.va_code

[@__reduce__]
let call_c_t = IX64.as_lowstar_sig_t_weak_stdcall c dom [] _ _ (W.mk_prediction c dom [] (v c IA.win))


let call_c : call_c_t = IX64.wrap_weak_stdcall
  c dom (W.mk_prediction c dom [] (v c IA.win))

let call_c_normal_t : normal call_c_t = as_normal_t #call_c_t call_c
//You can ask emacs to show you the type of call_c_normal_t ...

////////////////////////////////////////////////////////////////////////////////
//Now memcpy
module VM = Vale.Test.X64.Vale_memcpy

[@__reduce__]
let vm_dom = [t64_mod; t64_imm]
open Vale.X64.MemoryAdapters
(* Need to rearrange the order of arguments *)
[@__reduce__]
let vm_pre : VSig.vale_pre vm_dom =
  fun (c:V.va_code)
    (dst:b64)
    (src:ib64)
    (va_s0:V.va_state) ->
      VM.va_req_Memcpy c va_s0 IA.win (as_vale_buffer dst) (as_vale_immbuffer src)

[@__reduce__]
let vm_post : VSig.vale_post  vm_dom =
  fun (c:V.va_code)
    (dst:b64)
    (src:ib64)
    (va_s0:V.va_state)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      VM.va_ens_Memcpy c va_s0 IA.win (as_vale_buffer dst) (as_vale_immbuffer src) va_s1 f

module VS = Vale.X64.State
#reset-options "--print_effect_args --z3rlimit 200"

(* The vale lemma doesn't quite suffice to prove the modifies clause
   expected of the interop layer *)
[@__reduce__]
let vm_lemma'
    (code:V.va_code)
    (_win:bool)
    (dst:b64)
    (src:ib64)
    (va_s0:V.va_state)
  : Ghost (V.va_state & V.va_fuel)
    (requires
      vm_pre code dst src va_s0)
    (ensures (fun (va_s1, f) ->
      V.eval_code code va_s0 f va_s1 /\
      VSig.vale_calling_conventions_stdcall va_s0 va_s1 /\
      vm_post code dst src va_s0 va_s1 f /\
      ME.buffer_readable (VS.vs_get_vale_heap va_s1) (as_vale_immbuffer src) /\
      ME.buffer_readable (VS.vs_get_vale_heap va_s1) (as_vale_buffer dst) /\
      ME.buffer_writeable (as_vale_buffer dst) /\
      ME.modifies (ME.loc_union (ME.loc_buffer (as_vale_buffer dst))
                                ME.loc_none) (VS.vs_get_vale_heap va_s0) (VS.vs_get_vale_heap va_s1)
    ))
  = 
  let va_s1, f = VM.va_lemma_Memcpy code va_s0 IA.win (as_vale_buffer dst) (as_vale_immbuffer src) in
  Vale.AsLowStar.MemoryHelpers.buffer_writeable_reveal ME.TUInt8 ME.TUInt64 dst;
  (va_s1, f)

(* Prove that vm_lemma' has the required type *)
let vm_lemma = as_t #(VSig.vale_sig_stdcall vm_pre vm_post) vm_lemma'

let code_Memcpy = VM.va_code_Memcpy IA.win

(* Here's the type expected for the memcpy wrapper *)
[@__reduce__]
let lowstar_Memcpy_t =
  IX64.as_lowstar_sig_t_weak_stdcall
    code_Memcpy
    vm_dom
    []
    _
    _
    (W.mk_prediction code_Memcpy vm_dom [] (vm_lemma code_Memcpy IA.win))

(* And here's the memcpy wrapper itself *)
let lowstar_Memcpy : lowstar_Memcpy_t  =
  IX64.wrap_weak_stdcall
    code_Memcpy
    vm_dom
    (W.mk_prediction code_Memcpy vm_dom [] (vm_lemma code_Memcpy IA.win))

let lowstar_Memcpy_normal_t //: normal lowstar_Memcpy_t
  = as_normal_t #lowstar_Memcpy_t lowstar_Memcpy

module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module MB = LowStar.Monotonic.Buffer
open FStar.HyperStack.ST

module M = Vale.X64.Memory

let test (x:b64) =
  assert (V.buffer_length (as_vale_buffer x) == (B.length x * view_n TUInt8) / view_n TUInt64);
  assert (V.buffer_length (as_vale_buffer x) == B.length x / 8)
let itest (x:ib64) =
  assert (V.buffer_length (as_vale_immbuffer x) == (B.length x * view_n TUInt8) / view_n TUInt64);
  assert (V.buffer_length (as_vale_immbuffer x) == B.length x / 8)

module T = FStar.Tactics
#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection'"
module LBV = LowStar.BufferView.Up
module DV = LowStar.BufferView.Down

let memcpy_Test
  (dst:B.buffer UInt8.t{B.length dst % 8 == 0})
  (src:IB.ibuffer UInt8.t{B.length src % 8 == 0})
  : Stack UInt64.t
    (requires fun h0 ->
      B.live h0 dst /\
      B.live h0 src /\
      B.disjoint dst src /\
      B.length dst == 16 /\
      B.length src == 16)
    (ensures fun h0 _ h1 ->
      B.modifies (B.loc_buffer dst) h0 h1 /\
      B.live h1 src /\
      B.live h1 dst)
//      B.as_seq h1 dst == B.as_seq h1 src)
//  by (T.dump "A") (* in case you want to look at the VC *)
  = IB.inhabited_immutable_buffer_is_distinct_from_buffer (UInt8.uint_to_t 0) src dst;
    let (x, _) = lowstar_Memcpy_normal_t dst src () in //This is a call to the interop wrapper
    let h1 = get () in
    // let v = Vale.Interop.Views.up_view64 in
    // assert (DV.length_eq (get_downview dst);
    //         DV.length_eq (get_downview src);
    //         Seq.equal (LBV.as_seq h1 (LBV.mk_buffer (get_downview dst) v))
    //                   (LBV.as_seq h1 (LBV.mk_buffer (get_downview src) v)));
    // lbv_as_seq_eq dst src Vale.Interop.Views.up_view64 h1; //And a lemma to rephrase the Vale postcondition
    x                                      //with equalities of buffer views
                                           //back to equalities of buffers

module VC = Vale.Lib.X64.Cpuidstdcall

[@__reduce__]
let empty_list #a : l:list a {List.length l = 0} = []

[@__reduce__]
let aesni_dom : IX64.arity_ok_stdcall td = []

(* Need to rearrange the order of arguments *)
[@__reduce__]
let aesni_pre : VSig.vale_pre aesni_dom =
  fun (c:V.va_code)
    (va_s0:V.va_state) ->
      VC.va_req_Check_aesni_stdcall c va_s0 IA.win

[@__reduce__]
let aesni_post : VSig.vale_post aesni_dom =
  fun (c:V.va_code)
    (va_s0:V.va_state)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      VC.va_ens_Check_aesni_stdcall c va_s0 IA.win va_s1 f

[@__reduce__]
let with_len (l:list 'a)
  : Pure (list 'a)
    (requires True)
    (ensures fun m -> m==l /\ List.length m == normalize_term (List.length l))
  = l

#set-options "--max_fuel 0 --max_ifuel 1 --z3rlimit_factor 2"
(* The vale lemma doesn't quite suffice to prove the modifies clause
   expected of the interop layer *)
[@__reduce__]
let aesni_lemma'
    (code:V.va_code)
    (_win:bool)
    (va_s0:V.va_state)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       aesni_pre code va_s0)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions_stdcall va_s0 va_s1 /\
       aesni_post code va_s0 va_s1 f))
 = VC.va_lemma_Check_aesni_stdcall code va_s0 IA.win

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit_factor 2"

(* Prove that vm_lemma' has the required type *)
let aesni_lemma = as_t #(VSig.vale_sig_stdcall aesni_pre aesni_post) aesni_lemma'

let code_aesni = VC.va_code_Check_aesni_stdcall IA.win

(* Here's the type expected for the check_aesni wrapper *)
[@__reduce__]
let lowstar_aesni_t =
  IX64.as_lowstar_sig_t_weak_stdcall
    (coerce code_aesni)
    aesni_dom
    empty_list
    _
    _
    (W.mk_prediction code_aesni aesni_dom [] (aesni_lemma code_aesni IA.win))

(* And here's the check_aesni wrapper itself *)
let lowstar_aesni : lowstar_aesni_t  =
  IX64.wrap_weak_stdcall
    (coerce code_aesni)
    aesni_dom
    (W.mk_prediction code_aesni aesni_dom [] (aesni_lemma code_aesni IA.win))

let lowstar_aesni_normal_t //: normal lowstar_aesni_t
  = as_normal_t #lowstar_aesni_t lowstar_aesni

open Vale.X64.CPU_Features_s

#set-options "--print_full_names"

let aesni_Test ()
  : Stack UInt64.t
    (requires fun h0 -> True)
    (ensures fun h0 ret_val h1 -> (UInt64.v ret_val) =!= 0 ==> aesni_enabled /\ pclmulqdq_enabled)
//  by (T.dump "A") (* in case you want to look at the VC *)
  =
  let (x, _) = lowstar_aesni_normal_t () in //This is a call to the interop wrapper
  x


module TA = Vale.Test.X64.Args

[@__reduce__]
let (ta_dom:list td{List.length ta_dom <= 20}) =
  let y = [t64_imm; t64_imm; t64_imm; t64_imm; t64_imm; t64_imm; t64_imm; t64_imm] in
  assert_norm (List.length y = 8);
  y

(* Need to rearrange the order of arguments *)
[@__reduce__]
let ta_pre : VSig.vale_pre ta_dom =
  fun (c:V.va_code)
    (arg0:ib64)
    (arg1:ib64)
    (arg2:ib64)
    (arg3:ib64)
    (arg4:ib64)
    (arg5:ib64)
    (arg6:ib64)
    (arg7:ib64)
    (va_s0:V.va_state) ->
      TA.va_req_Test c va_s0 IA.win
      (as_vale_immbuffer arg0)
      (as_vale_immbuffer arg1)
      (as_vale_immbuffer arg2)
      (as_vale_immbuffer arg3)
      (as_vale_immbuffer arg4)
      (as_vale_immbuffer arg5)
      (as_vale_immbuffer arg6)
      (as_vale_immbuffer arg7)

[@__reduce__]
let ta_post : VSig.vale_post ta_dom =
  fun (c:V.va_code)
    (arg0:ib64)
    (arg1:ib64)
    (arg2:ib64)
    (arg3:ib64)
    (arg4:ib64)
    (arg5:ib64)
    (arg6:ib64)
    (arg7:ib64)
    (va_s0:V.va_state)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      TA.va_ens_Test c va_s0 IA.win
      (as_vale_immbuffer arg0)
      (as_vale_immbuffer arg1)
      (as_vale_immbuffer arg2)
      (as_vale_immbuffer arg3)
      (as_vale_immbuffer arg4)
      (as_vale_immbuffer arg5)
      (as_vale_immbuffer arg6)
      (as_vale_immbuffer arg7)
      va_s1 f

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"
(* The vale lemma doesn't quite suffice to prove the modifies clause
   expected of the interop layer *)
[@__reduce__]
let ta_lemma'
    (code:V.va_code)
    (_win:bool)
    (arg0:ib64)
    (arg1:ib64)
    (arg2:ib64)
    (arg3:ib64)
    (arg4:ib64)
    (arg5:ib64)
    (arg6:ib64)
    (arg7:ib64)
    (va_s0:V.va_state)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       ta_pre code arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 va_s0)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions_stdcall va_s0 va_s1 /\
       ta_post code arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 va_s0 va_s1 f /\
       ME.buffer_readable (VS.vs_get_vale_heap va_s1) (as_vale_immbuffer arg0) /\
       ME.buffer_readable (VS.vs_get_vale_heap va_s1) (as_vale_immbuffer arg1) /\
       ME.buffer_readable (VS.vs_get_vale_heap va_s1) (as_vale_immbuffer arg2) /\
       ME.buffer_readable (VS.vs_get_vale_heap va_s1) (as_vale_immbuffer arg3) /\
       ME.buffer_readable (VS.vs_get_vale_heap va_s1) (as_vale_immbuffer arg4) /\
       ME.buffer_readable (VS.vs_get_vale_heap va_s1) (as_vale_immbuffer arg5) /\
       ME.buffer_readable (VS.vs_get_vale_heap va_s1) (as_vale_immbuffer arg6) /\
       ME.buffer_readable (VS.vs_get_vale_heap va_s1) (as_vale_immbuffer arg7) /\
       ME.modifies ME.loc_none (VS.vs_get_vale_heap va_s0) (VS.vs_get_vale_heap va_s1)))
 =
 let va_s1, f = TA.va_lemma_Test code va_s0 IA.win
      (as_vale_immbuffer arg0)
      (as_vale_immbuffer arg1)
      (as_vale_immbuffer arg2)
      (as_vale_immbuffer arg3)
      (as_vale_immbuffer arg4)
      (as_vale_immbuffer arg5)
      (as_vale_immbuffer arg6)
      (as_vale_immbuffer arg7)
    in
    va_s1, f

(* Prove that vm_lemma' has the required type *)
let ta_lemma = as_t #(VSig.vale_sig_stdcall ta_pre ta_post) ta_lemma'

let code_ta = TA.va_code_Test IA.win

(* Here's the type expected for the check_aesni wrapper *)
[@__reduce__]
let lowstar_ta_t =
  IX64.as_lowstar_sig_t_weak_stdcall
    (coerce code_ta)
    ta_dom
    []
    _
    _
    (W.mk_prediction code_ta ta_dom [] (ta_lemma code_ta IA.win))

(* And here's the check_aesni wrapper itself *)
let lowstar_ta : lowstar_ta_t  =
  IX64.wrap_weak_stdcall
    (coerce code_ta)
    ta_dom
    (W.mk_prediction code_ta ta_dom [] (ta_lemma code_ta IA.win))

let lowstar_ta_normal_t //: normal lowstar_ta_t
  = as_normal_t #lowstar_ta_t lowstar_ta

