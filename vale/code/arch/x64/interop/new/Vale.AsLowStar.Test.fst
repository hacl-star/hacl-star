module Vale.AsLowStar.Test
open Interop.Base
module ME = X64.Memory
module IA = Interop.Assumptions
module V = X64.Vale.Decls
module IX64 = Interop.X64
module VSig = Vale.AsLowStar.ValeSig
module LSig = Vale.AsLowStar.LowStarSig
module W = Vale.AsLowStar.Wrapper

////////////////////////////////////////////////////////////////////////////////
//First a little standalone, toy experiment
[@__reduce__] unfold
let b64 = lowstar_buffer ME.(TBase TUInt64)
[@__reduce__] unfold
let t = TD_Buffer ME.TUInt64

[@__reduce__] unfold
let dom : (x:list td {List.length x == 2}) =
  let y = [t;t] in
  assert_norm (List.length y = 2);
  y

assume val pre : VSig.vale_pre dom
assume val post : VSig.vale_post dom
assume val n : nat
assume val v: VSig.vale_sig pre post
assume val c: V.va_code

[@__reduce__]
let call_c_t = IX64.as_lowstar_sig_t_weak c dom [] _ _ (W.mk_prediction c dom [] n (v c IA.win))
let call_c : call_c_t = IX64.wrap_weak c dom (W.mk_prediction c dom [] n (v c IA.win))
//You can ask emacs to evaluate `normal call_c_t` and see what you get
////////////////////////////////////////////////////////////////////////////////
//Now memcpy
module VM = Vale_memcpy

[@__reduce__] unfold
let vm_dom = dom

(* Need to rearrange the order of arguments *)
[@__reduce__] unfold
let vm_pre : VSig.vale_pre vm_dom =
  fun (c:V.va_code)
    (dst:b64)
    (src:b64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer) ->
      VM.va_pre c va_s0 IA.win (as_vale_buffer sb) (as_vale_buffer dst) (as_vale_buffer src)

[@__reduce__] unfold
let vm_post : VSig.vale_post vm_dom =
  fun (c:V.va_code)
    (dst:b64)
    (src:b64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer)
    (va_s1:V.va_state)
    (f:V.va_fuel) ->
      VM.va_post c va_s0 va_s1 f IA.win (as_vale_buffer sb) (as_vale_buffer dst) (as_vale_buffer src)

module VS = X64.Vale.State
#set-options "--print_effect_args"

(* The vale lemma doesn't quite suffice to prove the modifies clause
   expected of the interop layer;
   So, that's assumed for now ... to be fixed *)
[@__reduce__] unfold
let vm_lemma'
    (code:V.va_code)
    (_win:bool)
    (dst:b64)
    (src:b64)
    (va_s0:V.va_state)
    (sb:IX64.stack_buffer)
 : Ghost (V.va_state & V.va_fuel)
     (requires
       vm_pre code dst src va_s0 sb)
     (ensures (fun (va_s1, f) ->
       V.eval_code code va_s0 f va_s1 /\
       VSig.vale_calling_conventions va_s0 va_s1 /\
       vm_post code dst src va_s0 sb va_s1 f /\
       ME.modifies (ME.loc_union (ME.loc_buffer (as_vale_buffer src))
                                 (ME.loc_union (ME.loc_buffer (as_vale_buffer dst))
                                               ME.loc_none)) va_s0.VS.mem va_s1.VS.mem
 ))
 =  let va_s1, f = VM.va_lemma_memcpy code va_s0 IA.win (as_vale_buffer sb) (as_vale_buffer dst) (as_vale_buffer src) in
    assert (ME.modifies (ME.loc_buffer (as_vale_buffer dst)) va_s0.VS.mem va_s1.VS.mem);
    //should follow by weakening, but does not for some reason
    assume (ME.modifies (ME.loc_union (ME.loc_buffer (as_vale_buffer src))
                                      (ME.loc_union (ME.loc_buffer (as_vale_buffer dst))
                                                    ME.loc_none)) va_s0.VS.mem va_s1.VS.mem);
    va_s1, f

(* A little utility to trigger normalization in types *)
let as_t (#a:Type) (x:normal a) : a = x

(* Prove that vm_lemma' has the requires type *)
let vm_lemma = as_t #(VSig.vale_sig vm_pre vm_post) vm_lemma'

let code_memcpy =     (VM.va_code_memcpy IA.win)


(* Here's the type expected for the memcpy wrapper *)
[@__reduce__]
let lowstar_memcpy_t =
  IX64.as_lowstar_sig_t_weak
    code_memcpy
    vm_dom
    []
    _
    _
    (W.mk_prediction code_memcpy vm_dom [] 3 (vm_lemma code_memcpy IA.win))

(* And here's the memcpy wrapper itself *)
let lowstar_memcpy : lowstar_memcpy_t  =
  IX64.wrap_weak
    code_memcpy
    vm_dom
    (W.mk_prediction code_memcpy vm_dom [] 3 (vm_lemma code_memcpy IA.win))
(*
   -- Some things to fix up: I need to make it return an erased result type,
      so that KreMLin generates the right signature ... should be easy.

   -- Stack slots are not properly modeled yet ... so that "3" above
      is kinda random

   -- Modifies clauses need to be finer grained: as it stands, the
      wrapped type of memcpy says it modifies both buffers.

   That said, here's what you get by computing `normal lowstar_memcpy_t`,
   slightly rewritten to give distinct names (x0, x1) to the two arguments


x0: (b: b8{LowStar.Monotonic.Buffer.length b % 8 == 0} <: Type0) ->
  Prims.Tot
  (x1: (b: b8{LowStar.Monotonic.Buffer.length b % 8 == 0} <: Type0) ->
      Prims.Tot
      (_: unit ->
          FStar.HyperStack.ST.Stack
            (Interop.X64.as_lowstar_sig_ret [
                  (| TD_Buffer (X64.Memory.TUInt64), x1 |);
                  (| TD_Buffer (X64.Memory.TUInt64), x0 |)
                ])
            (fun h0 ->
                (LowStar.Monotonic.Buffer.disjoint x1 x0 \/ x1 == x0) /\
                LowStar.Monotonic.Buffer.live h0 x0 /\ LowStar.Monotonic.Buffer.live h0 x1 /\
                (forall (s0: X64.Vale.Decls.va_state) (sb: Interop.X64.stack_buffer).
                    Mkstate?.ok s0 /\
                    (LowStar.Monotonic.Buffer.loc_disjoint (LowStar.Monotonic.Buffer.loc_buffer x1)
                        (LowStar.Monotonic.Buffer.loc_buffer x0) \/ x0 == x1) /\
                    (X64.Memory.buffer_readable (Mkstate?.mem s0) x0 /\
                    X64.Memory.buffer_readable (Mkstate?.mem s0) x1) /\
                    ((X64.Vale.State.eval_reg (Interop.X64.register_of_arg_i 0) s0 ==
                      Interop.Assumptions.addrs x0) /\
                    (X64.Vale.State.eval_reg (Interop.X64.register_of_arg_i 1) s0 ==
                      Interop.Assumptions.addrs x1)) /\
                    (X64.Memory.valid_taint_buf64 x1
                      (Mkstate?.mem s0)
                      (Mkstate?.memTaint s0)
                      (X64.Machine_s.Secret) /\
                    X64.Memory.valid_taint_buf64 x0
                      (Mkstate?.mem s0)
                      (Mkstate?.memTaint s0)
                      (X64.Machine_s.Secret)) /\
                    Seq.Base.equal (LowStarSig.nat_to_uint_seq_t (X64.Memory.TUInt64)
                          (X64.Memory.buffer_as_seq (Mkstate?.mem s0) x1))
                      (LowStar.BufferView.as_seq h0
                          (LowStar.BufferView.mk_buffer_view x1 Views.view64)) /\
                    Seq.Base.equal (LowStarSig.nat_to_uint_seq_t (X64.Memory.TUInt64)
                          (X64.Memory.buffer_as_seq (Mkstate?.mem s0) x0))
                      (LowStar.BufferView.as_seq h0
                          (LowStar.BufferView.mk_buffer_view x0 Views.view64)) /\
                    X64.Vale.Decls.valid_stack_slots (Mkstate?.mem s0)
                      (X64.Vale.State.eval_reg (X64.Machine_s.Rsp) s0)
                      sb
                      3
                      (Mkstate?.memTaint s0) ==>
                    Vale_memcpy.va_pre code_memcpy s0 Interop.Assumptions.win sb x0 x1))
            (fun h0 _ h1 ->
                exists (fuel: nat)
                  (_s1: X64.Taint_Semantics_s.traceState)
                  (final_mem: X64.Memory.mem).
                  Monotonic.HyperStack.poppable (Interop.Adapters.hs_of_mem final_mem) /\
                  h1 == Monotonic.HyperStack.pop (Interop.Adapters.hs_of_mem final_mem) /\
                  (exists (h1_pre_pop:_).
                      h1_pre_pop == Interop.Adapters.hs_of_mem final_mem /\
                      Monotonic.HyperStack.poppable h1_pre_pop /\
                      (exists (h1:_).
                          h1 == Monotonic.HyperStack.pop h1_pre_pop /\
                          (LowStar.Monotonic.Buffer.disjoint x1 x0 \/ x1 == x0) /\
                          (LowStar.Monotonic.Buffer.live h1 x1 /\ LowStar.Monotonic.Buffer.live h1 x0) /\
                          LowStar.Monotonic.Buffer.modifies (LowStar.Monotonic.Buffer.loc_union (LowStar.Monotonic.Buffer.loc_buffer
                                    x1)
                                (LowStar.Monotonic.Buffer.loc_union (LowStar.Monotonic.Buffer.loc_buffer
                                        x0)
                                    LowStar.Monotonic.Buffer.loc_none))
                            h0
                            h1 /\
                          (exists (s0: X64.Vale.Decls.va_state)
                              (s1: X64.Vale.Decls.va_state)
                              (f: X64.Vale.Decls.va_fuel)
                              (sb: Interop.X64.stack_buffer).
                              Seq.Base.equal (LowStarSig.nat_to_uint_seq_t (X64.Memory.TUInt64)
                                    (X64.Memory.buffer_as_seq (Mkstate?.mem s0) x1))
                                (LowStar.BufferView.as_seq h0
                                    (LowStar.BufferView.mk_buffer_view x1 Views.view64)) /\
                              Seq.Base.equal (LowStarSig.nat_to_uint_seq_t (X64.Memory.TUInt64)
                                    (X64.Memory.buffer_as_seq (Mkstate?.mem s0) x0))
                                (LowStar.BufferView.as_seq h0
                                    (LowStar.BufferView.mk_buffer_view x0 Views.view64)) /\
                              Seq.Base.equal (LowStarSig.nat_to_uint_seq_t (X64.Memory.TUInt64)
                                    (X64.Memory.buffer_as_seq (Mkstate?.mem s1) x1))
                                (LowStar.BufferView.as_seq h1
                                    (LowStar.BufferView.mk_buffer_view x1 Views.view64)) /\
                              Seq.Base.equal (LowStarSig.nat_to_uint_seq_t (X64.Memory.TUInt64)
                                    (X64.Memory.buffer_as_seq (Mkstate?.mem s1) x0))
                                (LowStar.BufferView.as_seq h1
                                    (LowStar.BufferView.mk_buffer_view x0 Views.view64)) /\
                              Vale_memcpy.va_post code_memcpy s0 s1 f Interop.Assumptions.win sb x0 x1
                          ))))
        <:
        Type0)
    <:
    Type0)

*)


