module Vale.AsLowStar.MemoryHelpers

open Interop.Base
module B = LowStar.Buffer
module BS = X64.Bytes_Semantics_s
module BV = LowStar.BufferView
module HS = FStar.HyperStack
module ME = X64.Memory
module MES = X64.Memory_Sems
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
module ST = FStar.HyperStack.ST


val as_vale_buffer_len (#t:ME.typ) (x:lowstar_buffer t)
   : Lemma (V.buffer_length (as_vale_buffer x) == B.length x / view_n t)
           [SMTPat (V.buffer_length (as_vale_buffer x))]

val state_eq_down_mem (va_s1:V.va_state) (s1:_)
  : Lemma 
      (requires 
        VL.state_eq_opt (Some (SL.state_to_S va_s1)) 
                        (Some s1))
      (ensures (
         let h1 = (Interop.Adapters.hs_of_mem va_s1.VS.mem) in
         let final_mem = va_s1.VS.mem in
         IM.down_mem h1
                     IA.addrs
                     (Interop.Adapters.ptrs_of_mem final_mem) ==
         s1.TS.state.BS.mem))

val relate_modifies (args:list arg) (m0 m1 : ME.mem)
  : Lemma 
      (requires 
        ME.modifies (VSig.mloc_modified_args args) m0 m1)
      (ensures 
        B.modifies (loc_modified_args args) 
                   (Interop.Adapters.hs_of_mem m0)
                   (Interop.Adapters.hs_of_mem m1))

val reveal_readable (#t:_) (x:lowstar_buffer t) (s:ME.mem)
  : Lemma 
      ( List.memP x (Interop.Adapters.ptrs_of_mem s) <==>
        ME.buffer_readable s (as_vale_buffer x) )

val readable_live (#t:_) (x:lowstar_buffer t) (s:ME.mem)
  : Lemma 
      ( ME.buffer_readable s (as_vale_buffer x) ==>
        B.live (Interop.Adapters.hs_of_mem s) x)

val buffer_readable_reveal 
  (#n:_)
  (bt:ME.base_typ)
  (x:lowstar_buffer (ME.TBase bt)) 
  (args:IX64.arity_ok arg)
  (h0:HS.mem)
  (stack:IX64.stack_buffer n{mem_roots_p h0 (arg_of_sb stack::args)}) : Lemma (
    let mem = Interop.Adapters.mk_mem (arg_of_sb stack::args) h0 in
    ME.buffer_readable mem (as_vale_buffer #(ME.TBase bt) x) <==>
      List.memP x (Interop.Adapters.ptrs_of_mem mem))

val get_heap_mk_mem_reveal
  (#n:_)
  (args:IX64.arity_ok arg)
  (h0:HS.mem)
  (stack:IX64.stack_buffer n{mem_roots_p h0 (arg_of_sb stack::args)}) : Lemma
  (let mem = Interop.Adapters.mk_mem (arg_of_sb stack::args) h0 in
   Interop.Adapters.liveness_disjointness (arg_of_sb stack::args) h0;
   MES.get_heap mem == IM.down_mem h0 IA.addrs (Interop.Adapters.args_b8 (arg_of_sb stack::args)))

val buffer_as_seq_reveal
  (#n:_)
  (t:ME.base_typ)
  (x:lowstar_buffer (ME.TBase t))
  (args:IX64.arity_ok arg)
  (h0:HS.mem)
  (stack:IX64.stack_buffer n{mem_roots_p h0 (arg_of_sb stack::args)}) : Lemma
  (let y = as_vale_buffer x in
  let mem = Interop.Adapters.mk_mem (arg_of_sb stack::args) h0 in
  assume (t <> ME.TUInt128); // TODO: UInt128
  Seq.equal 
    (LSig.nat_to_uint_seq_t t (ME.buffer_as_seq mem y))
    (BV.as_seq h0 (BV.mk_buffer_view x (LSig.view_of_base_typ t))))

val buffer_as_seq_reveal2
  (t:ME.base_typ)
  (x:lowstar_buffer (ME.TBase t))
  (va_s:V.va_state) : Lemma
  (let y = as_vale_buffer x in
  let h = Interop.Adapters.hs_of_mem va_s.VS.mem in
  assume (t <> ME.TUInt128); // TODO: UInt128
  Seq.equal 
    (LSig.nat_to_uint_seq_t t (ME.buffer_as_seq va_s.VS.mem y))
    (BV.as_seq h (BV.mk_buffer_view x (LSig.view_of_base_typ t))))

val buffer_addr_reveal
  (t:ME.base_typ)
  (x:lowstar_buffer (ME.TBase t))
  (args:list arg)
  (h0:HS.mem{mem_roots_p h0 args}) : Lemma
  (let mem = Interop.Adapters.mk_mem args h0 in
  IA.addrs x == ME.buffer_addr (as_vale_buffer #(ME.TBase t) x) mem)

val fuel_eq : squash (V.va_fuel == nat)

val decls_eval_code_reveal
  (c:TS.tainted_code)
  (va_s0 va_s1:_)
  (f:V.va_fuel) : Lemma
  (requires (V.eval_code c va_s0 f va_s1))
  (ensures (VL.eval_code c va_s0 (coerce f) va_s1))
