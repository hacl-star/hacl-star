module Vale.AsLowStar.MemoryHelpers
open X64.MemoryAdapters
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
module V = X64.Vale.Decls
module VS = X64.Vale.State
module IX64 = Interop.X64
module VSig = Vale.AsLowStar.ValeSig
module LSig = Vale.AsLowStar.LowStarSig
module SL = X64.Vale.StateLemmas
module VL = X64.Vale.Lemmas
module ST = FStar.HyperStack.ST
module I = Interop

val as_vale_buffer_len (#t:base_typ) (x:buf_t t)
   : Lemma (V.buffer_length (as_vale_buffer x) == B.length x / view_n t)
           [SMTPat (V.buffer_length (as_vale_buffer x))]

val as_vale_immbuffer_len (#t:base_typ) (x:ibuf_t t)
   : Lemma (V.buffer_length (as_vale_immbuffer x) == B.length x / view_n t)
           [SMTPat (V.buffer_length (as_vale_immbuffer x))]

val state_eq_down_mem (va_s1:V.va_state) (s1:_)
  : Lemma 
      (requires 
        VL.state_eq_opt (Some (SL.state_to_S va_s1)) 
                        (Some s1))
      (ensures (
         I.down_mem (as_mem va_s1.VS.mem) == s1.TS.state.BS.mem))

val relate_modifies (args:list arg) (m0 m1 : ME.mem)
  : Lemma 
      (requires 
        ME.modifies (VSig.mloc_modified_args args) m0 m1)
      (ensures 
        B.modifies (loc_modified_args args) 
                   (hs_of_mem (as_mem m0))
                   (hs_of_mem (as_mem m1)))

val reveal_readable (#t:_) (x:buf_t t) (s:ME.mem)
  : Lemma 
      ( List.memP (Buffer x true) (ptrs_of_mem (as_mem s)) <==>
        ME.buffer_readable s (as_vale_buffer x) )

val reveal_imm_readable (#t:_) (x:ibuf_t t) (s:ME.mem)
  : Lemma 
      ( List.memP (imm_to_b8 x) (ptrs_of_mem (as_mem s)) <==>
        ME.buffer_readable s (as_vale_immbuffer x) )

val readable_live (#t:_) (x:buf_t t) (s:ME.mem)
  : Lemma 
      ( ME.buffer_readable s (as_vale_buffer x) ==>
        B.live (hs_of_mem (as_mem s)) x)

val readable_imm_live (#t:_) (x:ibuf_t t) (s:ME.mem)
  : Lemma 
      ( ME.buffer_readable s (as_vale_immbuffer x) ==>
        B.live (hs_of_mem (as_mem s)) x)


val buffer_readable_reveal 
  (#n:_)
  (bt:base_typ)
  (x:buf_t bt)
  (args:IX64.arity_ok arg)
  (h0:HS.mem)
  (stack:IX64.stack_buffer n{mem_roots_p h0 (arg_of_sb stack::args)}) : Lemma (
    let mem = mk_mem (arg_of_sb stack::args) h0 in
    ME.buffer_readable (as_vale_mem mem) (as_vale_buffer #bt x) <==>
      List.memP (Buffer x true) (ptrs_of_mem mem))

val get_heap_mk_mem_reveal
  (#n:_)
  (args:IX64.arity_ok arg)
  (h0:HS.mem)
  (stack:IX64.stack_buffer n{mem_roots_p h0 (arg_of_sb stack::args)}) : Lemma
  (let mem = mk_mem (arg_of_sb stack::args) h0 in
   liveness_disjointness (arg_of_sb stack::args) h0;
   MES.get_heap (as_vale_mem mem) == I.down_mem mem)

val buffer_as_seq_reveal
  (#n:_)
  (t:ME.base_typ)
  (x:buf_t t)
  (args:IX64.arity_ok arg)
  (h0:HS.mem)
  (stack:IX64.stack_buffer n{mem_roots_p h0 (arg_of_sb stack::args)}) : Lemma
  (let y = as_vale_buffer x in
   let mem = mk_mem (arg_of_sb stack::args) h0 in
   Seq.equal 
    (LSig.nat_to_uint_seq_t t (ME.buffer_as_seq (as_vale_mem mem) y))
    (BV.as_seq h0 (BV.mk_buffer_view x (LSig.view_of_base_typ t))))

val immbuffer_as_seq_reveal
  (#n:_)
  (t:ME.base_typ)
  (x:ibuf_t t)
  (args:IX64.arity_ok arg)
  (h0:HS.mem)
  (stack:IX64.stack_buffer n{mem_roots_p h0 (arg_of_sb stack::args)}) : Lemma
  (let y = as_vale_immbuffer x in
   let mem = mk_mem (arg_of_sb stack::args) h0 in
   Seq.equal 
    (LSig.nat_to_uint_seq_t t (ME.buffer_as_seq (as_vale_mem mem) y))
    (BV.as_seq h0 (BV.mk_buffer_view x (LSig.view_of_base_typ t))))

val buffer_as_seq_reveal2
  (t:ME.base_typ)
  (x:buf_t t)
  (va_s:V.va_state) : Lemma
  (let y = as_vale_buffer x in
   let h = hs_of_mem (as_mem va_s.VS.mem) in
   Seq.equal 
    (LSig.nat_to_uint_seq_t t (ME.buffer_as_seq va_s.VS.mem y))
    (BV.as_seq h (BV.mk_buffer_view x (LSig.view_of_base_typ t))))

val immbuffer_as_seq_reveal2
  (t:ME.base_typ)
  (x:ibuf_t t)
  (va_s:V.va_state) : Lemma
  (let y = as_vale_immbuffer x in
   let h = hs_of_mem (as_mem va_s.VS.mem) in
   Seq.equal 
    (LSig.nat_to_uint_seq_t t (ME.buffer_as_seq va_s.VS.mem y))
    (BV.as_seq h (BV.mk_buffer_view x (LSig.view_of_base_typ t))))

val buffer_addr_reveal
  (t:ME.base_typ)
  (x:buf_t t)
  (args:list arg)
  (h0:HS.mem{mem_roots_p h0 args}) : Lemma
  (let mem = mk_mem args h0 in
   addrs_of_mem mem (Buffer x true) == ME.buffer_addr (as_vale_buffer #t x) (as_vale_mem mem))

val immbuffer_addr_reveal
  (t:ME.base_typ)
  (x:ibuf_t t)
  (args:list arg)
  (h0:HS.mem{mem_roots_p h0 args}) : Lemma
  (let mem = mk_mem args h0 in
   addrs_of_mem mem (imm_to_b8 x) == ME.buffer_addr (as_vale_immbuffer #t x) (as_vale_mem mem))

val fuel_eq : squash (V.va_fuel == nat)

val decls_eval_code_reveal
  (c:TS.tainted_code)
  (va_s0 va_s1:_)
  (f:V.va_fuel) : Lemma
  (requires (V.eval_code c va_s0 f va_s1))
  (ensures (VL.eval_code c va_s0 (coerce f) va_s1))

val as_vale_buffer_disjoint (#t1 #t2:base_typ) (x:buf_t t1) (y:buf_t t2)
   : Lemma (B.disjoint x y ==> ME.loc_disjoint (ME.loc_buffer (as_vale_buffer x)) (ME.loc_buffer (as_vale_buffer y)))
           [SMTPat (ME.loc_disjoint (ME.loc_buffer (as_vale_buffer x)) (ME.loc_buffer (as_vale_buffer y)))]

val as_vale_buffer_imm_disjoint (#t1 #t2:base_typ) (x:ibuf_t t1) (y:buf_t t2)
   : Lemma (B.disjoint x y ==> ME.loc_disjoint (ME.loc_buffer (as_vale_immbuffer x)) (ME.loc_buffer (as_vale_buffer y)))
           [SMTPat (ME.loc_disjoint (ME.loc_buffer (as_vale_immbuffer x)) (ME.loc_buffer (as_vale_buffer y)))]

val as_vale_immbuffer_imm_disjoint (#t1 #t2:base_typ) (x:ibuf_t t1) (y:ibuf_t t2)
   : Lemma (B.disjoint x y ==> ME.loc_disjoint (ME.loc_buffer (as_vale_immbuffer x)) (ME.loc_buffer (as_vale_immbuffer y)))
           [SMTPat (ME.loc_disjoint (ME.loc_buffer (as_vale_immbuffer x)) (ME.loc_buffer (as_vale_immbuffer y)))]


val modifies_same_roots
  (s:ME.loc)
  (h0 h1:ME.mem) : Lemma
  (requires ME.modifies s h0 h1)
  (ensures ptrs_of_mem (as_mem h0) == ptrs_of_mem (as_mem h1))

val modifies_equal_domains
  (s:ME.loc)
  (h0 h1:ME.mem) : Lemma
  (requires ME.modifies s h0 h1)
  (ensures FStar.HyperStack.ST.equal_domains (hs_of_mem (as_mem h0)) (hs_of_mem (as_mem h1)))

val loc_disjoint_sym (x y:ME.loc)
   : Lemma (ME.loc_disjoint x y <==> ME.loc_disjoint y x)
           [SMTPat (ME.loc_disjoint x y)]

val core_create_lemma_taint_hyp
    (#n:_)
    (args:IX64.arity_ok arg)
    (h0:HS.mem)
    (stack:IX64.stack_buffer n{mem_roots_p h0 (arg_of_sb stack::args)})
  : Lemma
      (ensures (let va_s = LSig.create_initial_vale_state args h0 stack in
                LSig.taint_hyp args va_s /\
                ME.valid_taint_buf64 (as_vale_buffer stack) va_s.VS.mem va_s.VS.memTaint X64.Machine_s.Public))

val buffer_writeable_reveal (t:ME.base_typ) (x:buf_t t) : Lemma
  (ME.buffer_writeable (as_vale_buffer x))

let low_buffer_read (t:ME.base_typ) (h:HS.mem) (b:(buf_t t){B.live h b}) (i:nat{i < B.length b / view_n t}) : GTot (base_typ_as_type t) =
  let view = LSig.view_of_base_typ t in
  let b_v = BV.mk_buffer_view b view in
  BV.as_buffer_mk_buffer_view b view;
  BV.get_view_mk_buffer_view b view;
  BV.length_eq b_v;  
  BV.sel h b_v i

val buffer_read_reveal (t:ME.base_typ) (h:HS.mem) (s:ME.mem) (b:(buf_t t){B.live h b}) (i:nat{i < B.length b / view_n t}) : Lemma
  (requires Seq.equal 
    (LSig.nat_to_uint_seq_t t (ME.buffer_as_seq s (as_vale_buffer b)))
    (BV.as_seq h (BV.mk_buffer_view b (LSig.view_of_base_typ t))))
  (ensures LSig.nat_to_uint t (ME.buffer_read (as_vale_buffer b) i s) == 
    low_buffer_read t h b i ) 
  [SMTPat (low_buffer_read t h b i); SMTPat (ME.buffer_read (as_vale_buffer b) i s)]
