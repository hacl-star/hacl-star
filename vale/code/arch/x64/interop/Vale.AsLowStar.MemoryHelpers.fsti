module Vale.AsLowStar.MemoryHelpers
open Vale.X64.MemoryAdapters
open Vale.Interop.Base
module B = LowStar.Buffer
module BS = Vale.X64.Machine_Semantics_s
module DV = LowStar.BufferView.Down
module UV = LowStar.BufferView.Up
module HS = FStar.HyperStack
module ME = Vale.X64.Memory
module MES = Vale.X64.Memory_Sems
module SI = Vale.X64.Stack_i
module VSS = Vale.X64.Stack_Sems
module MS = Vale.X64.Machine_s
module IA = Vale.Interop.Assumptions
module V = Vale.X64.Decls
module VS = Vale.X64.State
module IX64 = Vale.Interop.X64
module VSig = Vale.AsLowStar.ValeSig
module LSig = Vale.AsLowStar.LowStarSig
module SL = Vale.X64.StateLemmas
module VL = Vale.X64.Lemmas
module ST = FStar.HyperStack.ST
module I = Vale.Interop
open Vale.Arch.Heap
open FStar.Mul

val as_vale_buffer_len (#src #t:base_typ) (x:buf_t src t)
   : Lemma (V.buffer_length (as_vale_buffer x) == (B.length x * view_n src) / view_n t)
           [SMTPat (V.buffer_length (as_vale_buffer x))]

val as_vale_immbuffer_len (#src #t:base_typ) (x:ibuf_t src t)
   : Lemma (V.buffer_length (as_vale_immbuffer x) == (B.length x * view_n src) / view_n t)
           [SMTPat (V.buffer_length (as_vale_immbuffer x))]

val state_eq_down_mem (va_s1:V.va_state) (s1:_)
  : Lemma
      (requires
        VL.state_eq_opt (Some (SL.state_to_S va_s1))
                        (Some s1))
      (ensures (
        heap_get (heap_of_interop (as_mem va_s1.VS.vs_heap)) == heap_get s1.BS.ms_heap))

val relate_modifies (args:list arg) (m0 m1 : ME.vale_heap)
  : Lemma
      (requires
        ME.modifies (VSig.mloc_modified_args args) m0 m1)
      (ensures
        B.modifies (loc_modified_args args)
                   (hs_of_mem (as_mem m0))
                   (hs_of_mem (as_mem m1)))

val reveal_readable (#src #t:_) (x:buf_t src t) (s:ME.vale_heap)
  : Lemma
      ( List.memP (mut_to_b8 src x) (ptrs_of_mem (as_mem s)) <==>
        ME.buffer_readable s (as_vale_buffer x) )

val reveal_imm_readable (#src #t:_) (x:ibuf_t src t) (s:ME.vale_heap)
  : Lemma
      ( List.memP (imm_to_b8 src x) (ptrs_of_mem (as_mem s)) <==>
        ME.buffer_readable s (as_vale_immbuffer x) )

val readable_live (#src #t:_) (x:buf_t src t) (s:ME.vale_heap)
  : Lemma
      ( ME.buffer_readable s (as_vale_buffer x) ==>
        B.live (hs_of_mem (as_mem s)) x)

val readable_imm_live (#src #t:_) (x:ibuf_t src t) (s:ME.vale_heap)
  : Lemma
      ( ME.buffer_readable s (as_vale_immbuffer x) ==>
        B.live (hs_of_mem (as_mem s)) x)

val buffer_readable_reveal
  (#max_arity:_)
  (src bt:base_typ)
  (x:buf_t src bt)
  (args:IX64.arity_ok max_arity arg)
  (h0:HS.mem{mem_roots_p h0 args}) : Lemma (
    let mem = mk_mem args h0 in
    ME.buffer_readable (as_vale_mem mem) (as_vale_buffer x) <==>
      List.memP (mut_to_b8 src x) (ptrs_of_mem mem))

val get_heap_mk_mem_reveal
  (args:IX64.arg_list)
  (h0:HS.mem{mem_roots_p h0 args}) : Lemma (
   let mem = mk_mem args h0 in
   as_vale_mem mem == coerce (heap_of_interop mem))

val lemma_as_mem_as_vale_mem (h:interop_heap) : Lemma
  (ensures as_mem (as_vale_mem h) == h)
  [SMTPat (as_mem (as_vale_mem h))]

val mk_stack_reveal (stack:BS.machine_stack) : Lemma
  (VSS.stack_to_s (as_vale_stack stack) == stack /\
   SI.init_rsp (as_vale_stack stack) == stack.BS.initial_rsp)

val buffer_as_seq_reveal
  (src t:ME.base_typ)
  (x:buf_t src t)
  (args:IX64.arg_list)
  (h0:HS.mem{mem_roots_p h0 args}) : Lemma
  (let y = as_vale_buffer x in
   let db = get_downview x in
   DV.length_eq db;
   let mem = mk_mem args h0 in
   Seq.equal
    (LSig.nat_to_uint_seq_t t (ME.buffer_as_seq (as_vale_mem mem) y))
    (UV.as_seq h0 (UV.mk_buffer db (LSig.view_of_base_typ t))))

val immbuffer_as_seq_reveal
  (src t:ME.base_typ)
  (x:ibuf_t src t)
  (args:IX64.arg_list)
  (h0:HS.mem{mem_roots_p h0 args}) : Lemma
  (let y = as_vale_immbuffer x in
   let db = get_downview x in
   DV.length_eq db;
   let mem = mk_mem args h0 in
   Seq.equal
    (LSig.nat_to_uint_seq_t t (ME.buffer_as_seq (as_vale_mem mem) y))
    (UV.as_seq h0 (UV.mk_buffer db (LSig.view_of_base_typ t))))

val buffer_as_seq_reveal2
  (src t:ME.base_typ)
  (x:buf_t src t)
  (va_s:V.va_state) : Lemma
  (let y = as_vale_buffer x in
   let db = get_downview x in
   DV.length_eq db;
   let h = hs_of_mem (as_mem va_s.VS.vs_heap) in
   Seq.equal
    (LSig.nat_to_uint_seq_t t (ME.buffer_as_seq va_s.VS.vs_heap y))
    (UV.as_seq h (UV.mk_buffer db (LSig.view_of_base_typ t))))

val immbuffer_as_seq_reveal2
  (src t:ME.base_typ)
  (x:ibuf_t src t)
  (va_s:V.va_state) : Lemma
  (let y = as_vale_immbuffer x in
   let db = get_downview x in
   DV.length_eq db;
   let h = hs_of_mem (as_mem va_s.VS.vs_heap) in
   Seq.equal
    (LSig.nat_to_uint_seq_t t (ME.buffer_as_seq va_s.VS.vs_heap y))
    (UV.as_seq h (UV.mk_buffer db (LSig.view_of_base_typ t))))

val buffer_addr_reveal
  (src t:ME.base_typ)
  (x:buf_t src t)
  (args:list arg)
  (h0:HS.mem{mem_roots_p h0 args}) : Lemma
  (let mem = mk_mem args h0 in
   addrs_of_mem mem (mut_to_b8 src x) == ME.buffer_addr (as_vale_buffer x) (as_vale_mem mem))

val immbuffer_addr_reveal
  (src t:ME.base_typ)
  (x:ibuf_t src t)
  (args:list arg)
  (h0:HS.mem{mem_roots_p h0 args}) : Lemma
  (let mem = mk_mem args h0 in
   addrs_of_mem mem (imm_to_b8 src x) == ME.buffer_addr (as_vale_immbuffer x) (as_vale_mem mem))

val fuel_eq : squash (V.va_fuel == nat)

val decls_eval_code_reveal
  (c:BS.code)
  (va_s0 va_s1:_)
  (f:V.va_fuel) : Lemma
  (requires (V.eval_code c va_s0 f va_s1))
  (ensures (VL.eval_code c va_s0 (coerce f) va_s1))

val as_vale_buffer_disjoint (#src1 #src2 #t1 #t2:base_typ) (x:buf_t src1 t1) (y:buf_t src2 t2)
   : Lemma (B.disjoint x y ==> ME.loc_disjoint (ME.loc_buffer (as_vale_buffer x)) (ME.loc_buffer (as_vale_buffer y)))
           [SMTPat (ME.loc_disjoint (ME.loc_buffer (as_vale_buffer x)) (ME.loc_buffer (as_vale_buffer y)))]

val as_vale_buffer_imm_disjoint (#src1 #src2 #t1 #t2:base_typ) (x:ibuf_t src1 t1) (y:buf_t src2 t2)
   : Lemma (B.disjoint x y ==> ME.loc_disjoint (ME.loc_buffer (as_vale_immbuffer x)) (ME.loc_buffer (as_vale_buffer y)))
           [SMTPat (ME.loc_disjoint (ME.loc_buffer (as_vale_immbuffer x)) (ME.loc_buffer (as_vale_buffer y)))]

val as_vale_immbuffer_imm_disjoint (#src1 #src2 #t1 #t2:base_typ) (x:ibuf_t src1 t1) (y:ibuf_t src2 t2)
   : Lemma (B.disjoint x y ==> ME.loc_disjoint (ME.loc_buffer (as_vale_immbuffer x)) (ME.loc_buffer (as_vale_immbuffer y)))
           [SMTPat (ME.loc_disjoint (ME.loc_buffer (as_vale_immbuffer x)) (ME.loc_buffer (as_vale_immbuffer y)))]

val modifies_same_roots
  (s:ME.loc)
  (h0 h1:ME.vale_heap) : Lemma
  (requires ME.modifies s h0 h1)
  (ensures ptrs_of_mem (as_mem h0) == ptrs_of_mem (as_mem h1))

val modifies_equal_domains
  (s:ME.loc)
  (h0 h1:ME.vale_heap) : Lemma
  (requires ME.modifies s h0 h1)
  (ensures FStar.HyperStack.ST.equal_domains (hs_of_mem (as_mem h0)) (hs_of_mem (as_mem h1)))

val loc_disjoint_sym (x y:ME.loc)
   : Lemma (ME.loc_disjoint x y <==> ME.loc_disjoint y x)
           [SMTPat (ME.loc_disjoint x y)]

val core_create_lemma_taint_hyp
    (#max_arity:_)
    (#arg_reg:IX64.arg_reg_relation max_arity)
    (args:IX64.arg_list)
    (h0:HS.mem{mem_roots_p h0 args})
  : Lemma
      (ensures (let va_s = LSig.create_initial_vale_state #max_arity #arg_reg args h0 in
                LSig.taint_hyp args va_s))

val buffer_writeable_reveal (src t:ME.base_typ) (x:buf_t src t) : Lemma
  (ME.buffer_writeable (as_vale_buffer x))

let low_buffer_read (src t:base_typ) (h:HS.mem) (b:(buf_t src t){B.live h b}) (i:nat{i < DV.length (get_downview b) / view_n t}) : GTot (base_typ_as_type t) =
  let view = LSig.view_of_base_typ t in
  let db = get_downview b in
  DV.length_eq db;
  let b_v = UV.mk_buffer db view in
  UV.length_eq b_v;
  UV.sel h b_v i

val buffer_read_reveal (src t:base_typ) (h:HS.mem) (s:ME.vale_heap) (b:(buf_t src t){B.live h b}) (i:nat{i < DV.length (get_downview b) / view_n t}) : Lemma
  (requires (
   DV.length_eq (get_downview b);
   Seq.equal
    (LSig.nat_to_uint_seq_t t (ME.buffer_as_seq s (as_vale_buffer b)))
    (UV.as_seq h (UV.mk_buffer (get_downview b) (LSig.view_of_base_typ t)))))
  (ensures LSig.nat_to_uint t (ME.buffer_read (as_vale_buffer b) i s) ==
    low_buffer_read src t h b i )
  [SMTPat (low_buffer_read src t h b i); SMTPat (ME.buffer_read (as_vale_buffer b) i s)]

let imm_low_buffer_read (src t:base_typ) (h:HS.mem) (b:(ibuf_t src t){B.live h b}) (i:nat{i < DV.length (get_downview b) / view_n t}) : GTot (base_typ_as_type t) =
  let view = LSig.view_of_base_typ t in
  let db = get_downview b in
  DV.length_eq db;
  let b_v = UV.mk_buffer db view in
  UV.length_eq b_v;
  UV.sel h b_v i

val imm_buffer_read_reveal (src t:base_typ) (h:HS.mem) (s:ME.vale_heap) (b:(ibuf_t src t){B.live h b}) (i:nat{i < DV.length (get_downview b) / view_n t}) : Lemma
  (requires (
  DV.length_eq (get_downview b);
  Seq.equal
    (LSig.nat_to_uint_seq_t t (ME.buffer_as_seq s (as_vale_immbuffer b)))
    (UV.as_seq h (UV.mk_buffer (get_downview b) (LSig.view_of_base_typ t)))))
  (ensures LSig.nat_to_uint t (ME.buffer_read (as_vale_immbuffer b) i s) ==
    imm_low_buffer_read src t h b i )
  [SMTPat (imm_low_buffer_read src t h b i); SMTPat (ME.buffer_read (as_vale_immbuffer b) i s)]

val buffer_as_seq_invert (src t:base_typ) (h:HS.mem) (s:ME.vale_heap) (b:(buf_t src t){B.live h b}) : Lemma
  (requires (
  DV.length_eq (get_downview b);
  Seq.equal
    (LSig.nat_to_uint_seq_t t (ME.buffer_as_seq s (as_vale_buffer b)))
    (UV.as_seq h (UV.mk_buffer (get_downview b) (LSig.view_of_base_typ t)))))
  (ensures ME.buffer_as_seq s (as_vale_buffer b) ==
    (LSig.uint_to_nat_seq_t t (UV.as_seq h (UV.mk_buffer (get_downview b) (LSig.view_of_base_typ t)))))
  [SMTPat (UV.as_seq h (UV.mk_buffer (get_downview b) (LSig.view_of_base_typ t)));
   SMTPat (ME.buffer_as_seq s (as_vale_buffer b))]

val buffer_as_seq_reveal_tuint128
  (src:base_typ)
  (x:buf_t src TUInt128)
  (va_s:V.va_state) : Lemma
  (let y = as_vale_buffer x in
   let h = hs_of_mem (as_mem va_s.VS.vs_heap) in
   Seq.equal
    (LSig.nat_to_uint_seq_t TUInt128 (ME.buffer_as_seq va_s.VS.vs_heap y))
    (V.buffer128_as_seq va_s.VS.vs_heap (as_vale_buffer x)))
  [SMTPat (V.buffer128_as_seq va_s.VS.vs_heap (as_vale_buffer x))]

val immbuffer_as_seq_reveal_tuint128
  (src:base_typ)
  (x:ibuf_t src TUInt128)
  (va_s:V.va_state) : Lemma
  (let y = as_vale_immbuffer x in
   let h = hs_of_mem (as_mem va_s.VS.vs_heap) in
   Seq.equal
    (LSig.nat_to_uint_seq_t TUInt128 (ME.buffer_as_seq va_s.VS.vs_heap y))
    (V.buffer128_as_seq va_s.VS.vs_heap (as_vale_immbuffer x)))
  [SMTPat (V.buffer128_as_seq va_s.VS.vs_heap (as_vale_immbuffer x))]

val bounded_buffer_addrs_one (src t:base_typ) (h:HS.mem) (b:buf_t src t{B.live h b}) (s:ME.vale_heap) : Lemma
  (ME.buffer_addr #t (as_vale_buffer b) s + DV.length (get_downview b) < Vale.Def.Words_s.pow2_64)

val bounded_buffer_addrs_all (src t:base_typ) (m:HS.mem) (b:buf_t src t{B.live m b}) : Lemma
  (forall (h:ME.vale_heap) (vb:ME.buffer t).{:pattern ME.buffer_addr #t vb h}
    vb == as_vale_buffer b ==>
    ME.buffer_addr #t vb h + DV.length (get_downview b) < Vale.Def.Words_s.pow2_64)

val same_down_up_buffer_length (src:base_typ) (b:buf_t src src) : Lemma
  (B.length b == DV.length (get_downview b) / view_n src)

val down_up_buffer_read_reveal (src:base_typ) (h:HS.mem) (s:ME.vale_heap) (b:(buf_t src src){B.live h b}) (i:nat{i < DV.length (get_downview b) / view_n src}) : Lemma
  (requires (
   DV.length_eq (get_downview b);
   same_down_up_buffer_length src b;
   Seq.equal
    (LSig.nat_to_uint_seq_t src (ME.buffer_as_seq s (as_vale_buffer b)))
    (UV.as_seq h (UV.mk_buffer (get_downview b) (LSig.view_of_base_typ src)))))
  (ensures LSig.nat_to_uint src (ME.buffer_read (as_vale_buffer b) i s) ==
    Seq.index (B.as_seq h b) i)
  [SMTPat (ME.buffer_read (as_vale_buffer b) i s); SMTPat (Seq.index (B.as_seq h b) i)]

val same_buffer_same_upviews (#src #bt:base_typ) (b:buf_t src bt) (h0 h1:HS.mem) : Lemma
  (requires Seq.equal (B.as_seq h0 b) (B.as_seq h1 b))
  (ensures (
    let db = get_downview b in
    DV.length_eq db;
    let ub = UV.mk_buffer db (LSig.view_of_base_typ bt) in
    Seq.equal (UV.as_seq h0 ub) (UV.as_seq h1 ub)))

val same_immbuffer_same_upviews (#src #bt:base_typ) (b:ibuf_t src bt) (h0 h1:HS.mem) : Lemma
  (requires Seq.equal (B.as_seq h0 b) (B.as_seq h1 b))
  (ensures (
    let db = get_downview b in
    DV.length_eq db;
    let ub = UV.mk_buffer db (LSig.view_of_base_typ bt) in
    Seq.equal (UV.as_seq h0 ub) (UV.as_seq h1 ub)))
