module Vale.AsLowStar.MemoryHelpers
open X64.MemoryAdapters
open Interop.Base
module B = LowStar.Buffer
module UV = LowStar.BufferView.Up
module DV = LowStar.BufferView.Down
module ME = X64.Memory
module VSig = Vale.AsLowStar.ValeSig

friend X64.Memory
friend X64.Memory_Sems
friend X64.Stack_i
friend X64.Stack_Sems
friend X64.Vale.Decls
friend X64.Vale.StateLemmas
friend X64.MemoryAdapters

let as_vale_buffer_len (#src #t:base_typ) (x:buf_t src t)
   = let db = get_downview x in
   DV.length_eq db;
   UV.length_eq (UV.mk_buffer db (ME.uint_view t))

let as_vale_immbuffer_len (#src #t:base_typ) (x:ibuf_t src t)
   = let db = get_downview x in
   DV.length_eq db;
   UV.length_eq (UV.mk_buffer db (ME.uint_view t))
   
let state_eq_down_mem (va_s1:V.va_state) (s1:_) = ()

let rec loc_eq (args:list arg)
  : Lemma (VSig.mloc_modified_args args == loc_modified_args args)
  = match args with
    | [] -> ()
    | hd :: tl -> loc_eq tl

let relate_modifies (args:list arg) (m0 m1 : ME.mem) = loc_eq args
let reveal_readable (#src #t:_) (x:buf_t src t) (s:ME.mem) = ()
let reveal_imm_readable (#src #t:_) (x:ibuf_t src t) (s:ME.mem) = ()
let readable_live (#src #t:_) (x:buf_t src t) (s:ME.mem) = ()
let readable_imm_live (#src #t:_) (x:ibuf_t src t) (s:ME.mem) = ()
let buffer_readable_reveal #max_arity src bt x args h0 = ()
let get_heap_mk_mem_reveal args h0 = ()
let mk_stack_reveal stack = ()
let buffer_as_seq_reveal src t x args h0 = ()
let immbuffer_as_seq_reveal src t x args h0 = ()
let buffer_as_seq_reveal2 src t x va_s = ()
let immbuffer_as_seq_reveal2 src t x va_s = ()
let buffer_addr_reveal src t x args h0 = ()
let immbuffer_addr_reveal src t x args h0 = ()
let fuel_eq = ()
let decls_eval_code_reveal c va_s0 va_s1 f = ()
let as_vale_buffer_disjoint (#src1 #src2 #t1 #t2:base_typ) (x:buf_t src1 t1) (y:buf_t src2 t2) = ()
let as_vale_buffer_imm_disjoint (#src1 #src2 #t1 #t2:base_typ) (x:ibuf_t src1 t1) (y:buf_t src2 t2) = ()
let as_vale_immbuffer_imm_disjoint (#src1 #src2 #t1 #t2:base_typ) (x:ibuf_t src1 t1) (y:ibuf_t src2 t2) = ()
let modifies_same_roots s h0 h1 = ()
let modifies_equal_domains s h0 h1 = ()
let loc_disjoint_sym (x y:ME.loc)  = ()

#set-options "--z3rlimit 20"

let core_create_lemma_taint_hyp
    #max_arity
    #arg_reg
    (args:IX64.arg_list)
    (h0:HS.mem{mem_roots_p h0 args})
  : Lemma
      (ensures (let va_s = LSig.create_initial_vale_state #max_arity #arg_reg args h0 in
                LSig.taint_hyp args va_s))
  = let va_s = LSig.create_initial_vale_state #max_arity #arg_reg args h0 in
    let taint_map = va_s.VS.memTaint in
    let mem = va_s.VS.mem in
//    assert (mem == mk_mem args h0);
    let raw_taint = IX64.(mk_taint args IX64.init_taint) in
    assert (taint_map == create_memtaint mem (args_b8 args) raw_taint);
    ME.valid_memtaint mem (args_b8 args) raw_taint;
//    assert (forall x. List.memP x (args_b8 args) ==> ME.valid_taint_buf x mem taint_map (raw_taint x));
    assert (forall x. List.memP x (args_b8 args) ==> ME.valid_taint_buf x mem taint_map (raw_taint x));
    Classical.forall_intro (IX64.mk_taint_equiv args);
    assert (forall (a:arg). List.memP a args /\ Some? (IX64.taint_of_arg a) ==>
            Some?.v (IX64.taint_of_arg a) == raw_taint (IX64.taint_arg_b8 a));
    Classical.forall_intro (args_b8_mem args);
    assert (forall x. List.memP x args /\ Some? (IX64.taint_of_arg x) ==>
                 LSig.taint_hyp_arg mem taint_map x);
    BigOps.big_and'_forall (LSig.taint_hyp_arg mem taint_map) args

let buffer_writeable_reveal src t x = ()

let buffer_read_reveal src t h s b i =
  let db = get_downview b in
  DV.length_eq db;
  let b_v = UV.mk_buffer db (LSig.view_of_base_typ t) in
  UV.as_seq_sel h b_v i

let imm_buffer_read_reveal src t h s b i =
  let db = get_downview b in
  DV.length_eq db;
  let b_v = UV.mk_buffer db (LSig.view_of_base_typ t) in
  UV.as_seq_sel h b_v i

let buffer_as_seq_invert src t h s b =
  let db = get_downview b in
  DV.length_eq db;
  assert (Seq.equal 
    (ME.buffer_as_seq s (as_vale_buffer b))
    (LSig.uint_to_nat_seq_t t (UV.as_seq h (UV.mk_buffer db (LSig.view_of_base_typ t)))))
    
let buffer_as_seq_reveal_tuint128 src x va_s = ()

let immbuffer_as_seq_reveal_tuint128 src x va_s = ()

let bounded_buffer_addrs src t h b s = ()

let same_down_up_buffer_length src b =
  let db = get_downview b in
  DV.length_eq db;
  FStar.Math.Lemmas.cancel_mul_div (B.length b) (view_n src)

val lemma_mult_lt_right: a:pos -> b:nat -> c:nat -> Lemma
  (requires (b < c))
  (ensures  (b * a < c * a))
let lemma_mult_lt_right a b c = 
  assert (c <> 0);
  if b = 0 then (
    assert (0 * a == 0);
    FStar.Math.Lemmas.pos_times_pos_is_pos c a
  ) else (
    FStar.Math.Lemmas.lemma_mult_lt_left a b c
  )

let down_up_buffer_read_reveal src h s b i =
  let db = get_downview b in
  let n:pos = view_n src in
  let up_view = (LSig.view_of_base_typ src) in
  let ub = UV.mk_buffer db up_view in
  same_down_up_buffer_length src b;
  UV.length_eq ub;
  UV.get_sel h ub i;
  lemma_mult_lt_right n i (DV.length db / n);
  FStar.Math.Lemmas.multiply_fractions (DV.length db) n;
  FStar.Math.Lemmas.nat_times_nat_is_nat i n;
  assert (low_buffer_read src src h b i == 
    UV.View?.get up_view (Seq.slice (DV.as_seq h db) (i*n) (i*n + n)));
  DV.put_sel h db (i*n);
  let aux () : Lemma (n * ((i*n)/n) == i*n) =
    FStar.Math.Lemmas.cancel_mul_div i n
  in aux()

let same_buffer_same_upviews #src #bt b h0 h1 =
    let dv = get_downview b in 
    let s0 = DV.as_seq h0 dv in
    let s1 = DV.as_seq h1 dv in
    let aux (i:nat{i < DV.length dv}) : Lemma (Seq.index s0 i == Seq.index s1 i) =
      DV.as_seq_sel h0 dv i;
      DV.as_seq_sel h1 dv i;
      DV.get_sel h0 dv i;
      DV.get_sel h1 dv i
    in Classical.forall_intro aux;
    Seq.lemma_eq_intro s0 s1;
    DV.length_eq dv;
    BufferViewHelpers.lemma_uv_equal (LSig.view_of_base_typ bt) dv h0 h1

let same_immbuffer_same_upviews #src #bt b h0 h1 =
    let dv = get_downview b in 
    let s0 = DV.as_seq h0 dv in
    let s1 = DV.as_seq h1 dv in
    let aux (i:nat{i < DV.length dv}) : Lemma (Seq.index s0 i == Seq.index s1 i) =
      DV.as_seq_sel h0 dv i;
      DV.as_seq_sel h1 dv i;
      DV.get_sel h0 dv i;
      DV.get_sel h1 dv i
    in Classical.forall_intro aux;
    Seq.lemma_eq_intro s0 s1;
    DV.length_eq dv;
    BufferViewHelpers.lemma_uv_equal (LSig.view_of_base_typ bt) dv h0 h1
