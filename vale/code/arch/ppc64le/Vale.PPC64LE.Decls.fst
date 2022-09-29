module Vale.PPC64LE.Decls
open Vale.PPC64LE.Machine_s
open Vale.PPC64LE.State
open Vale.PPC64LE.StateLemmas
module S = Vale.PPC64LE.Semantics_s
module P = Vale.PPC64LE.Print_s
friend Vale.PPC64LE.Memory

let same_heap_types = ()

let xer_ov = Lemmas.xer_ov
let xer_ca = Lemmas.xer_ca
let update_xer_ov = Lemmas.update_xer_ov
let update_xer_ca = Lemmas.update_xer_ca
let ins = S.ins
type ocmp = S.ocmp
type va_fuel = nat

type va_pbool = Vale.Def.PossiblyMonad.pbool
let va_ttrue () = Vale.Def.PossiblyMonad.ttrue
let va_ffalse = Vale.Def.PossiblyMonad.ffalse
let va_pbool_and x y = Vale.Def.PossiblyMonad.((&&.)) x y

let mul_nat_helper x y =
  FStar.Math.Lemmas.nat_times_nat_is_nat x y

let va_fuel_default () = 0

let lemma_opr_Mem64 (id:heaplet_id) (s:va_state) (address:reg_opr) (offset:int) (b:M.buffer64) (index:int) (t:taint) : Lemma
  (requires (
    let h = Map16.sel s.ms_heap.vf_heaplets id in
    M.mem_inv (coerce s.ms_heap) /\
    valid_src_addr h b index /\
    M.valid_layout_buffer b (s.ms_heap.vf_layout) h false /\
    M.valid_taint_buf64 b h (full_heap_taint s.ms_heap) t /\
    eval_reg address s + offset == M.buffer_addr b h + 8 * index
  ))
  (ensures (
    let h = Map16.sel s.ms_heap.vf_heaplets id in
    valid_mem_addr (va_opr_code_Mem64 id address offset t) s /\
    M.load_mem64 (M.buffer_addr b h + 8 * index) (s.ms_heap.vf_heap) == M.buffer_read b index h
  ))
  =
  Vale.PPC64LE.Memory_Sems.low_lemma_load_mem64_full b index s.ms_heap t id;
  let h = M.get_vale_heap s.ms_heap in
  let t = va_opr_code_Mem64 id address offset t in
  M.lemma_valid_mem64 b index h;
  let (m, t) = t in
  assert (valid_buf_maddr64 (eval_maddr m s) h s.ms_heap.vf_layout b index t);
  M.lemma_load_mem64 b index h

let va_cmp_eq o1 o2 = S.OEq o1 o2
let va_cmp_ne o1 o2 = S.ONe o1 o2
let va_cmp_le o1 o2 = S.OLe o1 o2
let va_cmp_ge o1 o2 = S.OGe o1 o2
let va_cmp_lt o1 o2 = S.OLt o1 o2
let va_cmp_gt o1 o2 = S.OGt o1 o2

let eval_code = Lemmas.eval_code
let eval_while_inv = Lemmas.eval_while_inv

let va_ins_lemma c0 s0 = ()

let eval_ocmp = Lemmas.eval_ocmp
let valid_ocmp = Lemmas.valid_ocmp
let eval_cmp_cr0 = S.eval_cmp_cr0

unfold let va_eval_ins = Lemmas.eval_ins

let lemma_cmp_eq s o1 o2 = ()
let lemma_cmp_ne s o1 o2 = ()
let lemma_cmp_le s o1 o2 = ()
let lemma_cmp_ge s o1 o2 = ()
let lemma_cmp_lt s o1 o2 = ()
let lemma_cmp_gt s o1 o2 = ()

let lemma_valid_cmp_eq s o1 o2 = ()
let lemma_valid_cmp_ne s o1 o2 = ()
let lemma_valid_cmp_le s o1 o2 = ()
let lemma_valid_cmp_ge s o1 o2 = ()
let lemma_valid_cmp_lt s o1 o2 = ()
let lemma_valid_cmp_gt s o1 o2 = ()

let va_compute_merge_total = Lemmas.compute_merge_total
let va_lemma_merge_total b0 s0 f0 sM fM sN = Lemmas.lemma_merge_total b0 s0 f0 sM fM sN; Lemmas.compute_merge_total f0 fM
let va_lemma_empty_total = Lemmas.lemma_empty_total
let va_lemma_ifElse_total = Lemmas.lemma_ifElse_total
let va_lemma_ifElseTrue_total = Lemmas.lemma_ifElseTrue_total
let va_lemma_ifElseFalse_total = Lemmas.lemma_ifElseFalse_total
let va_lemma_while_total = Lemmas.lemma_while_total
let va_lemma_whileTrue_total = Lemmas.lemma_whileTrue_total
let va_lemma_whileFalse_total = Lemmas.lemma_whileFalse_total
let va_lemma_whileMerge_total = Lemmas.lemma_whileMerge_total

let printer = P.printer
let print_string = FStar.IO.print_string
let print_header = P.print_header
let print_proc = P.print_proc
let print_footer = P.print_footer
let gcc = P.gcc
