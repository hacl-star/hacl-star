module Vale.X64.Decls
open FStar.Mul
open Vale.X64.Machine_s
open Vale.X64
open Vale.X64.State
open Vale.X64.StateLemmas
open FStar.UInt
module P = Vale.X64.Print_s
module BC = Vale.X64.Bytes_Code_s
module BS = Vale.X64.Machine_Semantics_s
#reset-options "--max_fuel 0 --max_ifuel 0 --smtencoding.elim_box true --smtencoding.l_arith_repr boxwrap --smtencoding.nl_arith_repr boxwrap --z3cliopt smt.arith.nl=true --using_facts_from 'Prims FStar.UInt Vale.Def.Words_s FStar.UInt64'"
let lemma_mul_in_bounds (x y:nat64) : Lemma (requires x * y < pow2_64) (ensures FStar.UInt.mul_mod #64 x y == x * y) = ()

#reset-options "--z3cliopt smt.arith.nl=true --using_facts_from Prims --using_facts_from FStar.Math"
let lemma_mul_nat (x:nat) (y:nat) : Lemma (ensures 0 <= (x * y)) = ()
#reset-options "--initial_fuel 2 --max_fuel 2"

let cf flags = match Lemmas.cf flags with | Some v -> v | None -> false
let overflow flags = match Lemmas.overflow flags with | Some v -> v | None -> false
let valid_cf flags = match Lemmas.cf flags with | Some v -> true | None -> false
let valid_of flags = match Lemmas.overflow flags with | Some v -> true | None -> false
let updated_cf new_flags new_cf = Lemmas.cf new_flags = Some new_cf
let updated_of new_flags new_cf = Lemmas.overflow new_flags = Some new_cf
let maintained_cf new_flags flags = Lemmas.cf new_flags = Lemmas.cf flags
let maintained_of new_flags flags = Lemmas.overflow new_flags = Lemmas.overflow flags
let ins = BS.ins
type ocmp = BS.ocmp
type va_fuel = nat

type va_pbool = Vale.Def.PossiblyMonad.pbool
let va_ttrue () = Vale.Def.PossiblyMonad.ttrue
let va_ffalse = Vale.Def.PossiblyMonad.ffalse
let va_pbool_and x y = Vale.Def.PossiblyMonad.((&&.)) x y
let get_reason p =
  match p with
  | Vale.Def.PossiblyMonad.Ok () -> None
  | Vale.Def.PossiblyMonad.Err reason -> Some reason

let mul_nat_helper x y =
  FStar.Math.Lemmas.nat_times_nat_is_nat x y

let va_fuel_default () = 0

let lemma_opr_Mem64 (id:heaplet_id) (s:va_state) (base:va_operand) (offset:int) (b:M.buffer64) (index:int) (t:taint) : Lemma
  (requires (
    let h = Map16.sel s.vs_heap.vf_heaplets id in
    M.mem_inv s.vs_heap /\
    OReg? base /\
    valid_src_addr h b index /\
    M.valid_layout_buffer b (s.vs_heap.vf_layout) h false /\
    M.valid_taint_buf64 b h (full_heap_taint s.vs_heap) t /\
    eval_operand base s + offset == M.buffer_addr b h + 8 * index
  ))
  (ensures (
    let h = Map16.sel s.vs_heap.vf_heaplets id in
    valid_operand (va_opr_code_Mem64 id base offset t) s /\
    M.load_mem64 (M.buffer_addr b h + 8 * index) (s.vs_heap.vf_heap) == M.buffer_read b index h
  ))
  =
  Vale.X64.Memory_Sems.low_lemma_load_mem64_full b index s.vs_heap t id;
  let h = M.get_vale_heap s.vs_heap in
  let t = va_opr_code_Mem64 id base offset t in
  M.lemma_valid_mem64 b index h;
  let OMem (m, t) = t in
  assert (valid_buf_maddr64 (eval_maddr m s) h s.vs_heap.vf_layout b index t);
  M.lemma_load_mem64 b index h

let lemma_opr_Mem128 (id:heaplet_id) (s:va_state) (base:va_operand) (offset:int) (t:taint) (b:M.buffer128) (index:int) : Lemma
  (requires (
    let h = Map16.sel s.vs_heap.vf_heaplets id in
    M.mem_inv s.vs_heap /\
    OReg? base /\
    valid_src_addr h b index /\
    M.valid_layout_buffer b (s.vs_heap.vf_layout) h false /\
    M.valid_taint_buf128 b h (full_heap_taint s.vs_heap) t /\
    eval_operand base s + offset == M.buffer_addr b h + 16 * index
  ))
  (ensures (
    let h = Map16.sel s.vs_heap.vf_heaplets id in
    valid_operand128 (va_opr_code_Mem128 id base offset t) s /\
    M.load_mem128 (M.buffer_addr b h + 16 * index) (M.get_vale_heap s.vs_heap) == M.buffer_read b index h
  ))
  =
  Vale.X64.Memory_Sems.low_lemma_load_mem128_full b index s.vs_heap t id;
  let h = M.get_vale_heap s.vs_heap in
  let t = va_opr_code_Mem128 id base offset t in
  M.lemma_valid_mem128 b index h;
  let OMem (m, t) = t in
  assert (valid_buf_maddr128 (eval_maddr m s) h s.vs_heap.vf_layout b index t);
  M.lemma_load_mem128 b index h

let taint_at memTaint addr = Map.sel memTaint addr

let va_cmp_eq o1 o2 = BC.OEq o1 o2
let va_cmp_ne o1 o2 = BC.ONe o1 o2
let va_cmp_le o1 o2 = BC.OLe o1 o2
let va_cmp_ge o1 o2 = BC.OGe o1 o2
let va_cmp_lt o1 o2 = BC.OLt o1 o2
let va_cmp_gt o1 o2 = BC.OGt o1 o2

let eval_code = Lemmas.eval_code
let eval_while_inv = Lemmas.eval_while_inv

let va_ins_lemma c0 s0 = ()

let eval_ocmp = Lemmas.eval_ocmp
let valid_ocmp = Lemmas.valid_ocmp

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
let masm = P.masm
let gcc = P.gcc
