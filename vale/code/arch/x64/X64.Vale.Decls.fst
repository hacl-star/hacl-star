module X64.Vale.Decls
open X64.Machine_s
open X64.Vale
open X64.Vale.State
open X64.Vale.StateLemmas
open FStar.UInt
module P = X64.Print_s
module BS = X64.Bytes_Semantics_s
module TS = X64.Taint_Semantics_s

#reset-options "--max_fuel 0 --max_ifuel 0 --smtencoding.elim_box true --smtencoding.l_arith_repr boxwrap --smtencoding.nl_arith_repr boxwrap --z3cliopt smt.arith.nl=true --using_facts_from 'Prims FStar.UInt Words_s FStar.UInt64'"
let lemma_mul_in_bounds (x y:nat64) : Lemma (requires x `op_Multiply` y < pow2_64) (ensures FStar.UInt.mul_mod #64 x y == x `op_Multiply` y) = ()

#reset-options "--z3cliopt smt.arith.nl=true --using_facts_from Prims --using_facts_from FStar.Math"
let lemma_mul_nat (x:nat) (y:nat) : Lemma (ensures 0 <= (x `op_Multiply` y)) = ()
#reset-options "--initial_fuel 2 --max_fuel 2"

let cf = Lemmas.cf
let overflow = Lemmas.overflow
let update_cf (flags:int) (new_cf:bool) = Lemmas.update_cf flags new_cf
let update_of (flags:int) (new_of:bool) = Lemmas.update_of flags new_of
let ins = TS.tainted_ins
type ocmp = TS.tainted_ocmp
type va_fuel = nat
let va_fuel_default () = 0

let va_opr_lemma_Mem s base offset b index t =
  let t = va_opr_code_Mem base offset t in
  M.lemma_valid_mem64 b index s.mem;
  let TMem m t = t in
  assert (valid_maddr (eval_maddr m s) s.mem s.memTaint b index t);
  M.lemma_load_mem64 b index s.mem

let va_opr_lemma_Stack s base offset = ()

let va_opr_lemma_Mem128 s base offset t b index =
  let t = va_opr_code_Mem128 base offset t in
  M.lemma_valid_mem128 b index s.mem;
  let TMem128 m t = t in
  assert (valid_maddr128 (eval_maddr m s) s.mem s.memTaint b index t);
  M.lemma_load_mem128 b index s.mem

let taint_at memTaint addr = Map.sel memTaint addr

let va_cmp_eq o1 o2 = TS.TaintedOCmp (BS.OEq (t_op_to_op o1) (t_op_to_op o2)) Public
let va_cmp_ne o1 o2 = TS.TaintedOCmp (BS.ONe (t_op_to_op o1) (t_op_to_op o2)) Public
let va_cmp_le o1 o2 = TS.TaintedOCmp (BS.OLe (t_op_to_op o1) (t_op_to_op o2)) Public
let va_cmp_ge o1 o2 = TS.TaintedOCmp (BS.OGe (t_op_to_op o1) (t_op_to_op o2)) Public
let va_cmp_lt o1 o2 = TS.TaintedOCmp (BS.OLt (t_op_to_op o1) (t_op_to_op o2)) Public
let va_cmp_gt o1 o2 = TS.TaintedOCmp (BS.OGt (t_op_to_op o1) (t_op_to_op o2)) Public

let eval_code = Lemmas.eval_code
let eval_while_inv = Lemmas.eval_while_inv
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
