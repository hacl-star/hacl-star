module Vale.Transformers.Locations

open Vale.Arch.HeapTypes_s
open Vale.Arch.Heap
open Vale.X64.Bytes_Code_s
open Vale.X64.Instruction_s
open Vale.X64.Instructions_s
open Vale.X64.Machine_Semantics_s
open Vale.X64.Machine_s
open Vale.X64.Print_s

open Vale.Def.PossiblyMonad

module L = FStar.List.Tot

(* See fsti *)
type location : eqtype =
  | ALocMem : location
  | ALocStack: location
  | ALocReg : reg -> location
  | ALocCf : location
  | ALocOf : location

let aux_print_reg_from_location (a:location{ALocReg? a}) : string =
  let ALocReg (Reg file id) = a in
  match file with
  | 0 -> print_reg_name id
  | 1 -> print_xmm id gcc

(* See fsti *)
let disjoint_location a1 a2 =
  match a1, a2 with
  | ALocCf, ALocCf -> ffalse "carry flag not disjoint from itself"
  | ALocOf, ALocOf -> ffalse "overflow flag not disjoint from itself"
  | ALocCf, _ | ALocOf, _ | _, ALocCf | _, ALocOf -> ttrue
  | ALocMem, ALocMem -> ffalse "memory not disjoint from itself"
  | ALocStack, ALocStack -> ffalse "stack not disjoint from itself"
  | ALocMem, ALocStack | ALocStack, ALocMem -> ttrue
  | ALocReg r1, ALocReg r2 ->
    (r1 <> r2) /- ("register " ^ aux_print_reg_from_location a1 ^ " not disjoint from itself")
  | ALocReg _, _ | _, ALocReg _ -> ttrue

(* See fsti *)
let auto_lemma_disjoint_location a1 a2 = ()

(* See fsti *)
let downgrade_val_raise_val_u0_u1 #a x = FStar.Universe.downgrade_val_raise_val #a x

(* See fsti *)
let location_val_t a =
  match a with
  | ALocMem -> heap_impl
  | ALocStack -> FStar.Universe.raise_t (machine_stack & memTaint_t)
  | ALocReg r -> FStar.Universe.raise_t (t_reg r)
  | ALocCf -> FStar.Universe.raise_t flag_val_t
  | ALocOf -> FStar.Universe.raise_t flag_val_t

(* See fsti *)
let location_val_eqt a =
  match a with
  | ALocMem -> unit
  | ALocStack -> unit
  | ALocReg r -> t_reg r
  | ALocCf -> flag_val_t
  | ALocOf -> flag_val_t

(* See fsti *)
let eval_location a s =
  match a with
  | ALocMem -> s.ms_heap
  | ALocStack -> FStar.Universe.raise_val (s.ms_stack, s.ms_stackTaint)
  | ALocReg r -> FStar.Universe.raise_val (eval_reg r s)
  | ALocCf -> FStar.Universe.raise_val (cf s.ms_flags)
  | ALocOf -> FStar.Universe.raise_val (overflow s.ms_flags)

(* See fsti *)
let update_location a v s =
  match a with
  | ALocMem ->
    let v = coerce v in
    { s with ms_heap = v }
  | ALocStack ->
    let v = FStar.Universe.downgrade_val (coerce v) in
    { s with ms_stack = fst v ; ms_stackTaint = snd v }
  | ALocReg r ->
    let v = FStar.Universe.downgrade_val v in
    update_reg' r v s
  | ALocCf ->
    let v = FStar.Universe.downgrade_val v in
    { s with ms_flags = FStar.FunctionalExtensionality.on_dom flag (fun f -> if f = fCarry then v else s.ms_flags f) }
  | ALocOf ->
    let v = FStar.Universe.downgrade_val v in
    { s with ms_flags = FStar.FunctionalExtensionality.on_dom flag (fun f -> if f = fOverflow then v else s.ms_flags f) }

(* See fsti *)
let lemma_locations_truly_disjoint a a_change v s = ()

(* See fsti *)
let lemma_locations_complete s1 s2 flags ok trace =
  let s1, s2 =
    filter_state s1 flags ok trace,
    filter_state s2 flags ok trace in
  assert (s1.ms_ok == s2.ms_ok);
  FStar.Classical.forall_intro (
    (fun r ->
       assert (eval_location (ALocReg r) s1 == eval_location (ALocReg r) s2) (* OBSERVE *)
    ) <: (r:_ -> Lemma (eval_reg r s1 == eval_reg r s2))
  );
  assert (FStar.FunctionalExtensionality.feq s1.ms_regs s2.ms_regs);
  assert (s1.ms_regs == s2.ms_regs);
  assert (overflow s1.ms_flags == overflow s2.ms_flags);
  assert (cf s1.ms_flags == cf s2.ms_flags);
  assert (FStar.FunctionalExtensionality.feq s1.ms_flags s2.ms_flags);
  assert (s1.ms_heap == s2.ms_heap);
  assert (s1.ms_stack == s2.ms_stack);
  assert (s1.ms_stackTaint == s2.ms_stackTaint);
  assert (s1.ms_trace == s2.ms_trace)

(* See fsti *)
let lemma_locations_same_with_filter s flags ok trace = ()
