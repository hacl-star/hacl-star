module Vale.X64.Decls
open FStar.Mul
module M = Vale.X64.Memory
module S = Vale.X64.Stack_i

// This interface should hide all of Machine_Semantics_s.
// (It should not refer to Machine_Semantics_s, directly or indirectly.)
// It should not refer to StateLemmas, Lemmas, or Print_s,
// because they refer to Machine_Semantics_s.
// Stack_i, Memory, Regs, Flags and State are ok, because they do not refer to Machine_Semantics_s.

open Vale.Def.Prop_s
open Vale.X64.Machine_s
open Vale.X64.State
open Vale.Def.Types_s

unfold let vale_heap = M.vale_heap
unfold let vale_heap_impl = M.vale_heap_impl
unfold let quad32 = quad32

val cf (flags:Flags.t) : bool
val overflow (flags:Flags.t) : bool
val valid_cf (flags:Flags.t) : bool
val valid_of (flags:Flags.t) : bool
val updated_cf (new_flags:Flags.t) (new_cf:bool) : (b:bool { b <==> (
                                                       cf new_flags == new_cf /\
						       valid_cf new_flags ) } )
val updated_of (new_flags:Flags.t) (new_of:bool) : (b:bool { b <==> (
                                                       overflow new_flags == new_of /\
						       valid_of new_flags ) } )
val maintained_cf (new_flags:Flags.t) (flags:Flags.t) : (b:bool { b <==> (
                                                       cf new_flags == cf flags /\
						       valid_cf new_flags == valid_cf flags ) } )
val maintained_of (new_flags:Flags.t) (flags:Flags.t) : (b:bool { b <==> (
                                                       overflow new_flags == overflow flags /\
						       valid_of new_flags == valid_of flags ) } )

//unfold let va_subscript = Map.sel
unfold let va_subscript (#a:eqtype) (#b:Type) (x:Map.t a b) (y:a) : Tot b = Map.sel x y
unfold let va_update = Map.upd
unfold let va_make_opaque = Vale.Def.Opaque_s.make_opaque
unfold let va_hd = Cons?.hd
//unfold let va_tl = Cons?.tl // F* inlines "let ... = va_tl ..." more than we'd like; revised definition below suppresses this

// REVIEW: FStar.Pervasives.reveal_opaque doesn't include zeta, so it fails for recursive functions
[@va_qattr] unfold let va_reveal_eq (#ax:Type) (s:string) (x x':ax) = norm [zeta; delta_only [s]] #ax x == x'
let va_reveal_opaque (s:string) = norm_spec [zeta; delta_only [s]]

// hide 'if' so that x and y get fully normalized
let va_if (#a:Type) (b:bool) (x:(_:unit{b}) -> GTot a) (y:(_:unit{~b}) -> GTot a) : GTot a =
  if b then x () else y ()

let total_if (#a:Type) (b:bool) (x y:a) : a =
  if b then x else y

let total_thunk_if (#a:Type) (b:bool) (x:(_:unit{b}) -> a) (y:(_:unit{~b}) -> a) : a =
  if b then x () else y ()

(* Type aliases *)
unfold let va_bool = bool
unfold let va_prop = prop0
unfold let va_int = int
let va_int_at_least (k:int) = i:int{i >= k}
let va_int_at_most (k:int) = i:int{i <= k}
let va_int_range (k1 k2:int) = i:int{k1 <= i /\ i <= k2}
val ins : Type0
val ocmp : eqtype
unfold let va_code = precode ins ocmp
unfold let va_codes = list va_code
let va_tl (cs:va_codes) : Ghost va_codes (requires Cons? cs) (ensures fun tl -> tl == Cons?.tl cs) = Cons?.tl cs
unfold let va_state = vale_state
val va_fuel : Type0
unfold let va_operand = operand64
unfold let va_operand_opr64 = va_operand
let va_reg_operand = o:va_operand{OReg? o}
let va_operand_reg_opr64 = o:va_operand{OReg? o}
unfold let va_dst_operand = va_operand
unfold let va_operand_dst_opr64 = va_operand
unfold let va_shift_amt = o:va_operand
unfold let va_operand_shift_amt64 = va_operand
unfold let va_cmp = o:va_operand{not (OMem? o)}
//unfold let va_register = reg_64
unfold let va_operand_xmm = reg_xmm
unfold let va_operand128 = operand128
unfold let va_operand_opr128 = va_operand128

val va_pbool : Type0
val va_ttrue (_:unit) : va_pbool
val va_ffalse (reason:string) : va_pbool
val va_pbool_and (x y:va_pbool) : va_pbool
val get_reason (p:va_pbool) : option string

noeq
type va_transformation_result = {
  success : va_pbool;
  result : va_code;
}
unfold let va_get_success (r:va_transformation_result) : va_pbool = r.success
unfold let va_get_result (r:va_transformation_result) : va_code = r.result

val mul_nat_helper (x y:nat) : Lemma (x * y >= 0)
[@va_qattr] unfold let va_mul_nat (x y:nat) : nat =
  mul_nat_helper x y;
  x * y

[@va_qattr] unfold let va_expand_state (s:vale_state) : vale_state = state_eta s

unfold let get_reg (o:va_reg_operand) : reg = Reg 0 (OReg?.r o)
unfold let buffer_readable (#t:M.base_typ) (h:vale_heap) (b:M.buffer t) : GTot prop0 = M.buffer_readable #t h b
unfold let buffer_writeable (#t:M.base_typ) (b:M.buffer t) : GTot prop0 = M.buffer_writeable #t b
unfold let buffer_length (#t:M.base_typ) (b:M.buffer t) = M.buffer_length #t b
unfold let buffer8_as_seq (m:vale_heap) (b:M.buffer8) : GTot (Seq.seq nat8) = M.buffer_as_seq m b
unfold let buffer64_as_seq (m:vale_heap) (b:M.buffer64) : GTot (Seq.seq nat64) = M.buffer_as_seq m b
unfold let s64 (m:vale_heap) (b:M.buffer64) : GTot (Seq.seq nat64) = buffer64_as_seq m b
unfold let buffer128_as_seq (m:vale_heap) (b:M.buffer128) : GTot (Seq.seq quad32) = M.buffer_as_seq m b
unfold let s128 (m:vale_heap) (b:M.buffer128) : GTot (Seq.seq quad32) = buffer128_as_seq m b
unfold let valid_src_addr (#t:M.base_typ) (m:vale_heap) (b:M.buffer t) (i:int) : prop0 = M.valid_buffer_read m b i
unfold let valid_dst_addr (#t:M.base_typ) (m:vale_heap) (b:M.buffer t) (i:int) : prop0 = M.valid_buffer_write m b i
unfold let buffer64_read (b:M.buffer64) (i:int) (m:vale_heap) : GTot nat64 = M.buffer_read b i m
let buffer64_write (b:M.buffer64) (i:int) (v:nat64) (m:vale_heap) : GTot vale_heap =
  if FStar.StrongExcludedMiddle.strong_excluded_middle (buffer_readable m b /\ buffer_writeable b) then
    M.buffer_write b i v m else m
unfold let buffer128_read (b:M.buffer128) (i:int) (m:vale_heap) : GTot quad32 = M.buffer_read b i m
let buffer128_write (b:M.buffer128) (i:int) (v:quad32) (m:vale_heap) : GTot vale_heap =
  if FStar.StrongExcludedMiddle.strong_excluded_middle (buffer_readable m b /\ buffer_writeable b) then
    M.buffer_write b i v m else m
unfold let modifies_mem (s:M.loc) (h1 h2:vale_heap) : GTot prop0 = M.modifies s h1 h2
unfold let loc_buffer(#t:M.base_typ) (b:M.buffer t) = M.loc_buffer #t b
unfold let locs_disjoint = M.locs_disjoint
unfold let loc_union = M.loc_union

let valid_buf_maddr64 (addr:int) (s_mem:vale_heap) (s_memTaint:M.memtaint) (b:M.buffer64) (index:int) (t:taint) : prop0 =
  valid_src_addr s_mem b index /\
  M.valid_taint_buf64 b s_mem s_memTaint t /\
  addr == M.buffer_addr b s_mem + 8 * index

let valid_buf_maddr128 (addr:int) (s_mem:vale_heap) (s_memTaint:M.memtaint) (b:M.buffer128) (index:int) (t:taint) : prop0 =
  valid_src_addr s_mem b index /\
  M.valid_taint_buf128 b s_mem s_memTaint t /\
  addr == M.buffer_addr b s_mem + 16 * index

let valid_mem_operand64 (addr:int) (t:taint) (s_mem:vale_heap) (s_memTaint:M.memtaint) : prop0 =
  exists (b:M.buffer64) (index:int).{:pattern (valid_buf_maddr64 addr s_mem s_memTaint b index t)}
    valid_buf_maddr64 addr s_mem s_memTaint b index t

let valid_mem_operand128 (addr:int) (t:taint) (s_mem:vale_heap) (s_memTaint:M.memtaint) : prop0 =
  exists (b:M.buffer128) (index:int).{:pattern (valid_buf_maddr128 addr s_mem s_memTaint b index t)}
    valid_buf_maddr128 addr s_mem s_memTaint b index t

[@va_qattr]
let valid_operand (o:operand64) (s:vale_state) : prop0 =
  Vale.X64.State.valid_src_operand o s /\
  ( match o with
    | OMem (m, t) -> valid_mem_operand64 (eval_maddr m s) t (M.get_vale_heap s.vs_heap) s.vs_memTaint
    | OStack (m, t) -> S.valid_taint_stack64 (eval_maddr m s) t s.vs_stackTaint
    | _ -> True
  )

[@va_qattr]
let valid_operand128 (o:operand128) (s:vale_state) : prop0 =
  Vale.X64.State.valid_src_operand128 o s /\
  ( match o with
    | OMem (m, t) -> valid_mem_operand128 (eval_maddr m s) t (M.get_vale_heap s.vs_heap) s.vs_memTaint
    | OStack (m, t) -> S.valid_taint_stack128 (eval_maddr m s) t s.vs_stackTaint
    | _ -> True
  )

(* Constructors *)
val va_fuel_default : unit -> va_fuel
[@va_qattr] unfold let va_op_operand_reg64 (r:reg_64) : va_operand = OReg r
[@va_qattr] unfold let va_op_xmm_xmm (x:reg_xmm) : va_operand_xmm = x
[@va_qattr] unfold let va_op_opr_reg (r:reg_64) : va_operand = OReg r
[@va_qattr] unfold let va_op_opr64_reg64 (r:reg_64) : va_operand = OReg r
[@va_qattr] unfold let va_op_reg64_reg64 (r:reg_64) : va_operand = OReg r
[@va_qattr] unfold let va_op_opr128_xmm (x:reg_xmm) : va_operand128 = OReg x
[@va_qattr] unfold let va_const_operand (n:nat64) : va_operand = OConst n
[@va_qattr] unfold let va_const_opr64 (n:nat64) : va_operand = OConst n
[@va_qattr] unfold let va_const_shift_amt (n:nat64) : va_shift_amt = OConst n
[@va_qattr] unfold let va_const_shift_amt64 (n:nat64) : va_shift_amt = OConst n
[@va_qattr] unfold let va_op_shift_amt_reg64 (r:reg_64) : va_shift_amt = OReg r
[@va_qattr] unfold let va_op_shift_amt64_reg64 (r:reg_64) : va_shift_amt = OReg r
[@va_qattr] unfold let va_op_cmp_reg64 (r:reg_64) : va_cmp = OReg r
[@va_qattr] unfold let va_const_cmp (n:nat64) : va_cmp = OConst n
[@va_qattr] unfold let va_coerce_reg64_opr64_to_cmp (r:va_operand_reg_opr64) : va_cmp = r
//[@va_qattr] unfold let va_coerce_register_to_operand (r:va_register) : va_operand = OReg r
[@va_qattr] unfold let va_coerce_operand_to_reg_operand (o:va_operand{OReg? o}) : va_reg_operand = o
[@va_qattr] unfold let va_coerce_dst_operand_to_reg_operand (o:va_dst_operand{OReg? o}) : va_reg_operand = o
[@va_qattr] unfold let va_coerce_reg_opr64_to_dst_opr64 (o:va_operand_reg_opr64) : va_operand_dst_opr64 = o
[@va_qattr] unfold let va_coerce_reg_opr64_to_opr64 (o:va_operand_reg_opr64) : va_operand_opr64 = o
[@va_qattr] unfold let va_coerce_operand_to_cmp (o:va_operand{not (OMem? o)}) : va_cmp = o
[@va_qattr] unfold let va_coerce_opr64_to_cmp (o:va_operand{not (OMem? o)}) : va_cmp = o
//[@va_qattr] unfold let va_op_register (r:reg_64) : va_register = r
//[@va_qattr] unfold let va_op_reg_oprerand_reg (r:reg_64) : va_reg_operand = OReg r
[@va_qattr] unfold let va_op_reg_opr64_reg64 (r:reg_64) : va_reg_operand = OReg r
[@va_qattr] unfold let va_op_dst_operand_reg64 (r:reg_64) : va_dst_operand = OReg r
[@va_qattr] unfold let va_op_dst_opr64_reg64 (r:reg_64) : va_dst_operand = OReg r
[@va_qattr] unfold let va_coerce_operand_to_dst_operand (o:va_operand) : va_dst_operand = o
[@va_qattr] unfold let va_coerce_dst_operand_to_operand (o:va_dst_operand) : va_operand = o
[@va_qattr] unfold let va_coerce_dst_opr64_to_opr64 (o:va_dst_operand) : va_operand = o
[@va_qattr] unfold let va_coerce_xmm_to_opr128 (x:reg_xmm) : va_operand128 = OReg x

[@va_qattr]
unfold let va_opr_code_Mem (o:va_operand) (offset:int) (t:taint) : va_operand =
  match o with
  | OConst n -> OMem (MConst (n + offset), t)
  | OReg r -> OMem (MReg (Reg 0 r) offset, t)
  | _ -> OMem (MConst 42, t)

val va_opr_lemma_Mem (s:va_state) (base:va_operand) (offset:int) (b:M.buffer64) (index:int) (t:taint) : Lemma
  (requires (
    let h = M.get_vale_heap s.vs_heap in
    OReg? base /\
    valid_src_addr h b index /\
    M.valid_taint_buf64 b h s.vs_memTaint t /\
    eval_operand base s + offset == M.buffer_addr b h + 8 * index
  ))
  (ensures (
    let h = M.get_vale_heap s.vs_heap in
    valid_operand (va_opr_code_Mem base offset t) s /\
    M.load_mem64 (M.buffer_addr b h + 8 * index) h == M.buffer_read b index h
  ))

[@va_qattr]
unfold let va_opr_code_Stack (o:va_operand) (offset:int) (t:taint) : va_operand =
  match o with
  | OConst n -> OStack (MConst (n + offset), t)
  | OReg r -> OStack (MReg (Reg 0 r) offset, t)
  | _ -> OStack (MConst 42, t)

val va_opr_lemma_Stack (s:va_state) (base:va_operand) (offset:int) (t:taint) : Lemma
  (requires
    OReg? base /\
    S.valid_stack_slot64 (eval_operand base s + offset) s.vs_stack t s.vs_stackTaint
  )
  (ensures True)

[@va_qattr]
unfold let va_opr_code_Mem128 (o:va_operand) (offset:int) (t:taint) : va_operand128 =
  match o with
  | OReg r -> OMem (MReg (Reg 0 r) offset, t)
  | _ -> OMem (MConst 42, t)

val va_opr_lemma_Mem128 (s:va_state) (base:va_operand) (offset:int) (t:taint) (b:M.buffer128) (index:int) : Lemma
  (requires (
    let h = M.get_vale_heap s.vs_heap in
    OReg? base /\
    valid_src_addr h b index /\
    M.valid_taint_buf128 b h s.vs_memTaint t /\
    eval_operand base s + offset == M.buffer_addr b h + 16 * index
  ))
  (ensures (
    let h = M.get_vale_heap s.vs_heap in
    valid_operand128 (va_opr_code_Mem128 base offset t) s /\
    M.load_mem128 (M.buffer_addr b h + 16 * index) h == M.buffer_read b index h
  ))

val taint_at (memTaint:M.memtaint) (addr:int) : taint

(* Evaluation *)
[@va_qattr] unfold let va_eval_opr64        (s:va_state) (o:va_operand)     : GTot nat64 = eval_operand o s
[@va_qattr] unfold let va_eval_dst_opr64    (s:va_state) (o:va_dst_operand) : GTot nat64 = eval_operand o s
[@va_qattr] unfold let va_eval_shift_amt64  (s:va_state) (o:va_shift_amt)   : GTot nat64 = eval_operand o s
[@va_qattr] unfold let va_eval_cmp_uint64   (s:va_state) (r:va_cmp)         : GTot nat64 = eval_operand r s
//[@va_qattr] unfold let va_eval_reg64        (s:va_state) (r:va_register)    : GTot nat64 = eval_reg_64 r s
[@va_qattr] unfold let va_eval_reg_opr64    (s:va_state) (o:va_operand)     : GTot nat64 = eval_operand o s
[@va_qattr] unfold let va_eval_xmm          (s:va_state) (x:reg_xmm)            : GTot quad32 = eval_reg_xmm x s
[@va_qattr] unfold let va_eval_opr128       (s:va_state) (o:va_operand128)  : GTot quad32 = eval_operand128 o s

(* Predicates *)
[@va_qattr] unfold let va_is_src_opr64 (o:va_operand) (s:va_state) = valid_operand o s
[@va_qattr] let va_is_dst_opr64 (o:va_operand) (s:va_state) = match o with OReg r -> not (r = rRsp ) | _ -> false
[@va_qattr] unfold let va_is_dst_dst_opr64 (o:va_dst_operand) (s:va_state) = va_is_dst_opr64 o s
[@va_qattr] unfold let va_is_src_reg (r:reg_64) (s:va_state) = True
[@va_qattr] unfold let va_is_dst_reg (r:reg_64) (s:va_state) = True
[@va_qattr] unfold let va_is_src_shift_amt64 (o:va_operand) (s:va_state) = valid_operand o s /\ (va_eval_shift_amt64 s o) < 64
[@va_qattr] unfold let va_is_src_reg_opr64 (o:va_operand) (s:va_state) = OReg? o
[@va_qattr] unfold let va_is_dst_reg_opr64 (o:va_operand) (s:va_state) = OReg? o /\ not (rRsp = (OReg?.r o))
[@va_qattr] unfold let va_is_src_xmm (x:reg_xmm) (s:va_state) = True
[@va_qattr] unfold let va_is_dst_xmm (x:reg_xmm) (s:va_state) = True
[@va_qattr] unfold let va_is_src_opr128 (o:va_operand128) (s:va_state) = valid_operand128 o s
[@va_qattr] unfold let va_is_dst_opr128 (o:va_operand128) (s:va_state) = valid_operand128 o s

(* Getters *)
[@va_qattr] unfold let va_get_ok (s:va_state) : bool = s.vs_ok
[@va_qattr] unfold let va_get_flags (s:va_state) : Flags.t = s.vs_flags
[@va_qattr] unfold let va_get_reg64 (r:reg_64) (s:va_state) : nat64 = eval_reg_64 r s
[@va_qattr] unfold let va_get_xmm (x:reg_xmm) (s:va_state) : quad32 = eval_reg_xmm x s
[@va_qattr] unfold let va_get_mem (s:va_state) : vale_heap = M.get_vale_heap s.vs_heap
[@va_qattr] unfold let va_get_stack (s:va_state) : S.vale_stack = s.vs_stack
[@va_qattr] unfold let va_get_memTaint (s:va_state) : M.memtaint = s.vs_memTaint
[@va_qattr] unfold let va_get_stackTaint (s:va_state) : M.memtaint = s.vs_stackTaint

[@va_qattr] let va_upd_ok (ok:bool) (s:vale_state) : vale_state = { s with vs_ok = ok }
[@va_qattr] let va_upd_flags (flags:Flags.t) (s:vale_state) : vale_state = { s with vs_flags = flags }
[@va_qattr] let va_upd_reg (r:reg) (v:t_reg r) (s:vale_state) : vale_state = update_reg r v s
[@va_qattr] let va_upd_reg64 (r:reg_64) (v:nat64) (s:vale_state) : vale_state = update_reg_64 r v s
[@va_qattr] let va_upd_xmm (x:reg_xmm) (v:quad32) (s:vale_state) : vale_state = update_reg_xmm x v s
[@va_qattr] let va_upd_mem (mem:vale_heap) (s:vale_state) : vale_state = { s with vs_heap = M.set_vale_heap s.vs_heap mem }
[@va_qattr] let va_upd_stack (stack:S.vale_stack) (s:vale_state) : vale_state = { s with vs_stack = stack }
[@va_qattr] let va_upd_memTaint (memTaint:M.memtaint) (s:vale_state) : vale_state = { s with vs_memTaint = memTaint }
[@va_qattr] let va_upd_stackTaint (stackTaint:M.memtaint) (s:vale_state) : vale_state = { s with vs_stackTaint = stackTaint }


(* Framing: va_update_foo means the two states are the same except for foo *)
[@va_qattr] unfold let va_update_ok (sM:va_state) (sK:va_state) : va_state = va_upd_ok sM.vs_ok sK
[@va_qattr] unfold let va_update_flags (sM:va_state) (sK:va_state) : va_state = va_upd_flags sM.vs_flags sK
[@va_qattr] unfold let va_update_reg (r:reg) (sM:va_state) (sK:va_state) : va_state =
  va_upd_reg r (eval_reg r sM) sK
[@va_qattr] unfold let va_update_reg64 (r:reg_64) (sM:va_state) (sK:va_state) : va_state =
  va_upd_reg64 r (eval_reg_64 r sM) sK
[@va_qattr] unfold let va_update_xmm (x:reg_xmm) (sM:va_state) (sK:va_state) : va_state =
  va_upd_xmm x (eval_reg_xmm x sM) sK
[@va_qattr] unfold let va_update_mem (sM:va_state) (sK:va_state) : va_state = va_upd_mem (M.get_vale_heap sM.vs_heap) sK
[@va_qattr] unfold let va_update_stack (sM:va_state) (sK:va_state) : va_state = va_upd_stack sM.vs_stack sK
[@va_qattr] unfold let va_update_memTaint (sM:va_state) (sK:va_state) : va_state = va_upd_memTaint sM.vs_memTaint sK
[@va_qattr] unfold let va_update_stackTaint (sM:va_state) (sK:va_state) : va_state = va_upd_stackTaint sM.vs_stackTaint sK

[@va_qattr]
let va_update_operand (o:va_operand) (sM:va_state) (sK:va_state) : va_state =
  match o with
  | OConst n -> sK
  | OReg r -> va_update_reg64 r sM sK
  | OMem (m, _) -> va_update_mem sM sK
  | OStack (m, _) -> va_update_stack sM sK

[@va_qattr] unfold
let va_update_dst_operand (o:va_operand) (sM:va_state) (sK:va_state) : va_state =
  va_update_operand o sM sK

[@va_qattr] unfold
let va_update_operand_dst_opr64 (o:va_operand) (sM:va_state) (sK:va_state) : va_state =
  va_update_dst_operand o sM sK

[@va_qattr] unfold
let va_update_operand_opr64 (o:va_operand) (sM:va_state) (sK:va_state) : va_state =
  va_update_dst_operand o sM sK

//[@va_qattr] unfold
//let va_update_register (r:reg_64) (sM:va_state) (sK:va_state) : va_state =
//  va_update_reg r sM sK

[@va_qattr] unfold
let va_update_operand_reg_opr64 (o:va_operand) (sM:va_state) (sK:va_state) : va_state =
  va_update_dst_operand o sM sK

[@va_qattr] unfold
let va_update_operand_xmm (x:reg_xmm) (sM:va_state) (sK:va_state) : va_state =
  update_reg_xmm x (eval_reg_xmm x sM) sK

unfold let va_value_opr64 = nat64
unfold let va_value_dst_opr64 = nat64
unfold let va_value_reg_opr64 = nat64
unfold let va_value_xmm = quad32

[@va_qattr]
let va_upd_operand_xmm (x:reg_xmm) (v:quad32) (s:vale_state) : vale_state =
  update_reg_xmm x v s

[@va_qattr]
let va_upd_operand_dst_opr64 (o:va_operand) (v:nat64) (s:vale_state) =
  match o with
  | OConst n -> s
  | OReg r -> update_reg_64 r v s
  | OMem (m, _) -> s // TODO: support destination memory operands
  | OStack (m, _) -> s // TODO: support destination stack operands

[@va_qattr]
let va_upd_operand_reg_opr64 (o:va_operand) (v:nat64) (s:vale_state) =
  match o with
  | OConst n -> s
  | OReg r -> update_reg_64 r v s
  | OMem (m, _) -> s
  | OStack (m, _) -> s

let va_lemma_upd_update (sM:vale_state) : Lemma
  (
    (forall (sK:vale_state) (o:va_operand).{:pattern (va_update_operand_dst_opr64 o sM sK)} va_is_dst_dst_opr64 o sK ==> va_update_operand_dst_opr64 o sM sK == va_upd_operand_dst_opr64 o (eval_operand o sM) sK) /\
    (forall (sK:vale_state) (o:va_operand).{:pattern (va_update_operand_reg_opr64 o sM sK)} va_is_dst_reg_opr64 o sK ==> va_update_operand_reg_opr64 o sM sK == va_upd_operand_reg_opr64 o (eval_operand o sM) sK) /\
    (forall (sK:vale_state) (x:reg_xmm).{:pattern (va_update_operand_xmm x sM sK)} va_update_operand_xmm x sM sK == va_upd_operand_xmm x (eval_reg_xmm x sM) sK)
  )
  = ()

(** Constructors for va_codes *)
[@va_qattr] unfold let va_CNil () : va_codes = []
[@va_qattr] unfold let va_CCons (hd:va_code) (tl:va_codes) : va_codes = hd::tl

(** Constructors for va_code *)
unfold let va_Block (block:va_codes) : va_code = Block block
unfold let va_IfElse (ifCond:ocmp) (ifTrue:va_code) (ifFalse:va_code) : va_code = IfElse ifCond ifTrue ifFalse
unfold let va_While (whileCond:ocmp) (whileBody:va_code) : va_code = While whileCond whileBody

val va_cmp_eq (o1:va_operand{ not (OMem? o1 || OStack? o1) }) (o2:va_operand{ not (OMem? o2 || OStack? o2) }) : ocmp
val va_cmp_ne (o1:va_operand{ not (OMem? o1 || OStack? o1) }) (o2:va_operand{ not (OMem? o2 || OStack? o2) }) : ocmp
val va_cmp_le (o1:va_operand{ not (OMem? o1 || OStack? o1) }) (o2:va_operand{ not (OMem? o2 || OStack? o2) }) : ocmp
val va_cmp_ge (o1:va_operand{ not (OMem? o1 || OStack? o1) }) (o2:va_operand{ not (OMem? o2 || OStack? o2) }) : ocmp
val va_cmp_lt (o1:va_operand{ not (OMem? o1 || OStack? o1) }) (o2:va_operand{ not (OMem? o2 || OStack? o2) }) : ocmp
val va_cmp_gt (o1:va_operand{ not (OMem? o1 || OStack? o1) }) (o2:va_operand{ not (OMem? o2 || OStack? o2) }) : ocmp

unfold let va_get_block (c:va_code{Block? c}) : va_codes = Block?.block c
unfold let va_get_ifCond (c:va_code{IfElse? c}) : ocmp = IfElse?.ifCond c
unfold let va_get_ifTrue (c:va_code{IfElse? c}) : va_code = IfElse?.ifTrue c
unfold let va_get_ifFalse (c:va_code{IfElse? c}) : va_code = IfElse?.ifFalse c
unfold let va_get_whileCond (c:va_code{While? c}) : ocmp = While?.whileCond c
unfold let va_get_whileBody (c:va_code{While? c}) : va_code = While?.whileBody c

(** Map syntax **)

//unfold let (.[]) (m:vale_heap) (b:M.buffer64) = fun index -> buffer64_read b index m

// syntax for map accesses, m.[key] and m.[key] <- value
(*
type map (key:eqtype) (value:Type) = Map.t key value
unfold let (.[]) = Map.sel
unfold let (.[]<-) = Map.upd
*)
(** Memory framing **)

(*
unfold let in_mem (addr:int) (m:mem) : bool = m `Map.contains` addr

let disjoint (ptr1:int) (num_bytes1:int) (ptr2:int) (num_bytes2:int) =
    ptr1 + num_bytes1 <= ptr2 \/ ptr2 + num_bytes2 <= ptr1

let validSrcAddrs (mem:mem) (addr:int) (size:int) (num_bytes:int) =
    size == 64 /\
    (forall (a:int) . {:pattern (mem `Map.contains` a)} addr <= a && a < addr+num_bytes && (a - addr) % 8 = 0 ==> mem `Map.contains` a)

let memModified (old_mem:mem) (new_mem:mem) (ptr:int) (num_bytes) =
    (forall (a:int) . {:pattern (new_mem `Map.contains` a)} old_mem `Map.contains` a <==> new_mem `Map.contains` a) /\
    (forall (a:int) . {:pattern (new_mem.[a]) \/ Map.sel new_mem a} a < ptr || a >= ptr + num_bytes ==> old_mem.[a] == new_mem.[ a])
*)

(** Convenient memory-related functions **)
let rec buffers_readable (h: vale_heap) (l: list M.buffer64) : GTot prop0 (decreases l) =
    match l with
    | [] -> True
    | b :: l'  -> buffer_readable h b /\ buffers_readable h l'

unfold let modifies_none (h1 h2:vale_heap) = modifies_mem M.loc_none h1 h2
unfold let modifies_buffer (b:M.buffer64) (h1 h2:vale_heap) = modifies_mem (loc_buffer b) h1 h2
unfold let modifies_buffer_2 (b1 b2:M.buffer64) (h1 h2:vale_heap) =modifies_mem (M.loc_union (loc_buffer b1) (loc_buffer b2)) h1 h2
unfold let modifies_buffer_3 (b1 b2 b3:M.buffer64) (h1 h2:vale_heap) =modifies_mem (M.loc_union (M.loc_union (loc_buffer b1) (loc_buffer b2)) (loc_buffer b3)) h1 h2
unfold let modifies_buffer128 (b:M.buffer128) (h1 h2:vale_heap) = modifies_mem (loc_buffer b) h1 h2
unfold let modifies_buffer128_2 (b1 b2:M.buffer128) (h1 h2:vale_heap) = modifies_mem (M.loc_union (loc_buffer b1) (loc_buffer b2)) h1 h2
unfold let modifies_buffer128_3 (b1 b2 b3:M.buffer128) (h1 h2:vale_heap) = modifies_mem (M.loc_union (M.loc_union (loc_buffer b1) (loc_buffer b2)) (loc_buffer b3)) h1 h2

let validSrcAddrs64 (m:vale_heap) (addr:int) (b:M.buffer64) (len:int) (memTaint:M.memtaint) (t:taint) =
    buffer_readable m b /\
    len <= buffer_length b /\
    M.buffer_addr b m == addr /\
    M.valid_taint_buf64 b m memTaint t

let validDstAddrs64 (m:vale_heap) (addr:int) (b:M.buffer64) (len:int) (memTaint:M.memtaint) (t:taint) =
    buffer_readable m b /\
    buffer_writeable b /\
    len <= buffer_length b /\
    M.buffer_addr b m == addr /\
    M.valid_taint_buf64 b m memTaint t

let validSrcAddrs128 (m:vale_heap) (addr:int) (b:M.buffer128) (len:int) (memTaint:M.memtaint) (t:taint) =
    buffer_readable m b /\
    len <= buffer_length b /\
    M.buffer_addr b m == addr /\
    M.valid_taint_buf128 b m memTaint t

let validDstAddrs128 (m:vale_heap) (addr:int) (b:M.buffer128) (len:int) (memTaint:M.memtaint) (t:taint) =
    buffer_readable m b /\
    buffer_writeable b /\
    len <= buffer_length b /\
    M.buffer_addr b m == addr /\
    M.valid_taint_buf128 b m memTaint t

let validSrcAddrsOffset128 (m:vale_heap) (addr:int) (b:M.buffer128) (offset len:int) (memTaint:M.memtaint) (t:taint) =
    buffer_readable m b /\
    offset + len <= buffer_length b /\
    M.buffer_addr b m + 16 * offset == addr /\
    M.valid_taint_buf128 b m memTaint t

let validDstAddrsOffset128 (m:vale_heap) (addr:int) (b:M.buffer128) (offset len:int) (memTaint:M.memtaint) (t:taint) =
    buffer_readable m b /\
    buffer_writeable b /\
    offset + len <= buffer_length b /\
    M.buffer_addr b m + 16 * offset == addr /\
    M.valid_taint_buf128 b m memTaint t

let modifies_buffer_specific128 (b:M.buffer128) (h1 h2:vale_heap) (start last:nat) : GTot prop0 =
    modifies_buffer128 b h1 h2 /\
    // TODO: Consider replacing this with: modifies (loc_buffer (gsub_buffer b i len)) h1 h2
    (forall (i:nat) . {:pattern (Seq.index (M.buffer_as_seq h2 b) i)}
                        0 <= i /\ i < buffer_length b
                     /\ (i < start || i > last)
                    ==> buffer128_read b i h1
                     == buffer128_read b i h2)

let buffer_modifies_specific128 (b:M.buffer128) (h1 h2:vale_heap) (start last:nat) : GTot prop0 =
    // TODO: Consider replacing this with: modifies (loc_buffer (gsub_buffer b i len)) h1 h2
    (forall (i:nat) . {:pattern (Seq.index (M.buffer_as_seq h2 b) i)}
                        0 <= i /\ i < buffer_length b
                     /\ (i < start || i > last)
                    ==> buffer128_read b i h1
                     == buffer128_read b i h2)

let modifies_buffer_specific (b:M.buffer64) (h1 h2:vale_heap) (start last:nat) : GTot prop0 =
    modifies_buffer b h1 h2 /\
    // TODO: Consider replacing this with: modifies (loc_buffer (gsub_buffer b i len)) h1 h2
    (forall (i:nat) . {:pattern (Seq.index (M.buffer_as_seq h2 b) i)}
                        0 <= i /\ i < buffer_length b
                     /\ (i < start || i > last)
                    ==> buffer64_read b i h1
                     == buffer64_read b i h2)

unfold let buffers_disjoint (b1 b2:M.buffer64) =
    locs_disjoint [loc_buffer b1; loc_buffer b2]

unfold let buffers_disjoint128 (b1 b2:M.buffer128) =
    locs_disjoint [loc_buffer b1; loc_buffer b2]

let rec loc_locs_disjoint_rec128 (l:M.buffer128) (ls:list (M.buffer128)) : prop0 =
  match ls with
  | [] -> True
  | h::t -> locs_disjoint [loc_buffer l; loc_buffer h] /\ loc_locs_disjoint_rec128 l t

unfold
let buffer_disjoints128 (l:M.buffer128) (ls:list (M.buffer128)) : prop0 =
  norm [zeta; iota; delta_only [`%loc_locs_disjoint_rec128]] (loc_locs_disjoint_rec128 l ls)

unfold let buffers3_disjoint128 (b1 b2 b3:M.buffer128) =
    locs_disjoint [loc_buffer b1; loc_buffer b2; loc_buffer b3]

val eval_code (c:va_code) (s0:va_state) (f0:va_fuel) (sN:va_state) : prop0
val eval_while_inv (c:va_code) (s0:va_state) (fW:va_fuel) (sW:va_state) : prop0

(* ok for now but no need to actually expose the definition.
   instead expose lemmas about it *)
[@va_qattr]
let va_state_eq (s0:va_state) (s1:va_state) : prop0 = state_eq s0 s1

let va_require_total (c0:va_code) (c1:va_code) (s0:va_state) : prop0 =
  c0 == c1

let va_ensure_total (c0:va_code) (s0:va_state) (s1:va_state) (f1:va_fuel) : prop0 =
  eval_code c0 s0 f1 s1

val eval_ocmp : s:va_state -> c:ocmp -> GTot bool
unfold let va_evalCond (b:ocmp) (s:va_state) : GTot bool = eval_ocmp s b

val valid_ocmp : c:ocmp -> s:va_state -> GTot bool

val lemma_cmp_eq : s:va_state -> o1:va_operand{ not (OMem? o1 || OStack? o1) } -> o2:va_operand{ not (OMem? o2 || OStack? o2) } -> Lemma
  (requires True)
  (ensures  (eval_ocmp s (va_cmp_eq o1 o2)) <==> (va_eval_opr64 s o1 == va_eval_opr64 s o2))
  [SMTPat (eval_ocmp s (va_cmp_eq o1 o2))]

val lemma_cmp_ne : s:va_state -> o1:va_operand{ not (OMem? o1 || OStack? o1) } -> o2:va_operand{ not (OMem? o2 || OStack? o2) } -> Lemma
  (requires True)
  (ensures  (eval_ocmp s (va_cmp_ne o1 o2)) <==> (va_eval_opr64 s o1 <> va_eval_opr64 s o2))
  [SMTPat (eval_ocmp s (va_cmp_ne o1 o2))]

val lemma_cmp_le : s:va_state -> o1:va_operand{ not (OMem? o1 || OStack? o1) } -> o2:va_operand{ not (OMem? o2 || OStack? o2) } -> Lemma
  (requires True)
  (ensures  (eval_ocmp s (va_cmp_le o1 o2)) <==> (va_eval_opr64 s o1 <= va_eval_opr64 s o2))
  [SMTPat (eval_ocmp s (va_cmp_le o1 o2))]

val lemma_cmp_ge : s:va_state -> o1:va_operand{ not (OMem? o1 || OStack? o1) } -> o2:va_operand{ not (OMem? o2 || OStack? o2) } -> Lemma
  (requires True)
  (ensures  (eval_ocmp s (va_cmp_ge o1 o2)) <==> (va_eval_opr64 s o1 >= va_eval_opr64 s o2))
  [SMTPat (eval_ocmp s (va_cmp_ge o1 o2))]

val lemma_cmp_lt : s:va_state -> o1:va_operand{ not (OMem? o1 || OStack? o1) } -> o2:va_operand{ not (OMem? o2 || OStack? o2) } -> Lemma
  (requires True)
  (ensures  (eval_ocmp s (va_cmp_lt o1 o2)) <==> (va_eval_opr64 s o1 < va_eval_opr64 s o2))
  [SMTPat (eval_ocmp s (va_cmp_lt o1 o2))]

val lemma_cmp_gt : s:va_state -> o1:va_operand{ not (OMem? o1 || OStack? o1) } -> o2:va_operand{ not (OMem? o2 || OStack? o2) } -> Lemma
  (requires True)
  (ensures  (eval_ocmp s (va_cmp_gt o1 o2)) <==> (va_eval_opr64 s o1 > va_eval_opr64 s o2))
  [SMTPat (eval_ocmp s (va_cmp_gt o1 o2))]

val lemma_valid_cmp_eq : s:va_state -> o1:va_operand{ not (OMem? o1 || OStack? o1) } -> o2:va_operand{ not (OMem? o2 || OStack? o2) } -> Lemma
  (requires True)
  (ensures  (valid_operand o1 s /\ valid_operand o2 s) ==> (valid_ocmp (va_cmp_eq o1 o2) s))
  [SMTPat (valid_ocmp (va_cmp_eq o1 o2) s)]

val lemma_valid_cmp_ne : s:va_state -> o1:va_operand{ not (OMem? o1 || OStack? o1) } -> o2:va_operand{ not (OMem? o2 || OStack? o2) } -> Lemma
  (requires True)
  (ensures (valid_operand o1 s /\ valid_operand o2 s) ==> (valid_ocmp (va_cmp_ne o1 o2) s))
  [SMTPat (valid_ocmp (va_cmp_ne o1 o2) s)]

val lemma_valid_cmp_le : s:va_state -> o1:va_operand{ not (OMem? o1 || OStack? o1) } -> o2:va_operand{ not (OMem? o2 || OStack? o2) } -> Lemma
  (requires True)
  (ensures (valid_operand o1 s /\ valid_operand o2 s) ==> (valid_ocmp (va_cmp_le o1 o2) s))
  [SMTPat (valid_ocmp (va_cmp_le o1 o2) s)]

val lemma_valid_cmp_ge : s:va_state -> o1:va_operand{ not (OMem? o1 || OStack? o1) } -> o2:va_operand{ not (OMem? o2 || OStack? o2) } -> Lemma
  (requires True)
  (ensures (valid_operand o1 s /\ valid_operand o2 s) ==> (valid_ocmp (va_cmp_ge o1 o2) s))
  [SMTPat (valid_ocmp (va_cmp_ge o1 o2) s)]

val lemma_valid_cmp_lt : s:va_state -> o1:va_operand{ not (OMem? o1 || OStack? o1) } -> o2:va_operand{ not (OMem? o2 || OStack? o2) } -> Lemma
  (requires True)
  (ensures (valid_operand o1 s /\ valid_operand o2 s) ==> (valid_ocmp (va_cmp_lt o1 o2) s))
  [SMTPat (valid_ocmp (va_cmp_lt o1 o2) s)]

val lemma_valid_cmp_gt : s:va_state -> o1:va_operand{ not (OMem? o1 || OStack? o1) } -> o2:va_operand{ not (OMem? o2 || OStack? o2) } -> Lemma
  (requires True)
  (ensures (valid_operand o1 s /\ valid_operand o2 s) ==> (valid_ocmp (va_cmp_gt o1 o2) s))
  [SMTPat (valid_ocmp (va_cmp_gt o1 o2) s)]

val va_compute_merge_total (f0:va_fuel) (fM:va_fuel) : va_fuel

val va_lemma_merge_total (b0:va_codes) (s0:va_state) (f0:va_fuel) (sM:va_state) (fM:va_fuel) (sN:va_state) : Ghost (fN:va_fuel)
  (requires
    Cons? b0 /\
    eval_code (Cons?.hd b0) s0 f0 sM /\
    eval_code (va_Block (Cons?.tl b0)) sM fM sN
  )
  (ensures (fun fN ->
    fN == va_compute_merge_total f0 fM /\
    eval_code (va_Block b0) s0 fN sN
  ))

val va_lemma_empty_total (s0:va_state) (bN:va_codes) : Ghost (va_state & va_fuel)
  (requires True)
  (ensures (fun (sM, fM) ->
    s0 == sM /\
    eval_code (va_Block []) s0 fM sM
  ))

val va_lemma_ifElse_total (ifb:ocmp) (ct:va_code) (cf:va_code) (s0:va_state) : Ghost (bool & va_state & va_state & va_fuel)
  (requires True)
  (ensures  (fun (cond, sM, sN, f0) ->
    cond == eval_ocmp s0 ifb /\
    sM == s0
  ))

val va_lemma_ifElseTrue_total (ifb:ocmp) (ct:va_code) (cf:va_code) (s0:va_state) (f0:va_fuel) (sM:va_state) : Lemma
  (requires
    valid_ocmp ifb s0 /\
    eval_ocmp s0 ifb /\
    eval_code ct s0 f0 sM
  )
  (ensures
    eval_code (IfElse ifb ct cf) s0 f0 sM
  )

val va_lemma_ifElseFalse_total (ifb:ocmp) (ct:va_code) (cf:va_code) (s0:va_state) (f0:va_fuel) (sM:va_state) : Lemma
  (requires
    valid_ocmp ifb s0 /\
    not (eval_ocmp s0 ifb) /\
    eval_code cf s0 f0 sM
  )
  (ensures
    eval_code (IfElse ifb ct cf) s0 f0 sM
  )

let va_whileInv_total (b:ocmp) (c:va_code) (s0:va_state) (sN:va_state) (f0:va_fuel) : prop0 =
  eval_while_inv (While b c) s0 f0 sN

val va_lemma_while_total (b:ocmp) (c:va_code) (s0:va_state) : Ghost (va_state & va_fuel)
  (requires True)
  (ensures fun (s1, f1) ->
    s1 == s0 /\
    eval_while_inv (While b c) s1 f1 s1
  )

val va_lemma_whileTrue_total (b:ocmp) (c:va_code) (s0:va_state) (sW:va_state) (fW:va_fuel) : Ghost (va_state & va_fuel)
  (requires eval_ocmp sW b /\ valid_ocmp b sW)
  (ensures fun (s1, f1) -> s1 == sW /\ f1 == fW)

val va_lemma_whileFalse_total (b:ocmp) (c:va_code) (s0:va_state) (sW:va_state) (fW:va_fuel) : Ghost (va_state & va_fuel)
  (requires
    valid_ocmp b sW /\
    not (eval_ocmp sW b) /\
    eval_while_inv (While b c) s0 fW sW
  )
  (ensures fun (s1, f1) ->
    s1 == sW /\
    eval_code (While b c) s0 f1 s1
  )

val va_lemma_whileMerge_total (c:va_code) (s0:va_state) (f0:va_fuel) (sM:va_state) (fM:va_fuel) (sN:va_state) : Ghost (fN:va_fuel)
  (requires
    While? c /\
    sN.vs_ok /\
    valid_ocmp (While?.whileCond c) sM /\
    eval_ocmp sM (While?.whileCond c) /\
    eval_while_inv c s0 f0 sM /\
    eval_code (While?.whileBody c) sM fM sN
  )
  (ensures (fun fN ->
    eval_while_inv c s0 fN sN
  ))

val printer : Type0
val print_string : string -> FStar.All.ML unit
val print_header : printer -> FStar.All.ML unit
val print_proc : (name:string) -> (code:va_code) -> (label:int) -> (p:printer) -> FStar.All.ML int
val print_footer : printer -> FStar.All.ML unit
val masm : printer
val gcc : printer

unfold let memTaint_type = Map.t int taint

[@va_qattr]
let max_one_mem (o1 o2:va_operand) : prop0 =
  match (o1, o2) with
  | (OMem _, OMem _) | (OMem _, OStack _) | (OStack _, OMem _) | (OStack _, OStack _) -> False
  | _ -> True

