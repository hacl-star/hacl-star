module X64.Vale.Decls
module M = X64.Memory
module S = X64.Stack_i

// This interface should hide all of Semantics_s.
// (It should not refer to Semantics_s, directly or indirectly.)
// It should not refer to StateLemmas, Lemmas, or Print_s,
// because they refer to Semantics_s.
// Stack_i, Memory, Regs and State are ok, because they do not refer to Semantics_s.

open Prop_s
open X64.Machine_s
open X64.Vale.State
open Types_s

unfold let quad32 = quad32

val cf : (flags:int) -> bool
val overflow (flags:int) : bool
val update_cf (flags:int) (new_cf:bool) : (new_flags:int { cf new_flags == new_cf /\ 
                                                       overflow new_flags == overflow flags} )
val update_of (flags:int) (new_of:bool) : (new_flags:int { overflow new_flags == new_of /\
                                                       cf new_flags == cf flags })

//unfold let va_subscript = Map.sel
unfold let va_subscript (#a:eqtype) (#b:Type) (x:Map.t a b) (y:a) : Tot b = Map.sel x y
unfold let va_update = Map.upd
unfold let va_make_opaque = Opaque_s.make_opaque
unfold let va_reveal_opaque = Opaque_s.reveal_opaque
unfold let va_hd = Cons?.hd
//unfold let va_tl = Cons?.tl // F* inlines "let ... = va_tl ..." more than we'd like; revised definition below suppresses this

// hide 'if' so that x and y get fully normalized
let va_if (#a:Type) (b:bool) (x:(_:unit{b}) -> GTot a) (y:(_:unit{~b}) -> GTot a) : GTot a =
  if b then x () else y ()

(* Define a tainted operand to wrap the base operand type *)
[@va_qattr]
type tainted_operand:eqtype =
| TConst: n:int -> tainted_operand
| TReg: r:reg -> tainted_operand
| TMem: m:maddr -> t:taint -> tainted_operand
| TStack: m:maddr -> tainted_operand


[@va_qattr]
type tainted_operand128:eqtype =
| TReg128: x:xmm -> tainted_operand128
| TMem128: m:maddr -> t:taint -> tainted_operand128

[@va_qattr]
unfold let t_op_to_op (t:tainted_operand) : operand =
  match t with
  | TConst n -> OConst n
  | TReg r -> OReg r
  | TMem m _ -> OMem m
  | TStack m -> OStack m
  

[@va_qattr]
unfold let t_op_to_op128 (t:tainted_operand128) : mov128_op =
  match t with
  | TReg128 r -> Mov128Xmm r
  | TMem128 m _ -> Mov128Mem m

let get_taint (t:tainted_operand) : taint =
  match t with
  | TConst _ -> Public
  | TReg _ -> Public
  | TMem _ t -> t
  | TStack _ -> Public

let extract_taint (o1 o2:tainted_operand) : taint =
  if TMem? o1 then TMem?.t o1
  else if TMem? o2 then TMem?.t o2
  else Public

let extract_taint3 (o1 o2 o3:tainted_operand) : taint =
  if TMem? o1 then TMem?.t o1
  else if TMem? o2 then TMem?.t o2
  else if TMem? o3 then TMem?.t o3
  else Public

(* Type aliases *)
unfold let va_bool = bool
unfold let va_prop = prop0
unfold let va_int = int
let va_int_at_least (k:int) = i:int{i >= k}
let va_int_at_most (k:int) = i:int{i <= k}
let va_int_range (k1 k2:int) = i:int{k1 <= i /\ i <= k2}
val ins : eqtype
val ocmp : eqtype
unfold let va_code = precode ins ocmp
unfold let va_codes = list va_code
let va_tl (cs:va_codes) : Ghost va_codes (requires Cons? cs) (ensures fun tl -> tl == Cons?.tl cs) = Cons?.tl cs
unfold let va_state = state
val va_fuel : Type0
unfold let va_operand = tainted_operand
unfold let va_operand_opr64 = va_operand
let va_reg_operand = o:va_operand{OReg? (t_op_to_op o)}
let va_operand_reg_opr64 = o:va_operand{OReg? (t_op_to_op o)}
unfold let va_dst_operand = o:va_operand
unfold let va_operand_dst_opr64 = o:va_operand
unfold let va_shift_amt = o:va_operand
unfold let va_operand_shift_amt64 = o:va_operand
unfold let va_cmp = o:va_operand{not (TMem? o)}
unfold let va_register = reg
unfold let va_operand_xmm = xmm
unfold let va_operand128 = tainted_operand128
unfold let va_operand_opr128 = va_operand128

[@va_qattr] unfold let va_expand_state (s:state) : state = state_eta s

(* Abbreviations *)
unfold let get_reg (o:va_reg_operand) : reg = OReg?.r (t_op_to_op o)
unfold let buffer_readable (#t:M.base_typ) (h:M.mem) (b:M.buffer t) : GTot prop0 = M.buffer_readable #t h b
unfold let buffer_writeable (#t:M.base_typ) (b:M.buffer t) : GTot prop0 = M.buffer_writeable #t b
unfold let buffer_length (#t:M.base_typ) (b:M.buffer t) = M.buffer_length #t b
unfold let buffer8_as_seq (m:M.mem) (b:M.buffer8) : GTot (Seq.seq nat8) = M.buffer_as_seq m b
unfold let buffer64_as_seq (m:M.mem) (b:M.buffer64) : GTot (Seq.seq nat64) = M.buffer_as_seq m b
unfold let s64 (m:M.mem) (b:M.buffer64) : GTot (Seq.seq nat64) = buffer64_as_seq m b
unfold let buffer128_as_seq (m:M.mem) (b:M.buffer128) : GTot (Seq.seq quad32) = M.buffer_as_seq m b
unfold let s128 (m:M.mem) (b:M.buffer128) : GTot (Seq.seq quad32) = buffer128_as_seq m b
unfold let valid_src_addr (#t:M.base_typ) (m:M.mem) (b:M.buffer t) (i:int) : prop0 =
  0 <= i /\ i < buffer_length b /\ buffer_readable m b
unfold let valid_dst_addr (#t:M.base_typ) (m:M.mem) (b:M.buffer t) (i:int) : prop0 =
  0 <= i /\ i < buffer_length b /\ buffer_readable m b /\ buffer_writeable b
unfold let buffer64_read (b:M.buffer64) (i:int) (m:M.mem) : GTot nat64 = M.buffer_read b i m
unfold let buffer64_write (b:M.buffer64) (i:int) (v:nat64) (m:M.mem) : GTot M.mem =
  if FStar.StrongExcludedMiddle.strong_excluded_middle (buffer_readable m b /\ buffer_writeable b) then
    M.buffer_write b i v m else m
unfold let buffer128_read (b:M.buffer128) (i:int) (m:M.mem) : GTot quad32 = M.buffer_read b i m
unfold let buffer128_write (b:M.buffer128) (i:int) (v:quad32) (m:M.mem) : GTot M.mem =
  if FStar.StrongExcludedMiddle.strong_excluded_middle (buffer_readable m b /\ buffer_writeable b) then
    M.buffer_write b i v m else m
unfold let modifies_mem (s:M.loc) (h1 h2:M.mem) : GTot prop0 = M.modifies s h1 h2
unfold let loc_buffer(#t:M.base_typ) (b:M.buffer t) = M.loc_buffer #t b
unfold let locs_disjoint = M.locs_disjoint
unfold let loc_union = M.loc_union

let valid_maddr (addr:int) (s_mem:M.mem) (s_memTaint:M.memtaint) (b:M.buffer64) (index:int) (t:taint) : prop0 =
  valid_src_addr s_mem b index /\
  M.valid_taint_buf64 b s_mem s_memTaint t /\
  addr == M.buffer_addr b s_mem + 8 `op_Multiply` index

let valid_maddr128 (addr:int) (s_mem:M.mem) (s_memTaint:M.memtaint) (b:M.buffer128) (index:int) (t:taint) : prop0 =
  valid_src_addr s_mem b index /\
  M.valid_taint_buf128 b s_mem s_memTaint t /\
  addr == M.buffer_addr b s_mem + 16 `op_Multiply` index

let valid_mem_operand (addr:int) (t:taint) (s_mem:M.mem) (s_memTaint:M.memtaint) : prop0 =
  exists (b:M.buffer64) (index:int).{:pattern (valid_maddr addr s_mem s_memTaint b index t)}
    valid_maddr addr s_mem s_memTaint b index t

let valid_mem_operand128 (addr:int) (t:taint) (s_mem:M.mem) (s_memTaint:M.memtaint) : prop0 =
  exists (b:M.buffer128) (index:int).{:pattern (valid_maddr128 addr s_mem s_memTaint b index t)}
    valid_maddr128 addr s_mem s_memTaint b index t

[@va_qattr]
let valid_operand (t:tainted_operand) (s:state) : prop0 =
  X64.Vale.State.valid_src_operand (t_op_to_op t) s /\
  (match t with TMem m t -> valid_mem_operand (eval_maddr m s) t s.mem s.memTaint | _ -> True)

[@va_qattr]
let valid_operand128 (t:tainted_operand128) (s:state) : prop0 =
  X64.Vale.State.valid_src_operand128 (t_op_to_op128 t) s /\
  (match t with TMem128 m t -> valid_mem_operand128 (eval_maddr m s) t s.mem s.memTaint | _ -> True)

(* Constructors *)
val va_fuel_default : unit -> va_fuel
[@va_qattr] unfold let va_op_operand_reg (r:reg) : va_operand = TReg r
[@va_qattr] unfold let va_op_xmm_xmm (x:xmm) : va_operand_xmm = x
[@va_qattr] unfold let va_op_opr_reg (r:reg) : va_operand = TReg r
[@va_qattr] unfold let va_op_opr64_reg (r:reg) : va_operand = TReg r
[@va_qattr] unfold let va_op_reg64_reg (r:reg) : va_operand = TReg r
[@va_qattr] unfold let va_op_opr128_xmm (x:xmm) : va_operand128 = TReg128 x
[@va_qattr] unfold let va_const_operand (n:int) = TConst n
[@va_qattr] unfold let va_const_opr64 (n:int) = TConst n
[@va_qattr] unfold let va_const_shift_amt (n:int) : va_shift_amt = TConst n
[@va_qattr] unfold let va_const_shift_amt64 (n:int) : va_shift_amt = TConst n
[@va_qattr] unfold let va_op_shift_amt_reg (r:reg) : va_shift_amt = TReg r
[@va_qattr] unfold let va_op_shift_amt64_reg (r:reg) : va_shift_amt = TReg r
[@va_qattr] unfold let va_op_cmp_reg (r:reg) : va_cmp = TReg r
[@va_qattr] unfold let va_const_cmp (n:int) : va_cmp = TConst n
[@va_qattr] unfold let va_coerce_reg_opr64_to_cmp (r:va_operand_reg_opr64) : va_cmp = r
[@va_qattr] unfold let va_coerce_register_to_operand (r:va_register) : va_operand = TReg r
[@va_qattr] unfold let va_coerce_operand_to_reg_operand (o:va_operand{OReg? (t_op_to_op o)}) : va_reg_operand = o
[@va_qattr] unfold let va_coerce_dst_operand_to_reg_operand (o:va_dst_operand{OReg? (t_op_to_op o)}) : va_reg_operand = o
[@va_qattr] unfold let va_coerce_reg_opr64_to_dst_opr64 (o:va_operand_reg_opr64) : va_operand_dst_opr64 = o
[@va_qattr] unfold let va_coerce_reg_opr64_to_opr64 (o:va_operand_reg_opr64) : va_operand_opr64 = o
[@va_qattr] unfold let va_coerce_operand_to_cmp (o:va_operand{not (TMem? o)}) : va_cmp = o
[@va_qattr] unfold let va_coerce_opr64_to_cmp (o:va_operand{not (TMem? o)}) : va_cmp = o
[@va_qattr] unfold let va_op_register (r:reg) : va_register = r
[@va_qattr] unfold let va_op_reg_oprerand_reg (r:reg) : va_reg_operand = TReg r
[@va_qattr] unfold let va_op_reg_opr64_reg (r:reg) : va_reg_operand = TReg r
[@va_qattr] unfold let va_op_dst_operand_reg (r:reg) : va_dst_operand = TReg r
[@va_qattr] unfold let va_op_dst_opr64_reg (r:reg) : va_dst_operand = TReg r
[@va_qattr] unfold let va_coerce_operand_to_dst_operand (o:va_operand) : va_dst_operand = o
[@va_qattr] unfold let va_coerce_dst_operand_to_operand (o:va_dst_operand) : va_operand = o
[@va_qattr] unfold let va_coerce_dst_opr64_to_opr64 (o:va_dst_operand) : va_operand = o
[@va_qattr] unfold let va_coerce_xmm_to_opr128 (x:xmm) : va_operand128 = TReg128 x

[@va_qattr]
unfold let va_opr_code_Mem (o:va_operand) (offset:int) (t:taint) : va_operand =
  match o with
  | TConst n -> TMem (MConst (n + offset)) t
  | TReg r -> TMem (MReg r offset) t
  | _ -> TMem (MConst 42) t

val va_opr_lemma_Mem (s:va_state) (base:va_operand) (offset:int) (b:M.buffer64) (index:int) (t:taint) : Lemma
  (requires
    TReg? base /\
    valid_src_addr s.mem b index /\
    M.valid_taint_buf64 b s.mem s.memTaint t /\
    eval_operand (t_op_to_op base) s + offset == M.buffer_addr b s.mem + 8 `op_Multiply` index
  )
  (ensures
    valid_operand (va_opr_code_Mem base offset t) s /\
    M.load_mem64 (M.buffer_addr b s.mem + 8 `op_Multiply` index) s.mem == M.buffer_read b index s.mem
  )

[@va_qattr]
unfold let va_opr_code_Stack (o:va_operand) (offset:int) : va_operand =
  match o with
  | TConst n -> TStack (MConst (n + offset))
  | TReg r -> TStack (MReg r offset)
  | _ -> TStack (MConst 42)

val va_opr_lemma_Stack (s:va_state) (base:va_operand) (offset:int) : Lemma
  (requires
    TReg? base /\
    S.valid_src_stack64 (eval_operand (t_op_to_op base) s + offset) s.stack
  )
  (ensures True)

[@va_qattr]
unfold let va_opr_code_Mem128 (o:va_operand) (offset:int) (t:taint) : va_operand128 =
  match o with
  | TReg r -> TMem128 (MReg r offset) t
  | _ -> TMem128 (MConst 42) t

val va_opr_lemma_Mem128 (s:va_state) (base:va_operand) (offset:int) (t:taint) (b:M.buffer128) (index:int) : Lemma
  (requires
    TReg? base /\
    valid_src_addr s.mem b index /\
    M.valid_taint_buf128 b s.mem s.memTaint t /\
    eval_operand (t_op_to_op base) s + offset == M.buffer_addr b s.mem + 16 `op_Multiply` index
  )
  (ensures
    valid_operand128 (va_opr_code_Mem128 base offset t) s /\
    M.load_mem128 (M.buffer_addr b s.mem + 16 `op_Multiply` index) s.mem == M.buffer_read b index s.mem
  )

val taint_at (memTaint:M.memtaint) (addr:int) : taint

(* Evaluation *)
[@va_qattr] unfold let va_eval_opr64        (s:va_state) (o:va_operand)     : GTot nat64 = eval_operand (t_op_to_op o) s
[@va_qattr] unfold let va_eval_dst_opr64    (s:va_state) (o:va_dst_operand) : GTot nat64 = eval_operand (t_op_to_op o) s
[@va_qattr] unfold let va_eval_shift_amt64  (s:va_state) (o:va_shift_amt)   : GTot nat64 = eval_operand (t_op_to_op o) s
[@va_qattr] unfold let va_eval_cmp_uint64   (s:va_state) (r:va_cmp)         : GTot nat64 = eval_operand (t_op_to_op r) s
[@va_qattr] unfold let va_eval_reg64        (s:va_state) (r:va_register)    : GTot nat64 = eval_reg r s
[@va_qattr] unfold let va_eval_reg_opr64    (s:va_state) (o:va_operand)     : GTot nat64 = eval_operand (t_op_to_op o) s
[@va_qattr] unfold let va_eval_xmm          (s:va_state) (x:xmm)            : GTot quad32 = eval_xmm x s
[@va_qattr] unfold let va_eval_opr128       (s:va_state) (o:va_operand128)  : GTot quad32 = eval_operand128 (t_op_to_op128 o) s

(* Predicates *)
[@va_qattr] unfold let va_is_src_opr64 (o:va_operand) (s:va_state) = valid_operand o s
[@va_qattr] let va_is_dst_opr64 (o:va_operand) (s:va_state) = match (t_op_to_op o) with OReg Rsp -> false | OReg _ -> true | _ -> false
[@va_qattr] unfold let va_is_dst_dst_opr64 (o:va_dst_operand) (s:va_state) = va_is_dst_opr64 o s
[@va_qattr] unfold let va_is_src_reg (r:reg) (s:va_state) = True
[@va_qattr] unfold let va_is_dst_reg (r:reg) (s:va_state) = True
[@va_qattr] unfold let va_is_src_shift_amt64 (o:va_operand) (s:va_state) = valid_operand o s /\ (va_eval_shift_amt64 s o) < 64
[@va_qattr] unfold let va_is_src_reg_opr64 (o:va_operand) (s:va_state) = OReg? (t_op_to_op o)
[@va_qattr] unfold let va_is_dst_reg_opr64 (o:va_operand) (s:va_state) = OReg? (t_op_to_op o) /\ not (Rsp? (OReg?.r (t_op_to_op o)))
[@va_qattr] unfold let va_is_src_xmm (x:xmm) (s:va_state) = True
[@va_qattr] unfold let va_is_dst_xmm (x:xmm) (s:va_state) = True
[@va_qattr] unfold let va_is_src_opr128 (o:va_operand128) (s:va_state) = valid_operand128 o s
[@va_qattr] unfold let va_is_dst_opr128 (o:va_operand128) (s:va_state) = valid_operand128 o s

(* Getters *)
[@va_qattr] unfold let va_get_ok (s:va_state) : bool = s.ok
[@va_qattr] unfold let va_get_flags (s:va_state) : int = s.flags
[@va_qattr] unfold let va_get_reg (r:reg) (s:va_state) : nat64 = eval_reg r s
[@va_qattr] unfold let va_get_xmm (x:xmm) (s:va_state) : quad32 = eval_xmm x s
[@va_qattr] unfold let va_get_mem (s:va_state) : M.mem = s.mem
[@va_qattr] unfold let va_get_stack (s:va_state) : S.stack = s.stack
[@va_qattr] unfold let va_get_memTaint (s:va_state) : M.memtaint = s.memTaint

[@va_qattr] let va_upd_ok (ok:bool) (s:state) : state = { s with ok = ok }
[@va_qattr] let va_upd_flags (flags:nat64) (s:state) : state = { s with flags = flags }
[@va_qattr] let va_upd_reg (r:reg) (v:nat64) (s:state) : state = update_reg r v s
[@va_qattr] let va_upd_xmm (x:xmm) (v:quad32) (s:state) : state = update_xmm x v s
[@va_qattr] let va_upd_mem (mem:M.mem) (s:state) : state = { s with mem = mem }
[@va_qattr] let va_upd_stack (stack:S.stack) (s:state) : state = { s with stack = stack }
[@va_qattr] let va_upd_memTaint (memTaint:M.memtaint) (s:state) : state = { s with memTaint = memTaint }

(* Framing: va_update_foo means the two states are the same except for foo *)
[@va_qattr] unfold let va_update_ok (sM:va_state) (sK:va_state) : va_state = va_upd_ok sM.ok sK
[@va_qattr] unfold let va_update_flags (sM:va_state) (sK:va_state) : va_state = va_upd_flags sM.flags sK
[@va_qattr] unfold let va_update_reg (r:reg) (sM:va_state) (sK:va_state) : va_state =
  va_upd_reg r (eval_reg r sM) sK
[@va_qattr] unfold let va_update_xmm (x:xmm) (sM:va_state) (sK:va_state) : va_state =
  va_upd_xmm x (eval_xmm x sM) sK
[@va_qattr] unfold let va_update_mem (sM:va_state) (sK:va_state) : va_state = va_upd_mem sM.mem sK
[@va_qattr] unfold let va_update_stack (sM:va_state) (sK:va_state) : va_state = va_upd_stack sM.stack sK
[@va_qattr] unfold let va_update_memTaint (sM:va_state) (sK:va_state) : va_state = va_upd_memTaint sM.memTaint sK

[@va_qattr]
let va_update_operand (o:va_operand) (sM:va_state) (sK:va_state) : va_state =
  match (t_op_to_op o) with
  | OConst n -> sK
  | OReg r -> va_update_reg r sM sK
  | OMem m -> va_update_mem sM sK
  | OStack m -> va_update_stack sM sK

[@va_qattr] unfold
let va_update_dst_operand (o:va_operand) (sM:va_state) (sK:va_state) : va_state =
  va_update_operand o sM sK

[@va_qattr] unfold
let va_update_operand_dst_opr64 (o:va_operand) (sM:va_state) (sK:va_state) : va_state =
  va_update_dst_operand o sM sK

[@va_qattr] unfold
let va_update_operand_opr64 (o:va_operand) (sM:va_state) (sK:va_state) : va_state =
  va_update_dst_operand o sM sK

[@va_qattr] unfold
let va_update_register (r:reg) (sM:va_state) (sK:va_state) : va_state =
  va_update_reg r sM sK

[@va_qattr] unfold
let va_update_operand_reg_opr64 (o:va_operand) (sM:va_state) (sK:va_state) : va_state =
  va_update_dst_operand o sM sK

[@va_qattr] unfold
let va_update_operand_xmm (x:xmm) (sM:va_state) (sK:va_state) : va_state =
  update_xmm x (eval_xmm x sM) sK

unfold let va_value_opr64 = nat64
unfold let va_value_dst_opr64 = nat64
unfold let va_value_reg_opr64 = nat64
unfold let va_value_xmm = quad32

[@va_qattr]
let va_upd_operand_xmm (x:xmm) (v:quad32) (s:state) : state =
  update_xmm x v s

[@va_qattr]
let va_upd_operand_dst_opr64 (o:va_operand) (v:nat64) (s:state) =
  match (t_op_to_op o) with
  | OConst n -> s
  | OReg r -> update_reg r v s
  | OMem m -> s // TODO: support destination memory operands
  | OStack m -> s // TODO: support destination stack operands

[@va_qattr]
let va_upd_operand_reg_opr64 (o:va_operand) (v:nat64) (s:state) =
  match (t_op_to_op o) with
  | OConst n -> s
  | OReg r -> update_reg r v s
  | OMem m -> s
  | OStack m -> s

let va_lemma_upd_update (sM:state) : Lemma
  (
    (forall (sK:state) (o:va_operand).{:pattern (va_update_operand_dst_opr64 o sM sK)} va_is_dst_dst_opr64 o sK ==> va_update_operand_dst_opr64 o sM sK == va_upd_operand_dst_opr64 o (eval_operand (t_op_to_op o) sM) sK) /\
    (forall (sK:state) (o:va_operand).{:pattern (va_update_operand_reg_opr64 o sM sK)} va_is_dst_reg_opr64 o sK ==> va_update_operand_reg_opr64 o sM sK == va_upd_operand_reg_opr64 o (eval_operand (t_op_to_op o) sM) sK) /\
    (forall (sK:state) (x:xmm).{:pattern (va_update_operand_xmm x sM sK)} va_update_operand_xmm x sM sK == va_upd_operand_xmm x (eval_xmm x sM) sK)
  )
  = ()

(** Constructors for va_codes *)
[@va_qattr] unfold let va_CNil () : va_codes = []
[@va_qattr] unfold let va_CCons (hd:va_code) (tl:va_codes) : va_codes = hd::tl

(** Constructors for va_code *)
unfold let va_Block (block:va_codes) : va_code = Block block
unfold let va_IfElse (ifCond:ocmp) (ifTrue:va_code) (ifFalse:va_code) : va_code = IfElse ifCond ifTrue ifFalse
unfold let va_While (whileCond:ocmp) (whileBody:va_code) : va_code = While whileCond whileBody

val va_cmp_eq (o1:va_operand{ not (TMem? o1 || TStack? o1) }) (o2:va_operand{ not (TMem? o2 || TStack? o2) }) : ocmp
val va_cmp_ne (o1:va_operand{ not (TMem? o1 || TStack? o1) }) (o2:va_operand{ not (TMem? o2 || TStack? o2) }) : ocmp
val va_cmp_le (o1:va_operand{ not (TMem? o1 || TStack? o1) }) (o2:va_operand{ not (TMem? o2 || TStack? o2) }) : ocmp
val va_cmp_ge (o1:va_operand{ not (TMem? o1 || TStack? o1) }) (o2:va_operand{ not (TMem? o2 || TStack? o2) }) : ocmp
val va_cmp_lt (o1:va_operand{ not (TMem? o1 || TStack? o1) }) (o2:va_operand{ not (TMem? o2 || TStack? o2) }) : ocmp
val va_cmp_gt (o1:va_operand{ not (TMem? o1 || TStack? o1) }) (o2:va_operand{ not (TMem? o2 || TStack? o2) }) : ocmp

unfold let va_get_block (c:va_code{Block? c}) : va_codes = Block?.block c
unfold let va_get_ifCond (c:va_code{IfElse? c}) : ocmp = IfElse?.ifCond c
unfold let va_get_ifTrue (c:va_code{IfElse? c}) : va_code = IfElse?.ifTrue c
unfold let va_get_ifFalse (c:va_code{IfElse? c}) : va_code = IfElse?.ifFalse c
unfold let va_get_whileCond (c:va_code{While? c}) : ocmp = While?.whileCond c
unfold let va_get_whileBody (c:va_code{While? c}) : va_code = While?.whileBody c

(** Map syntax **)

//unfold let op_String_Access (m:M.mem) (b:M.buffer64) = fun index -> buffer64_read b index m

// syntax for map accesses, m.[key] and m.[key] <- value
(*
type map (key:eqtype) (value:Type) = Map.t key value
let op_String_Access     = Map.sel
let op_String_Assignment = Map.upd
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
let rec buffers_readable (h: M.mem) (l: list M.buffer64) : GTot prop0 (decreases l) =
    match l with
    | [] -> True
    | b :: l'  -> buffer_readable h b /\ buffers_readable h l'

unfold let modifies_none (h1 h2:M.mem) = modifies_mem M.loc_none h1 h2
unfold let modifies_buffer (b:M.buffer64) (h1 h2:M.mem) = modifies_mem (loc_buffer b) h1 h2
unfold let modifies_buffer_2 (b1 b2:M.buffer64) (h1 h2:M.mem) =modifies_mem (M.loc_union (loc_buffer b1) (loc_buffer b2)) h1 h2
unfold let modifies_buffer_3 (b1 b2 b3:M.buffer64) (h1 h2:M.mem) =modifies_mem (M.loc_union (M.loc_union (loc_buffer b1) (loc_buffer b2)) (loc_buffer b3)) h1 h2
unfold let modifies_buffer128 (b:M.buffer128) (h1 h2:M.mem) = modifies_mem (loc_buffer b) h1 h2
unfold let modifies_buffer128_2 (b1 b2:M.buffer128) (h1 h2:M.mem) = modifies_mem (M.loc_union (loc_buffer b1) (loc_buffer b2)) h1 h2
unfold let modifies_buffer128_3 (b1 b2 b3:M.buffer128) (h1 h2:M.mem) = modifies_mem (M.loc_union (M.loc_union (loc_buffer b1) (loc_buffer b2)) (loc_buffer b3)) h1 h2

let validSrcAddrs64 (m:M.mem) (addr:int) (b:M.buffer64) (len:int) (memTaint:M.memtaint) (t:taint) =
    buffer_readable m b /\
    len <= buffer_length b /\
    M.buffer_addr b m == addr /\
    M.valid_taint_buf64 b m memTaint t

let validDstAddrs64 (m:M.mem) (addr:int) (b:M.buffer64) (len:int) (memTaint:M.memtaint) (t:taint) =
    buffer_readable m b /\
    buffer_writeable b /\
    len <= buffer_length b /\
    M.buffer_addr b m == addr /\
    M.valid_taint_buf64 b m memTaint t

let validSrcAddrs128 (m:M.mem) (addr:int) (b:M.buffer128) (len:int) (memTaint:M.memtaint) (t:taint) =
    buffer_readable m b /\
    len <= buffer_length b /\
    M.buffer_addr b m == addr /\
    M.valid_taint_buf128 b m memTaint t

let validDstAddrs128 (m:M.mem) (addr:int) (b:M.buffer128) (len:int) (memTaint:M.memtaint) (t:taint) =
    buffer_readable m b /\
    buffer_writeable b /\
    len <= buffer_length b /\
    M.buffer_addr b m == addr /\
    M.valid_taint_buf128 b m memTaint t

let validSrcAddrsOffset128 (m:M.mem) (addr:int) (b:M.buffer128) (offset len:int) (memTaint:M.memtaint) (t:taint) =
    buffer_readable m b /\
    offset + len <= buffer_length b /\
    M.buffer_addr b m + 16 `op_Multiply` offset == addr /\
    M.valid_taint_buf128 b m memTaint t

let validDstAddrsOffset128 (m:M.mem) (addr:int) (b:M.buffer128) (offset len:int) (memTaint:M.memtaint) (t:taint) =
    buffer_readable m b /\
    buffer_writeable b /\
    offset + len <= buffer_length b /\
    M.buffer_addr b m + 16 `op_Multiply` offset == addr /\
    M.valid_taint_buf128 b m memTaint t

let modifies_buffer_specific128 (b:M.buffer128) (h1 h2:M.mem) (start last:nat) : GTot prop0 =
    modifies_buffer128 b h1 h2 /\
    // TODO: Consider replacing this with: modifies (loc_buffer (gsub_buffer b i len)) h1 h2
    (forall (i:nat) . {:pattern (Seq.index (M.buffer_as_seq h2 b) i)}
                        0 <= i /\ i < buffer_length b
                     /\ (i < start || i > last)
                    ==> buffer128_read b i h1
                     == buffer128_read b i h2)

let buffer_modifies_specific128 (b:M.buffer128) (h1 h2:M.mem) (start last:nat) : GTot prop0 =
    // TODO: Consider replacing this with: modifies (loc_buffer (gsub_buffer b i len)) h1 h2
    (forall (i:nat) . {:pattern (Seq.index (M.buffer_as_seq h2 b) i)}
                        0 <= i /\ i < buffer_length b
                     /\ (i < start || i > last)
                    ==> buffer128_read b i h1
                     == buffer128_read b i h2)

let modifies_buffer_specific (b:M.buffer64) (h1 h2:M.mem) (start last:nat) : GTot prop0 =
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
let buffer_disjoints128 (l:M.buffer128) (ls:list (M.buffer128)) : prop0 = normalize (loc_locs_disjoint_rec128 l ls)

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

val lemma_cmp_eq : s:va_state -> o1:va_operand{ not (TMem? o1 || TStack? o1) } -> o2:va_operand{ not (TMem? o2 || TStack? o2) } -> Lemma
  (requires True)
  (ensures  (eval_ocmp s (va_cmp_eq o1 o2)) <==> (va_eval_opr64 s o1 == va_eval_opr64 s o2))
  [SMTPat (eval_ocmp s (va_cmp_eq o1 o2))]

val lemma_cmp_ne : s:va_state -> o1:va_operand{ not (TMem? o1 || TStack? o1) } -> o2:va_operand{ not (TMem? o2 || TStack? o2) } -> Lemma
  (requires True)
  (ensures  (eval_ocmp s (va_cmp_ne o1 o2)) <==> (va_eval_opr64 s o1 <> va_eval_opr64 s o2))
  [SMTPat (eval_ocmp s (va_cmp_ne o1 o2))]

val lemma_cmp_le : s:va_state -> o1:va_operand{ not (TMem? o1 || TStack? o1) } -> o2:va_operand{ not (TMem? o2 || TStack? o2) } -> Lemma
  (requires True)
  (ensures  (eval_ocmp s (va_cmp_le o1 o2)) <==> (va_eval_opr64 s o1 <= va_eval_opr64 s o2))
  [SMTPat (eval_ocmp s (va_cmp_le o1 o2))]

val lemma_cmp_ge : s:va_state -> o1:va_operand{ not (TMem? o1 || TStack? o1) } -> o2:va_operand{ not (TMem? o2 || TStack? o2) } -> Lemma
  (requires True)
  (ensures  (eval_ocmp s (va_cmp_ge o1 o2)) <==> (va_eval_opr64 s o1 >= va_eval_opr64 s o2))
  [SMTPat (eval_ocmp s (va_cmp_ge o1 o2))]

val lemma_cmp_lt : s:va_state -> o1:va_operand{ not (TMem? o1 || TStack? o1) } -> o2:va_operand{ not (TMem? o2 || TStack? o2) } -> Lemma
  (requires True)
  (ensures  (eval_ocmp s (va_cmp_lt o1 o2)) <==> (va_eval_opr64 s o1 < va_eval_opr64 s o2))
  [SMTPat (eval_ocmp s (va_cmp_lt o1 o2))]

val lemma_cmp_gt : s:va_state -> o1:va_operand{ not (TMem? o1 || TStack? o1) } -> o2:va_operand{ not (TMem? o2 || TStack? o2) } -> Lemma
  (requires True)
  (ensures  (eval_ocmp s (va_cmp_gt o1 o2)) <==> (va_eval_opr64 s o1 > va_eval_opr64 s o2))
  [SMTPat (eval_ocmp s (va_cmp_gt o1 o2))]

val lemma_valid_cmp_eq : s:va_state -> o1:va_operand{ not (TMem? o1 || TStack? o1) } -> o2:va_operand{ not (TMem? o2 || TStack? o2) } -> Lemma
  (requires True)
  (ensures  (valid_operand o1 s /\ valid_operand o2 s) ==> (valid_ocmp (va_cmp_eq o1 o2) s))
  [SMTPat (valid_ocmp (va_cmp_eq o1 o2) s)]

val lemma_valid_cmp_ne : s:va_state -> o1:va_operand{ not (TMem? o1 || TStack? o1) } -> o2:va_operand{ not (TMem? o2 || TStack? o2) } -> Lemma
  (requires True)
  (ensures (valid_operand o1 s /\ valid_operand o2 s) ==> (valid_ocmp (va_cmp_ne o1 o2) s))
  [SMTPat (valid_ocmp (va_cmp_ne o1 o2) s)]

val lemma_valid_cmp_le : s:va_state -> o1:va_operand{ not (TMem? o1 || TStack? o1) } -> o2:va_operand{ not (TMem? o2 || TStack? o2) } -> Lemma
  (requires True)
  (ensures (valid_operand o1 s /\ valid_operand o2 s) ==> (valid_ocmp (va_cmp_le o1 o2) s))
  [SMTPat (valid_ocmp (va_cmp_le o1 o2) s)]

val lemma_valid_cmp_ge : s:va_state -> o1:va_operand{ not (TMem? o1 || TStack? o1) } -> o2:va_operand{ not (TMem? o2 || TStack? o2) } -> Lemma
  (requires True)
  (ensures (valid_operand o1 s /\ valid_operand o2 s) ==> (valid_ocmp (va_cmp_ge o1 o2) s))
  [SMTPat (valid_ocmp (va_cmp_ge o1 o2) s)]

val lemma_valid_cmp_lt : s:va_state -> o1:va_operand{ not (TMem? o1 || TStack? o1) } -> o2:va_operand{ not (TMem? o2 || TStack? o2) } -> Lemma
  (requires True)
  (ensures (valid_operand o1 s /\ valid_operand o2 s) ==> (valid_ocmp (va_cmp_lt o1 o2) s))
  [SMTPat (valid_ocmp (va_cmp_lt o1 o2) s)]

val lemma_valid_cmp_gt : s:va_state -> o1:va_operand{ not (TMem? o1 || TStack? o1) } -> o2:va_operand{ not (TMem? o2 || TStack? o2) } -> Lemma
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

val va_lemma_empty_total (s0:va_state) (bN:va_codes) : Ghost ((sM:va_state) * (fM:va_fuel))
  (requires True)
  (ensures (fun (sM, fM) ->
    s0 == sM /\
    eval_code (va_Block []) s0 fM sM
  ))

val va_lemma_ifElse_total (ifb:ocmp) (ct:va_code) (cf:va_code) (s0:va_state) : Ghost (bool * va_state * va_state * va_fuel)
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

val va_lemma_while_total (b:ocmp) (c:va_code) (s0:va_state) : Ghost ((s1:va_state) * (f1:va_fuel))
  (requires True)
  (ensures fun (s1, f1) ->
    s1 == s0 /\
    eval_while_inv (While b c) s1 f1 s1
  )

val va_lemma_whileTrue_total (b:ocmp) (c:va_code) (s0:va_state) (sW:va_state) (fW:va_fuel) : Ghost ((s1:va_state) * (f1:va_fuel))
  (requires eval_ocmp sW b /\ valid_ocmp b sW)
  (ensures fun (s1, f1) -> s1 == sW /\ f1 == fW)

val va_lemma_whileFalse_total (b:ocmp) (c:va_code) (s0:va_state) (sW:va_state) (fW:va_fuel) : Ghost ((s1:va_state) * (f1:va_fuel))
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
    sN.ok /\
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

// There can only be one!
[@va_qattr]
let max_one_mem (o1 o2:va_operand) : prop0 =
  match (o1, o2) with
  | (TMem _ _, TMem _ _) | (TMem _ _, TStack _) | (TStack _, TMem _ _) | (TStack _, TStack _) -> False
  | _ -> True

