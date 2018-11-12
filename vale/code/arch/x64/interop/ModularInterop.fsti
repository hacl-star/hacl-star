module ModularInterop

module LB = LowStar.Buffer
module LBV = LowStar.BufferView
module LM = LowStar.Modifies
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module TS = X64.Taint_Semantics_s
module MS = X64.Memory_s
module M = X64.Memory
module BS = X64.Bytes_Semantics_s
module I = Interop
module IA = Interop_assumptions
module VS = X64.Vale.State
module V = X64.Vale.Decls
open FStar.Mul
open X64.Machine_s

// === for refinement types
noeq type h_equals_refine (a:Type) (x:a) : b:Type -> y:b -> Type =
  | HReflRefine : p:(a -> Type0) -> q:squash (p x) -> h_equals_refine a x (y:a{p y}) x

unfold let b8 = I.b8
val to_b8 (m:M.buffer64) : m':b8{h_equals_refine b8 m' M.buffer64 m}


let registers = reg -> nat64
let xmms_t = xmm -> quad32
let taint_map = b8 -> GTot taint

let max_arity (is_win:bool) = if is_win then 4 else 6

let register_of_arg_i (is_win:bool) (i:nat{i < max_arity is_win}) : reg =
  if is_win then
    match i with
    | 0 -> Rcx
    | 1 -> Rdx
    | 2 -> R8
    | 3 -> R9
  else
    match i with
    | 0 -> Rdi
    | 1 -> Rsi
    | 2 -> Rdx
    | 3 -> Rcx
    | 4 -> R8
    | 5 -> R9

let rec disjoint_or_eq_l_aux (b:b8) (rest:list b8) =
    match rest with
    | [] -> True
    | hd::tl -> I.disjoint_or_eq b hd /\ disjoint_or_eq_l_aux b tl

let rec disjoint_or_eq_l (roots:list b8) =
  match roots with
  | [] -> True
  | hd::tl -> disjoint_or_eq_l_aux hd tl /\ disjoint_or_eq_l tl

let rec live_l (h:HS.mem) (bs:list b8) =
  match bs with
  | [] -> True
  | hd::tl -> LB.live h hd /\ live_l h tl

let rec equiv_disjoint_or_eq_l (roots:list b8)
  : Lemma (ensures (disjoint_or_eq_l roots <==> I.list_disjoint_or_eq roots))
          [SMTPatOr [[SMTPat (disjoint_or_eq_l roots)];
                     [SMTPat (I.list_disjoint_or_eq roots)]]]
  = 
  let rec equiv_disjoint_or_eq_l_aux (b:b8) (tl:list b8) : Lemma
    (disjoint_or_eq_l_aux b tl <==> (forall p. List.memP p tl ==> I.disjoint_or_eq b p))
  = match tl with
    | [] -> ()
    | a::q -> equiv_disjoint_or_eq_l_aux b q
  in
  match roots with
    | [] -> ()
    | a::q -> 
      equiv_disjoint_or_eq_l_aux a q;
      equiv_disjoint_or_eq_l q

let rec equiv_live_l (h:HS.mem) (roots:list b8)
  : Lemma (ensures (live_l h roots <==> I.list_live h roots))
          [SMTPatOr [[SMTPat (live_l h roots)];
                     [SMTPat (I.list_live h roots)]]]
  = match roots with
    | [] -> ()
    | a::q -> equiv_live_l h q

let mem_roots_p (h0:HS.mem) (roots:list b8) =
  disjoint_or_eq_l roots /\
  live_l h0 roots

let stack_buffer = M.buffer64

let vale_pre =
    win:bool ->
    x0:M.buffer64 ->
    x1:M.buffer64 ->
    V.va_state ->
    stack_buffer ->
    prop

let vale_post =
    win:bool ->
    x0:M.buffer64 ->
    x1:M.buffer64 ->
    V.va_state ->
    stack_buffer ->
    V.va_state ->
    V.va_fuel ->
    prop

let vale_sig
    (code:V.va_code)
    (pre:vale_pre)
    (post:vale_post)
  : Type =
    win:bool ->
    x0:M.buffer64 ->
    x1:M.buffer64 ->
    va_s0:V.va_state ->
    stack_b:stack_buffer ->
    Ghost (V.va_state & V.va_fuel)
      (requires (pre win x0 x1 va_s0 stack_b))
      (ensures (fun (va_s1, f) ->
        VS.eval_reg (register_of_arg_i win 0) va_s0 == M.buffer_addr x0 va_s0.VS.mem /\
        VS.eval_reg (register_of_arg_i win 1) va_s0 == M.buffer_addr x1 va_s0.VS.mem /\
        V.eval_code code va_s0 f va_s1 /\
        // TODO: saved registers
        V.modifies_mem (M.loc_union (M.loc_buffer x0) (M.loc_buffer x1)) va_s0.VS.mem va_s1.VS.mem /\
        post win x0 x1 va_s0 stack_b va_s1 f))

let seq_nat64_to_seq_U64 (b:Seq.seq nat64) : (Seq.seq UInt64.t) =
  Seq.init (Seq.length b) (fun (i:nat{i < Seq.length b}) -> UInt64.uint_to_t (Seq.index b i))

let low_assumption (hs_mem:HS.mem) (va_mem:M.mem) (b:M.buffer64) : prop =
  LB.length (to_b8 b) == 8 * M.buffer_length b /\
  (Seq.equal
    (seq_nat64_to_seq_U64 (M.buffer_as_seq va_mem b)) (LBV.as_seq hs_mem (LBV.mk_buffer_view (to_b8 b) Views.view64)))

let low_assumptions (hs_mem:HS.mem) (va_mem:M.mem) (x0 x1:M.buffer64) : prop =
  low_assumption hs_mem va_mem x0 /\
  low_assumption hs_mem va_mem x1
//  low_assumption hs_mem va_mem sb
//  (forall (b:M.buffer64) (mem:M.mem) M.buffer_addr b mem == )
  // TODO: modifies
  // TODO: patterns
//  (forall (b:M.buffer64).{:pattern (M.buffer_length b) \/ (to_b8 b)} LB.length (to_b8 b) == 8 * M.buffer_length b) /\
//  (forall (b:M.buffer64). seq_nat64_to_seq_U64 (M.buffer_as_seq va_mem b) == LBV.as_seq hs_mem (LBV.mk_buffer_view (to_b8 b) Views.view64))
//  (forall (b:M.buffer64). M.buffer_readable va_mem b ==> LB.live hs_mem (to_b8 b))

// vp: vale_pre = fun win s0 x0 x1 = buffer_length x0 == 2

let to_low_pre
    (pre:vale_pre)
    (x0 x1:M.buffer64)
    (hs_mem:HS.mem)
  : prop =
  LB.live hs_mem (to_b8 x0) /\
  LB.live hs_mem (to_b8 x1) /\
  (forall
    (s0:V.va_state)
    (sb:stack_buffer).
    let num_stack_slots = 3 in // TODO: generalize this
    ( low_assumptions hs_mem s0.VS.mem x0 x1 /\
      s0.VS.ok /\
      M.buffer_readable s0.VS.mem x0 /\
      M.buffer_readable s0.VS.mem x1 /\
//      M.buffer_length sb >= num_stack_slots /\
      M.locs_disjoint ([M.loc_buffer sb; M.loc_buffer x0; M.loc_buffer x1]) /\
      VS.eval_reg (register_of_arg_i IA.win 0) s0 == M.buffer_addr x0 s0.VS.mem /\
      VS.eval_reg (register_of_arg_i IA.win 1) s0 == M.buffer_addr x1 s0.VS.mem /\
      M.valid_taint_buf64 x0 s0.VS.mem s0.VS.memTaint Secret /\ // TODO: generalize this
      M.valid_taint_buf64 x1 s0.VS.mem s0.VS.memTaint Secret /\ // TODO: generalize this
      V.valid_stack_slots s0.VS.mem (VS.eval_reg Rsp s0) sb num_stack_slots s0.VS.memTaint
      ) ==>
    pre IA.win x0 x1 s0 sb)

let to_low_post
    (post:vale_post)
    (x0 x1:M.buffer64)
    (hs_mem0:HS.mem)
    (_:unit)
    (hs_mem1:HS.mem)
  : prop =
  // REVIEW: it would be more flexible to let low_assumptions/post take care of modifies:
  LB.modifies (LB.loc_union (LB.loc_buffer (to_b8 x0)) (LB.loc_buffer (to_b8 x1))) hs_mem0 hs_mem1 /\
  (exists
    (s0:V.va_state)
    (sb:stack_buffer)
    (s1:V.va_state)
    (f:V.va_fuel).
    low_assumptions hs_mem0 s0.VS.mem x0 x1 /\
    low_assumptions hs_mem1 s1.VS.mem x0 x1 /\
    post IA.win x0 x1 s0 sb s1 f)

let as_lowstar_sig
    (pre:vale_pre)
    (post:vale_post)
  : Type0 =
  // REVIEW: wouldn't b8 make more sense here?
  x0:M.buffer64 ->
  x1:M.buffer64 ->
  HST.Stack unit
    (requires fun h0 ->
      LB.loc_disjoint (LB.loc_buffer (to_b8 x0)) (LB.loc_buffer (to_b8 x1)) /\ // REVIEW: should be more flexible about buffer aliasing
      to_low_pre pre x0 x1 h0)
    (ensures to_low_post post x0 x1)

val wrap
    (code:V.va_code)
    (pre:vale_pre)
    (post:vale_post)
    (v:vale_sig code pre post)
  : as_lowstar_sig pre post

