module X64.Bytes_Semantics_s

open Prop_s
open Opaque_s
open X64.Machine_s
open X64.CPU_Features_s
open Words_s
open Words.Two_s
open Words.Four_s
open Types_s
open X64.Instruction_s
open FStar.Seq.Base
module F = FStar.FunctionalExtensionality

type uint64:eqtype = UInt64.t

type heap = Map.t int nat8
let op_String_Access = Map.sel
let op_String_Assignment = Map.upd

noeq
type stack =
  | Vale_stack: 
    initial_rsp:nat64{initial_rsp >= 4096} ->  // Initial rsp pointer when entering the function
    mem:Map.t int nat8 ->                       // Stack contents
    stack
  
noeq type ins:eqtype =
  // Generic instruction (should be able to express most instructions)
  | Instr :
      outs:list instr_out ->
      args:list instr_operand ->
      havoc_flags:flag_havoc ->
      i:instr_t outs args havoc_flags ->
      oprs:instr_operands_t outs args ->
      ins

  // Temporary partially-generic instructions
  // TODO: replace these with Instr when Leakage_Ins supports Instr:
  | Ins_64_64_preserve : i:instr_t [out op64] [op64] PreserveFlags -> dst:operand -> src:operand -> ins
  | Ins_io64_64 : i:instr_t [inOut op64] [op64] HavocFlags -> dst:operand -> src:operand -> ins
  | Ins_io64_64_cf : i:instr_t [inOut opFlagsCf; inOut op64] [op64] HavocFlags -> dst:operand -> src:operand -> ins
  | Ins_ioXmm : i:instr_t [inOut opXmm] [] PreserveFlags -> dst:xmm -> ins
  | Ins_Xmm_Xmm : i:instr_t [out opXmm] [opXmm] PreserveFlags -> dst:xmm -> src:xmm -> ins
  | Ins_ioXmm_Xmm : i:instr_t [inOut opXmm] [opXmm] PreserveFlags -> dst:xmm -> src:xmm -> ins

  // TODO: convert these to Instr:
  | Xor64      : dst:operand -> src:operand -> ins
  | Pxor       : dst:xmm -> src:xmm -> ins
  | VPxor      : dst:xmm -> src1:xmm -> src2:mov128_op -> ins
  | MOVDQU     : dst:mov128_op -> src:mov128_op -> ins  // We let the assembler complain about attempts to use two memory ops

  // Stack operations
  | Push       : src:operand -> ins
  | Pop        : dst:operand -> ins
  | Alloc      : n:nat -> ins
  | Dealloc    : n:nat -> ins

type ocmp:eqtype =
  | OEq: o1:operand{not (OMem? o1 || OStack? o1)} -> o2:operand{not (OMem? o2 || OStack? o2)} -> ocmp
  | ONe: o1:operand{not (OMem? o1 || OStack? o1)} -> o2:operand{not (OMem? o2 || OStack? o2)} -> ocmp
  | OLe: o1:operand{not (OMem? o1 || OStack? o1)} -> o2:operand{not (OMem? o2 || OStack? o2)} -> ocmp
  | OGe: o1:operand{not (OMem? o1 || OStack? o1)} -> o2:operand{not (OMem? o2 || OStack? o2)} -> ocmp
  | OLt: o1:operand{not (OMem? o1 || OStack? o1)} -> o2:operand{not (OMem? o2 || OStack? o2)} -> ocmp
  | OGt: o1:operand{not (OMem? o1 || OStack? o1)} -> o2:operand{not (OMem? o2 || OStack? o2)} -> ocmp

type code:eqtype = precode ins ocmp
type codes:eqtype = list code
type regs_t = F.restricted_t reg (fun _ -> nat64)
type xmms_t = F.restricted_t xmm (fun _ -> quad32)

noeq type state = {
  ok: bool;
  regs: regs_t;
  xmms: xmms_t;
  flags: nat64;
  mem: heap;
  stack:stack;
}

assume val havoc : state -> ins -> nat64

unfold let eval_reg (r:reg) (s:state) : nat64 = s.regs r
unfold let eval_xmm (i:xmm) (s:state) : quad32 = s.xmms i

let get_heap_val64_def (ptr:int) (mem:heap) : nat64 =
  two_to_nat 32
  (Mktwo
    (four_to_nat 8 (Mkfour mem.[ptr] mem.[ptr+1] mem.[ptr+2] mem.[ptr+3]))
    (four_to_nat 8 (Mkfour mem.[ptr+4] mem.[ptr+5] mem.[ptr+6] mem.[ptr+7]))
  )
let get_heap_val64 = make_opaque get_heap_val64_def

let get_heap_val32_def (ptr:int) (mem:heap) : nat32 =
  four_to_nat 8 
  (Mkfour
    mem.[ptr]
    mem.[ptr+1]
    mem.[ptr+2]
    mem.[ptr+3])

let get_heap_val32 = make_opaque get_heap_val32_def

let get_heap_val128_def (ptr:int) (mem:heap) : quad32 = Mkfour
  (get_heap_val32 ptr mem)
  (get_heap_val32 (ptr+4) mem)
  (get_heap_val32 (ptr+8) mem)
  (get_heap_val32 (ptr+12) mem)
let get_heap_val128 = make_opaque get_heap_val128_def

unfold let eval_mem (ptr:int) (s:state) : nat64 = get_heap_val64 ptr s.mem
unfold let eval_mem128 (ptr:int) (s:state) : quad32 = get_heap_val128 ptr s.mem

unfold let eval_stack (ptr:int) (s:stack) : nat64 = 
  let Vale_stack _ mem = s in
  get_heap_val64 ptr mem
unfold let eval_stack128 (ptr:int) (s:stack) : quad32 = 
  let Vale_stack _ mem = s in
  get_heap_val128 ptr mem

[@va_qattr]
let eval_maddr (m:maddr) (s:state) : int =
  let open FStar.Mul in
    match m with
    | MConst n -> n
    | MReg reg offset -> (eval_reg reg s) + offset
    | MIndex base scale index offset -> (eval_reg base s) + scale * (eval_reg index s) + offset

let eval_operand (o:operand) (s:state) : nat64 =
  match o with
  | OConst n -> int_to_nat64 n
  | OReg r -> eval_reg r s
  | OMem m -> eval_mem (eval_maddr m s) s
  | OStack m -> eval_stack (eval_maddr m s) s.stack

let eval_mov128_op (o:mov128_op) (s:state) : quad32 =
  match o with
  | Mov128Xmm i -> eval_xmm i s
  | Mov128Mem m -> eval_mem128 (eval_maddr m s) s
  | Mov128Stack m -> eval_stack128 (eval_maddr m s) s.stack

let eval_ocmp (s:state) (c:ocmp) :bool =
  match c with
  | OEq o1 o2 -> eval_operand o1 s = eval_operand o2 s
  | ONe o1 o2 -> eval_operand o1 s <> eval_operand o2 s
  | OLe o1 o2 -> eval_operand o1 s <= eval_operand o2 s
  | OGe o1 o2 -> eval_operand o1 s >= eval_operand o2 s
  | OLt o1 o2 -> eval_operand o1 s < eval_operand o2 s
  | OGt o1 o2 -> eval_operand o1 s > eval_operand o2 s

let update_reg' (r:reg) (v:nat64) (s:state) : state =
  { s with regs = F.on_dom reg (fun r' -> if r' = r then v else s.regs r') }

let update_xmm' (x:xmm) (v:quad32) (s:state) : state =
  { s with xmms = F.on_dom xmm (fun x' -> if x' = x then v else s.xmms x') }

val mod_8: (n:nat{n < pow2_64}) -> nat8
let mod_8 n = n % 0x100

let update_heap32_def (ptr:int) (v:nat32) (mem:heap) : heap =
  let v = nat_to_four 8 v in
  let mem = mem.[ptr] <- v.lo0 in
  let mem = mem.[ptr+1] <- v.lo1 in
  let mem = mem.[ptr+2] <- v.hi2 in
  let mem = mem.[ptr+3] <- v.hi3 in
  mem
let update_heap32 = make_opaque update_heap32_def

let update_heap64_def (ptr:int) (v:nat64) (mem:heap) : heap =
  let v = nat_to_two 32 v in
  let lo = nat_to_four 8 v.lo in
  let hi = nat_to_four 8 v.hi in
  let mem = mem.[ptr] <- lo.lo0 in
  let mem = mem.[ptr+1] <- lo.lo1 in
  let mem = mem.[ptr+2] <- lo.hi2 in
  let mem = mem.[ptr+3] <- lo.hi3 in
  let mem = mem.[ptr+4] <- hi.lo0 in
  let mem = mem.[ptr+5] <- hi.lo1 in
  let mem = mem.[ptr+6] <- hi.hi2 in
  let mem = mem.[ptr+7] <- hi.hi3 in
  mem
let update_heap64 = make_opaque update_heap64_def

let update_heap128 (ptr:int) (v:quad32) (mem:heap) =
  let mem = update_heap32 ptr v.lo0 mem in
  let mem = update_heap32 (ptr+4) v.lo1 mem in
  let mem = update_heap32 (ptr+8) v.hi2 mem in
  let mem = update_heap32 (ptr+12) v.hi3 mem in
  mem

let valid_addr (ptr:int) (mem:heap) : bool =
  Map.contains mem ptr

let valid_addr64 (ptr:int) (mem:heap) =
  valid_addr ptr mem &&
  valid_addr (ptr+1) mem &&
  valid_addr (ptr+2) mem &&
  valid_addr (ptr+3) mem &&
  valid_addr (ptr+4) mem &&
  valid_addr (ptr+5) mem &&
  valid_addr (ptr+6) mem &&
  valid_addr (ptr+7) mem

let valid_addr128 (ptr:int) (mem:heap) =
  valid_addr ptr mem &&
  valid_addr (ptr+1) mem &&
  valid_addr (ptr+2) mem &&
  valid_addr (ptr+3) mem &&
  valid_addr (ptr+4) mem &&
  valid_addr (ptr+5) mem &&
  valid_addr (ptr+6) mem &&
  valid_addr (ptr+7) mem &&
  valid_addr (ptr+8) mem &&
  valid_addr (ptr+9) mem &&
  valid_addr (ptr+10) mem &&
  valid_addr (ptr+11) mem &&
  valid_addr (ptr+12) mem &&
  valid_addr (ptr+13) mem &&
  valid_addr (ptr+14) mem &&
  valid_addr (ptr+15) mem

let update_mem (ptr:int) (v:nat64) (s:state) : state =
  if valid_addr64 ptr s.mem then
  { s with mem = update_heap64 ptr v s.mem }
  else s
  
let update_mem128 (ptr:int) (v:quad32) (s:state) : state =
  if valid_addr128 ptr s.mem then
  { s with mem = update_heap128 ptr v s.mem }
  else s

unfold
let update_stack' (ptr:int) (v:nat64) (s:stack) : stack =
  let Vale_stack init_rsp mem = s in
  let mem = update_heap64 ptr v mem in
  Vale_stack init_rsp mem

unfold
let update_stack128' (ptr:int) (v:quad32) (s:stack) : stack =
  let Vale_stack init_rsp mem = s in
  let mem = update_heap128 ptr v mem in
  Vale_stack init_rsp mem

let update_stack (ptr:int) (v:nat64) (s:state) : state =
  let Vale_stack init_rsp mem = s.stack in
  // We can only write the stack between the current stack pointer and
  // the initial stack pointer. Everything above is read-only
  if (ptr >= s.regs Rsp && ptr + 8 <= init_rsp) then (
    {s with stack = update_stack' ptr v s.stack}
  ) else 
    // If we are in this case, a previous check set the ok field to false
    s

let update_stack128 (ptr:int) (v:quad32) (s:state) : state =
  let Vale_stack init_rsp mem = s.stack in
  // We can only write the stack between the current stack pointer and
  // the initial stack pointer. Everything above is read-only
  if (ptr >= s.regs Rsp && ptr + 16 <= init_rsp) then (
    {s with stack = update_stack128' ptr v s.stack}
  ) else 
    // If we are in this case, a previous check set the ok field to false  
    s

unfold
let valid_src_stack64 (ptr:int) (st:stack) : bool =
  let Vale_stack init_rsp mem = st in
  valid_addr64 ptr mem

unfold
let valid_src_stack128 (ptr:int) (st:stack) : bool =
  let Vale_stack init_rsp mem = st in
  valid_addr128 ptr mem

let valid_src_operand (o:operand) (s:state) : bool =
  match o with
  | OConst n -> true
  | OReg r -> true
  | OMem m -> valid_addr64 (eval_maddr m s) s.mem
  | OStack m -> valid_src_stack64 (eval_maddr m s) s.stack

let valid_src_mov128_op (o:mov128_op) (s:state) : bool =
  match o with
  | Mov128Xmm i -> true (* We leave it to the printer/assembler to object to invalid XMM indices *)
  | Mov128Mem m -> valid_addr128 (eval_maddr m s) s.mem
  | Mov128Stack m -> valid_src_stack128 (eval_maddr m s) s.stack
  
let valid_src_shift_operand (o:operand) (s:state) : bool =
  valid_src_operand o s && (eval_operand o s) < 64

let valid_ocmp (c:ocmp) (s:state) :bool =
  match c with
  | OEq o1 o2 -> valid_src_operand o1 s && valid_src_operand o2 s
  | ONe o1 o2 -> valid_src_operand o1 s && valid_src_operand o2 s
  | OLe o1 o2 -> valid_src_operand o1 s && valid_src_operand o2 s
  | OGe o1 o2 -> valid_src_operand o1 s && valid_src_operand o2 s
  | OLt o1 o2 -> valid_src_operand o1 s && valid_src_operand o2 s
  | OGt o1 o2 -> valid_src_operand o1 s && valid_src_operand o2 s

unfold
let valid_dst_stack64 (rsp:nat64) (ptr:int) (st:stack) : bool =
  let Vale_stack init_rsp mem = st in
    // We are allowed to store anywhere between Rsp and the initial stack pointer
  ptr >= rsp && ptr + 8 <= init_rsp

unfold
let valid_dst_stack128 (rsp:nat64) (ptr:int) (st:stack) : bool =
  let Vale_stack init_rsp mem = st in
    // We are allowed to store anywhere between Rsp and the initial stack pointer
    ptr >= rsp && ptr + 16 <= init_rsp

let valid_dst_operand (o:operand) (s:state) : bool =
  match o with
  | OConst n -> false
  | OReg r -> not (Rsp? r)
  | OMem m -> valid_addr64 (eval_maddr m s) s.mem
  | OStack m -> valid_dst_stack64 (eval_reg Rsp s) (eval_maddr m s) s.stack

let valid_dst_mov128_op (o:mov128_op) (s:state) : bool =
  match o with
  | Mov128Xmm i -> true (* We leave it to the printer/assembler to object to invalid XMM indices *)
  | Mov128Mem m -> valid_addr128 (eval_maddr m s) s.mem
  | Mov128Stack m -> valid_dst_stack128 (eval_reg Rsp s) (eval_maddr m s) s.stack

let update_operand_preserve_flags'' (o:operand) (v:nat64) (s_orig s:state) : state =
  match o with
  | OConst _ -> {s with ok = false}
  | OReg r -> update_reg' r v s
  | OMem m -> update_mem (eval_maddr m s_orig) v s // see valid_maddr for how eval_maddr connects to b and i
  | OStack m -> update_stack (eval_maddr m s_orig) v s 

let update_operand_preserve_flags' (o:operand) (v:nat64) (s:state) : state =
  update_operand_preserve_flags'' o v s s

let update_mov128_op_preserve_flags'' (o:mov128_op) (v:quad32) (s_orig s:state) : state =
  match o with
  | Mov128Xmm i -> update_xmm' i v s
  | Mov128Mem m -> update_mem128 (eval_maddr m s_orig) v s
  | Mov128Stack m -> update_stack128 (eval_maddr m s_orig) v s

let update_mov128_op_preserve_flags' (o:mov128_op) (v:quad32) (s:state) : state =
  update_mov128_op_preserve_flags'' o v s s

// Default version havocs flags
let update_operand' (o:operand) (ins:ins) (v:nat64) (s:state) : state =
  { (update_operand_preserve_flags' o v s) with flags = havoc s ins }

let update_rsp' (new_rsp:int) (s:state) : state =
  let Vale_stack init_rsp mem = s.stack in
  // Only modify the stack pointer if the new value is valid, that is in the current stack frame, and in the same page
  if new_rsp >= init_rsp - 4096 && new_rsp <= init_rsp then
    update_reg' Rsp new_rsp s
  else
    s

(* REVIEW: Will we regret exposing a mod here?  Should flags be something with more structure? *)
let cf (flags:nat64) : bool =
  flags % 2 = 1

//unfold let bit11 = normalize_term (pow2 11)
let _ = assert (2048 == normalize_term (pow2 11))

let overflow(flags:nat64) : bool =
  (flags / 2048) % 2 = 1  // OF is the 12th bit, so dividing by 2^11 shifts right 11 bits

let update_cf' (flags:nat64) (new_cf:bool) : (new_flags:nat64{cf new_flags == new_cf}) =
  if new_cf then
    if not (cf flags) then
      flags + 1
    else
      flags
  else
    if (cf flags) then
      flags - 1
    else
      flags

let update_of' (flags:nat64) (new_of:bool) : (new_flags:nat64{overflow new_flags == new_of}) =
  if new_of then
    if not (overflow flags) then
      flags + 2048
    else
      flags
  else
    if (overflow flags) then
      flags - 2048
    else
      flags

let free_stack' (start finish:int) (st:stack) : stack =
  let Vale_stack init_rsp mem = st in
  let domain = Map.domain mem in
  // Returns the domain, without elements between start and finish
  let restricted_domain = Vale.Set.remove_between domain start finish in
  // The new domain of the stack does not contain elements between start and finish
  let new_mem = Map.restrict restricted_domain mem in
  Vale_stack init_rsp new_mem

(* Define a stateful monad to simplify defining the instruction semantics *)
let st (a:Type) = state -> a * state

unfold
let return (#a:Type) (x:a) :st a =
  fun s -> x, s

unfold
let bind (#a:Type) (#b:Type) (m:st a) (f:a -> st b) :st b =
fun s0 ->
  let x, s1 = m s0 in
  let y, s2 = f x s1 in
  y, {s2 with ok=s0.ok && s1.ok && s2.ok}

unfold
let get :st state =
  fun s -> s, s

unfold
let set (s:state) :st unit =
  fun _ -> (), s

unfold
let fail :st unit =
  fun s -> (), {s with ok=false}

unfold
let check_imm (valid:bool) : st unit =
  if valid then
    return ()
  else
    fail

unfold
let check (valid: state -> bool) : st unit =
  s <-- get;
  if valid s then
    return ()
  else
    fail

unfold
let try_option (#a:Type) (o:option a) (f:a -> st unit) : st unit =
  match o with
  | None -> fail
  | Some x -> f x

let apply_option (#a:Type) (o:option a) (f:a -> st unit) : st unit =
  try_option o f

unfold
let run (f:st unit) (s:state) : state = snd (f s)

(* Monadic update operations *)
unfold
let update_operand_preserve_flags (dst:operand) (v:nat64) :st unit =
  check (valid_dst_operand dst);;
  s <-- get;
  set (update_operand_preserve_flags' dst v s)

unfold
let update_mov128_op_preserve_flags (dst:mov128_op) (v:quad32) :st unit =
  check (valid_dst_mov128_op dst);;
  s <-- get;
  set (update_mov128_op_preserve_flags' dst v s)

// Default version havocs flags
unfold
let update_operand (dst:operand) (ins:ins) (v:nat64) :st unit =
  check (valid_dst_operand dst);;
  s <-- get;
  set (update_operand' dst ins v s)

unfold
let update_rsp (i:int) : st unit =
  // Only modify the stack pointer if the new value is valid, that is in the current stack frame, and in the same page
 check (fun s -> i >= s.stack.initial_rsp - 4096);;
 check (fun s -> i <= s.stack.initial_rsp);;
 s <-- get;
 set (update_rsp' i s)

let update_reg (r:reg) (v:nat64) :st unit =
  s <-- get;
  set (update_reg' r v s)

let update_xmm (x:xmm)  (ins:ins) (v:quad32) :st unit =
  s <-- get;
  set (  { (update_xmm' x v s) with flags = havoc s ins } )

let update_xmm_preserve_flags (x:xmm) (v:quad32) :st unit =
  s <-- get;
  set ( update_xmm' x v s )

let update_flags (new_flags:nat64) :st unit =
  s <-- get;
  set ( { s with flags = new_flags } )

let update_cf (new_cf:bool) :st unit =
  s <-- get;
  set ( { s with flags = update_cf' s.flags new_cf } )

let update_of (new_of:bool) :st unit =
  s <-- get;
  set ( { s with flags = update_of' s.flags new_of } )

let update_cf_of (new_cf new_of:bool) :st unit =
  s <-- get;
  set ( { s with flags = update_cf' (update_of' s.flags new_of) new_cf } )

let free_stack (start finish:int) : st unit =
  s <-- get;
  set ( { s with stack = free_stack' start finish s.stack} )

let bind_option (#a #b:Type) (v:option a) (f:a -> option b) : option b =
  match v with
  | None -> None
  | Some x -> f x

[@instr_attr]
let instr_eval_operand_explicit (i:instr_operand_explicit) (o:instr_operand_t i) (s:state) : option (instr_val_t (IOpEx i)) =
  match i with
  | IOp64 -> if valid_src_operand o s then Some (eval_operand o s) else None
  | IOpXmm -> if valid_src_mov128_op o s then Some (eval_mov128_op o s) else None

[@instr_attr]
let instr_eval_operand_implicit (i:instr_operand_implicit) (s:state) : option (instr_val_t (IOpIm i)) =
  match i with
  | IOp64One o -> if valid_src_operand o s then Some (eval_operand o s) else None
  | IOpXmmOne o -> if valid_src_mov128_op o s then Some (eval_mov128_op o s) else None
  | IOpFlagsCf -> Some (cf s.flags)
  | IOpFlagsOf -> Some (overflow s.flags)

[@instr_attr]
let rec instr_apply_eval_args
    (outs:list instr_out) (args:list instr_operand)
    (f:instr_args_t outs args) (oprs:instr_operands_t_args args) (s:state)
  : option (instr_ret_t outs) =
  match args with
  | [] -> f
  | i::args ->
    let (v, oprs) =
      match i with
      | IOpEx i -> let oprs = coerce oprs in (instr_eval_operand_explicit i (fst oprs) s, snd oprs)
      | IOpIm i -> (instr_eval_operand_implicit i s, coerce oprs)
      in
    let f:arrow (instr_val_t i) (instr_args_t outs args) = coerce f in
    bind_option v (fun v -> instr_apply_eval_args outs args (f v) oprs s)

[@instr_attr]
let rec instr_apply_eval_inouts
    (outs inouts:list instr_out) (args:list instr_operand)
    (f:instr_inouts_t outs inouts args) (oprs:instr_operands_t inouts args) (s:state)
  : option (instr_ret_t outs) =
  match inouts with
  | [] -> instr_apply_eval_args outs args f oprs s
  | (Out, i)::inouts ->
    let oprs =
      match i with
      | IOpEx i -> snd #(instr_operand_t i) (coerce oprs)
      | IOpIm i -> coerce oprs
      in
    instr_apply_eval_inouts outs inouts args (coerce f) oprs s
  | (InOut, i)::inouts ->
    let (v, oprs) =
      match i with
      | IOpEx i -> let oprs = coerce oprs in (instr_eval_operand_explicit i (fst oprs) s, snd oprs)
      | IOpIm i -> (instr_eval_operand_implicit i s, coerce oprs)
      in
    let f:arrow (instr_val_t i) (instr_inouts_t outs inouts args) = coerce f in
    bind_option v (fun v -> instr_apply_eval_inouts outs inouts args (f v) oprs s)

(*
Take the all the input operands for an instruction and:
- check that they are valid
- evaluate them
- apply the instruction's evaluator function f to the evaluated operands
*)
[@instr_attr]
let instr_apply_eval
    (outs:list instr_out) (args:list instr_operand)
    (f:instr_eval_t outs args) (oprs:instr_operands_t outs args) (s:state)
  : option (instr_ret_t outs) =
  instr_apply_eval_inouts outs outs args f oprs s

let state_or_fail (s:state) (b:bool) (s':state) : state =
  if b then s' else {s with ok = false}

[@instr_attr]
let rec instr_write_output_explicit
    (i:instr_operand_explicit) (v:instr_val_t (IOpEx i)) (o:instr_operand_t i) (s_orig s:state)
  : state =
  match i with
  | IOp64 -> state_or_fail s (valid_dst_operand o s_orig) (update_operand_preserve_flags'' o v s_orig s)
  | IOpXmm -> state_or_fail s (valid_dst_mov128_op o s_orig) (update_mov128_op_preserve_flags'' o v s_orig s)

[@instr_attr]
let rec instr_write_output_implicit
    (i:instr_operand_implicit) (v:instr_val_t (IOpIm i)) (s_orig s:state)
  : state =
  match i with
  | IOp64One o -> state_or_fail s (valid_dst_operand o s_orig) (update_operand_preserve_flags'' o v s_orig s)
  | IOpXmmOne o -> state_or_fail s (valid_dst_mov128_op o s_orig) (update_mov128_op_preserve_flags'' o v s_orig s)
  | IOpFlagsCf -> {s with flags = update_cf' s.flags v}
  | IOpFlagsOf -> {s with flags = update_of' s.flags v}

(*
For each output operand:
- compute the location of the operand in s_orig
- check that the operand is valid and update the current state (in order that the operands appear in "outs")
*)
[@instr_attr]
let rec instr_write_outputs
    (outs:list instr_out) (args:list instr_operand)
    (vs:instr_ret_t outs) (oprs:instr_operands_t outs args) (s_orig s:state)
  : state =
  match outs with
  | [] -> s
  | (_, i):: outs ->
    (
      let ((v:instr_val_t i), (vs:instr_ret_t outs)) =
        match outs with
        | [] -> (vs, ())
        | _::_ -> let vs = coerce vs in (fst vs, snd vs)
        in
      match i with
      | IOpEx i ->
        let oprs = coerce oprs in
        let s = instr_write_output_explicit i v (fst oprs) s_orig s in
        instr_write_outputs outs args vs (snd oprs) s_orig s
      | IOpIm i ->
        let s = instr_write_output_implicit i v s_orig s in
        instr_write_outputs outs args vs (coerce oprs) s_orig s
    )

[@instr_attr]
let eval_instr
    (outs:list instr_out) (args:list instr_operand) (havoc_flags:flag_havoc)
    (i:instr_t outs args havoc_flags) (oprs:instr_operands_t outs args) (s0:state)
  : option state =
  let vs = instr_apply_eval outs args (instr_eval i) oprs s0 in
  let s1 =
    match havoc_flags with
    | HavocFlags -> {s0 with flags = havoc s0 (Instr outs args havoc_flags i oprs)}
    | PreserveFlags -> s0
    in
  FStar.Option.mapTot (fun vs -> instr_write_outputs outs args vs oprs s0 s1) vs

(* Core definition of instruction semantics *)
[@instr_attr]
let eval_ins (ins:ins) : st unit =
  s <-- get;
  match ins with
  | Instr outs args havoc_flags i oprs ->
    apply_option (eval_instr outs args havoc_flags i oprs s) set

  | Ins_64_64_preserve i dst src ->
    check (valid_src_operand src);;
    let vOpt = instr_eval i (eval_operand src s) in
    try_option vOpt (update_operand_preserve_flags dst)

  | Ins_io64_64 i dst src ->
    check (valid_src_operand src);;
    let vOpt = instr_eval i (eval_operand dst s) (eval_operand src s) in
    try_option vOpt (update_operand dst ins)

  | Ins_io64_64_cf i dst src ->
    check (valid_src_operand src);;
    let vOpt = instr_eval i (cf s.flags) (eval_operand dst s) (eval_operand src s) in
    try_option vOpt (fun (new_carry, v) ->
      update_operand dst ins v;;
      update_flags (havoc s ins);; // We specify cf, but underspecify everything else
      update_cf new_carry)

  | Ins_ioXmm i dst ->
    let vOpt = instr_eval i (eval_xmm dst s) in
    try_option vOpt (update_xmm_preserve_flags dst)

  | Ins_Xmm_Xmm i dst src ->
    let vOpt = instr_eval i (eval_xmm src s) in
    try_option vOpt (update_xmm_preserve_flags dst)

  | Ins_ioXmm_Xmm i dst src ->
    let vOpt = instr_eval i (eval_xmm dst s) (eval_xmm src s) in
    try_option vOpt (update_xmm_preserve_flags dst)

  | Xor64 dst src ->
    check (valid_src_operand src);;
    update_operand dst ins (Types_s.ixor (eval_operand dst s) (eval_operand src s));;
    update_cf_of false false

  | Push src ->
    check (valid_src_operand src);;
    // Evaluate value on initial state
    let new_src = eval_operand src s in
    // Compute the new stack pointer
    let new_rsp = eval_reg Rsp s - 8 in
    // Actually modify the stack pointer
    update_rsp new_rsp;;
    // Store the element at the new stack pointer
    update_operand_preserve_flags (OStack (MConst new_rsp)) new_src

  | Pop dst ->
    let stack_op = OStack (MReg Rsp 0) in
    // Ensure that we can read at the initial stack pointer
    check (valid_src_operand stack_op);;
    // Get the element currently on top of the stack
    let new_dst = eval_operand stack_op s in
    // Compute the new stack pointer
    let new_rsp = (eval_reg Rsp s + 8) % pow2_64 in
    // Store it in the dst operand
    update_operand_preserve_flags dst new_dst;;
    // Free the memory that is popped
    free_stack (new_rsp - 8) new_rsp;;
    // Finally, update the stack pointer
    update_rsp new_rsp

  | Alloc n ->
    // We already check in update_rsp that the new stack pointer is valid
    update_rsp (eval_reg Rsp s - n)
  
  | Dealloc n ->
    let old_rsp = eval_reg Rsp s in
    let new_rsp = old_rsp + n in
    update_rsp new_rsp;;
    // The deallocated stack memory should now be considered invalid
    free_stack old_rsp new_rsp

// In the XMM-related instructions below, we generally don't need to check for validity of the operands,
// since all possibilities are valid, thanks to dependent types

  | Pxor dst src ->
    update_xmm_preserve_flags dst (quad32_xor (eval_xmm dst s) (eval_xmm src s))

  |VPxor dst src1 src2 ->
    check (valid_src_mov128_op src2);;
    update_xmm_preserve_flags dst (quad32_xor (eval_xmm src1 s) (eval_mov128_op src2 s))

  | MOVDQU dst src ->
    check (valid_src_mov128_op src);;
    update_mov128_op_preserve_flags dst (eval_mov128_op src s)

(*
 * These functions return an option state
 * None case arises when the while loop runs out of fuel
 *)
// TODO: IfElse and While should havoc the flags
val eval_code:  c:code           -> fuel:nat -> s:state -> Tot (option state) (decreases %[fuel; c])
val eval_codes: l:codes          -> fuel:nat -> s:state -> Tot (option state) (decreases %[fuel; l])
val eval_while: b:ocmp -> c:code -> fuel:nat -> s:state -> Tot (option state) (decreases %[fuel; c])

let rec eval_code c fuel s =
  match c with
  | Ins ins                       -> Some (run (eval_ins ins) s)
  | Block l                       -> eval_codes l fuel s
  | IfElse ifCond ifTrue ifFalse  -> let s = run (check (valid_ocmp ifCond)) s in
           if eval_ocmp s ifCond then eval_code ifTrue fuel s else eval_code ifFalse fuel s
  | While b c                     -> eval_while b c fuel s

and eval_codes l fuel s =
  match l with
  | []   -> Some s
  | c::tl ->
    let s_opt = eval_code c fuel s in
    if None? s_opt then None else eval_codes tl fuel (Some?.v s_opt)

and eval_while b c fuel s0 =
  if fuel = 0 then None else
  let s0 = run (check (valid_ocmp b)) s0 in
  if not (eval_ocmp s0 b) then Some s0
  else
    match eval_code c (fuel - 1) s0 with
    | None -> None
    | Some s1 ->
      if s1.ok then eval_while b c (fuel - 1) s1  // success: continue to next iteration
      else Some s1  // failure: propagate failure immediately
