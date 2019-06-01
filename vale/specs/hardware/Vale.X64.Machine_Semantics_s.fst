module Vale.X64.Machine_Semantics_s

open Vale.Def.Prop_s
open Vale.Def.Opaque_s
open Vale.X64.Machine_s
open Vale.X64.CPU_Features_s
open Vale.Def.Words_s
open Vale.Def.Words.Two_s
open Vale.Def.Words.Four_s
open Vale.Def.Types_s
open Vale.X64.Instruction_s
open Vale.X64.Instructions_s
open FStar.Seq.Base
module F = FStar.FunctionalExtensionality
module BC = Vale.X64.Bytes_Code_s

type uint64:eqtype = UInt64.t

type heap = Map.t int nat8
let op_String_Access = Map.sel
let op_String_Assignment = Map.upd

//TODO: [@"opaque_to_smt"]
let equals_instr (x1 x2:instr_t_record) : Type0 =
  squash (x1 == x2)

noeq type instr_annotation (it:instr_t_record) =
  | AnnotateNone : instr_annotation it
  | AnnotateXor64 : equals_instr it (InstrTypeRecord ins_Xor64) -> instr_annotation it
  | AnnotatePxor : equals_instr it (InstrTypeRecord ins_Pxor) -> instr_annotation it
  | AnnotateVPxor : equals_instr it (InstrTypeRecord ins_VPxor) -> instr_annotation it

let ins = BC.instruction_t instr_annotation
let ocmp = BC.ocmp
let code = BC.code_t instr_annotation
let codes = BC.codes_t instr_annotation

noeq
type stack =
  | Vale_stack:
    initial_rsp:nat64{initial_rsp >= 4096} ->  // Initial rsp pointer when entering the function
    stack_mem:Map.t int nat8 ->                // Stack contents
    stack

type regs_t = F.restricted_t reg (fun _ -> nat64)
type xmms_t = F.restricted_t xmm (fun _ -> quad32)

noeq
type machine_state = {
  ms_ok: bool;
  ms_regs: regs_t;
  ms_xmms: xmms_t;
  ms_flags: nat64;
  ms_mem: heap;
  ms_memTaint: memTaint_t;
  ms_stack: stack;
  ms_stackTaint: memTaint_t;
  ms_trace: list observation;
}

let get_fst_ocmp (o:ocmp) = match o with
  | BC.OEq o1 _ | BC.ONe o1 _ | BC.OLe o1 _ | BC.OGe o1 _ | BC.OLt o1 _ | BC.OGt o1 _ -> o1

let get_snd_ocmp (o:ocmp) = match o with
  | BC.OEq _ o2 | BC.ONe _ o2 | BC.OLe _ o2 | BC.OGe _ o2 | BC.OLt _ o2 | BC.OGt _ o2 -> o2

assume val havoc_any (#a:Type) (x:a) : nat64
let havoc_state_ins (s:machine_state) (i:ins) : nat64 =
  havoc_any (s.ms_regs, s.ms_xmms, s.ms_flags, s.ms_mem, s.ms_stack, ins)

unfold let eval_reg (r:reg) (s:machine_state) : nat64 = s.ms_regs r
unfold let eval_xmm (i:xmm) (s:machine_state) : quad32 = s.ms_xmms i

let get_heap_val64_def (ptr:int) (mem:heap) : nat64 =
  two_to_nat 32
  (Mktwo
    (four_to_nat 8 (Mkfour mem.[ptr] mem.[ptr + 1] mem.[ptr + 2] mem.[ptr + 3]))
    (four_to_nat 8 (Mkfour mem.[ptr + 4] mem.[ptr + 5] mem.[ptr + 6] mem.[ptr + 7]))
  )
let get_heap_val64 = make_opaque get_heap_val64_def

let get_heap_val32_def (ptr:int) (mem:heap) : nat32 =
  four_to_nat 8
  (Mkfour
    mem.[ptr]
    mem.[ptr + 1]
    mem.[ptr + 2]
    mem.[ptr + 3])

let get_heap_val32 = make_opaque get_heap_val32_def

let get_heap_val128_def (ptr:int) (mem:heap) : quad32 = Mkfour
  (get_heap_val32 ptr mem)
  (get_heap_val32 (ptr + 4) mem)
  (get_heap_val32 (ptr + 8) mem)
  (get_heap_val32 (ptr + 12) mem)
let get_heap_val128 = make_opaque get_heap_val128_def

unfold let eval_mem (ptr:int) (s:machine_state) : nat64 = get_heap_val64 ptr s.ms_mem
unfold let eval_mem128 (ptr:int) (s:machine_state) : quad32 = get_heap_val128 ptr s.ms_mem

unfold let eval_stack (ptr:int) (s:stack) : nat64 =
  let Vale_stack _ mem = s in
  get_heap_val64 ptr mem
unfold let eval_stack128 (ptr:int) (s:stack) : quad32 =
  let Vale_stack _ mem = s in
  get_heap_val128 ptr mem

[@va_qattr]
let eval_maddr (m:maddr) (s:machine_state) : int =
  let open FStar.Mul in
    match m with
    | MConst n -> n
    | MReg reg offset -> (eval_reg reg s) + offset
    | MIndex base scale index offset -> (eval_reg base s) + scale * (eval_reg index s) + offset

let eval_operand (o:operand64) (s:machine_state) : nat64 =
  match o with
  | OConst n -> int_to_nat64 n
  | OReg r -> eval_reg r s
  | OMem (m, _) -> eval_mem (eval_maddr m s) s
  | OStack (m, _) -> eval_stack (eval_maddr m s) s.ms_stack

let eval_mov128_op (o:operand128) (s:machine_state) : quad32 =
  match o with
  | OConst c -> c
  | OReg i -> eval_xmm i s
  | OMem (m, _) -> eval_mem128 (eval_maddr m s) s
  | OStack (m, _) -> eval_stack128 (eval_maddr m s) s.ms_stack

let eval_ocmp (s:machine_state) (c:ocmp) :bool =
  match c with
  | BC.OEq o1 o2 -> eval_operand o1 s = eval_operand o2 s
  | BC.ONe o1 o2 -> eval_operand o1 s <> eval_operand o2 s
  | BC.OLe o1 o2 -> eval_operand o1 s <= eval_operand o2 s
  | BC.OGe o1 o2 -> eval_operand o1 s >= eval_operand o2 s
  | BC.OLt o1 o2 -> eval_operand o1 s < eval_operand o2 s
  | BC.OGt o1 o2 -> eval_operand o1 s > eval_operand o2 s

let update_reg' (r:reg) (v:nat64) (s:machine_state) : machine_state =
  { s with ms_regs = F.on_dom reg (fun r' -> if r' = r then v else s.ms_regs r') }

let update_xmm' (x:xmm) (v:quad32) (s:machine_state) : machine_state =
  { s with ms_xmms = F.on_dom xmm (fun x' -> if x' = x then v else s.ms_xmms x') }

val mod_8: (n:nat{n < pow2_64}) -> nat8
let mod_8 n = n % 0x100

let update_heap32_def (ptr:int) (v:nat32) (mem:heap) : heap =
  let v = nat_to_four 8 v in
  let mem = mem.[ptr] <- v.lo0 in
  let mem = mem.[ptr + 1] <- v.lo1 in
  let mem = mem.[ptr + 2] <- v.hi2 in
  let mem = mem.[ptr + 3] <- v.hi3 in
  mem
let update_heap32 = make_opaque update_heap32_def

let update_heap64_def (ptr:int) (v:nat64) (mem:heap) : heap =
  let v = nat_to_two 32 v in
  let lo = nat_to_four 8 v.lo in
  let hi = nat_to_four 8 v.hi in
  let mem = mem.[ptr] <- lo.lo0 in
  let mem = mem.[ptr + 1] <- lo.lo1 in
  let mem = mem.[ptr + 2] <- lo.hi2 in
  let mem = mem.[ptr + 3] <- lo.hi3 in
  let mem = mem.[ptr + 4] <- hi.lo0 in
  let mem = mem.[ptr + 5] <- hi.lo1 in
  let mem = mem.[ptr + 6] <- hi.hi2 in
  let mem = mem.[ptr + 7] <- hi.hi3 in
  mem
let update_heap64 = make_opaque update_heap64_def

let update_heap128_def (ptr:int) (v:quad32) (mem:heap) =
  let mem = update_heap32 ptr v.lo0 mem in
  let mem = update_heap32 (ptr + 4) v.lo1 mem in
  let mem = update_heap32 (ptr + 8) v.hi2 mem in
  let mem = update_heap32 (ptr + 12) v.hi3 mem in
  mem
let update_heap128 = make_opaque update_heap128_def

let valid_addr (ptr:int) (mem:heap) : bool =
  Map.contains mem ptr

[@"opaque_to_smt"]
let valid_addr64 (ptr:int) (mem:heap) =
  valid_addr ptr mem &&
  valid_addr (ptr + 1) mem &&
  valid_addr (ptr + 2) mem &&
  valid_addr (ptr + 3) mem &&
  valid_addr (ptr + 4) mem &&
  valid_addr (ptr + 5) mem &&
  valid_addr (ptr + 6) mem &&
  valid_addr (ptr + 7) mem

[@"opaque_to_smt"]
let valid_addr128 (ptr:int) (mem:heap) =
  valid_addr ptr mem &&
  valid_addr (ptr + 1) mem &&
  valid_addr (ptr + 2) mem &&
  valid_addr (ptr + 3) mem &&
  valid_addr (ptr + 4) mem &&
  valid_addr (ptr + 5) mem &&
  valid_addr (ptr + 6) mem &&
  valid_addr (ptr + 7) mem &&
  valid_addr (ptr + 8) mem &&
  valid_addr (ptr + 9) mem &&
  valid_addr (ptr + 10) mem &&
  valid_addr (ptr + 11) mem &&
  valid_addr (ptr + 12) mem &&
  valid_addr (ptr + 13) mem &&
  valid_addr (ptr + 14) mem &&
  valid_addr (ptr + 15) mem

(*
Check if the taint annotation of a memory operand matches the taint in the memory map.
Evaluation will fail in case of a mismatch.
This allows the taint analysis to learn information about the memory map from the annotation,
assuming that the code has been verified not to fail.
(Note that this only relates to memory maps, so non-memory operands need no annotation.)
*)
[@"opaque_to_smt"]
let rec match_n (addr:int) (n:nat) (memTaint:memTaint_t) (t:taint)
  : Tot (b:bool{b <==>
      (forall i.{:pattern (memTaint `Map.sel` i)}
        (i >= addr /\ i < addr + n) ==> memTaint.[i] == t)})
    (decreases n)
  =
  if n = 0 then true
  else if memTaint.[addr] <> t then false
  else match_n (addr + 1) (n - 1) memTaint t

[@"opaque_to_smt"]
let rec update_n (addr:int) (n:nat) (memTaint:memTaint_t) (t:taint)
  : Tot (m:memTaint_t{(
      forall i.{:pattern (m `Map.sel` i)}
        ((i >= addr /\ i < addr + n) ==> m.[i] == t) /\
        ((i < addr \/ i >= addr + n) ==> m.[i] == memTaint.[i]))})
    (decreases n)
  =
  if n = 0 then memTaint
  else update_n (addr + 1) (n - 1) (memTaint.[addr] <- t) t

let update_mem_and_taint (ptr:int) (v:nat64) (s:machine_state) (t:taint) : machine_state =
  if valid_addr64 ptr s.ms_mem then
    { s with
      ms_mem = update_heap64 ptr v s.ms_mem;
      ms_memTaint = update_n ptr 8 s.ms_memTaint t;
    }
  else s

let update_mem128_and_taint (ptr:int) (v:quad32) (s:machine_state) (t:taint) : machine_state =
  if valid_addr128 ptr s.ms_mem then
    { s with
      ms_mem = update_heap128 ptr v s.ms_mem;
      ms_memTaint = update_n ptr 16 s.ms_memTaint t
    }
  else s

unfold
let update_stack64' (ptr:int) (v:nat64) (s:stack) : stack =
  let Vale_stack init_rsp mem = s in
  let mem = update_heap64 ptr v mem in
  Vale_stack init_rsp mem

unfold
let update_stack128' (ptr:int) (v:quad32) (s:stack) : stack =
  let Vale_stack init_rsp mem = s in
  let mem = update_heap128 ptr v mem in
  Vale_stack init_rsp mem

let update_stack_and_taint (ptr:int) (v:nat64) (s:machine_state) (t:taint) : machine_state =
  let Vale_stack init_rsp mem = s.ms_stack in
  { s with
    ms_stack = update_stack64' ptr v s.ms_stack;
    ms_stackTaint = update_n ptr 8 s.ms_stackTaint t;
  }

let update_stack128_and_taint (ptr:int) (v:quad32) (s:machine_state) (t:taint) : machine_state =
  let Vale_stack init_rsp mem = s.ms_stack in
  { s with
    ms_stack = update_stack128' ptr v s.ms_stack;
    ms_stackTaint = update_n ptr 16 s.ms_stackTaint t
  }

unfold
let valid_src_stack64 (ptr:int) (st:stack) : bool =
  let Vale_stack init_rsp mem = st in
  valid_addr64 ptr mem

unfold
let valid_src_stack128 (ptr:int) (st:stack) : bool =
  let Vale_stack init_rsp mem = st in
  valid_addr128 ptr mem

let valid_src_operand (o:operand64) (s:machine_state) : bool =
  match o with
  | OConst n -> true
  | OReg r -> true
  | OMem (m, t) -> valid_addr64 (eval_maddr m s) s.ms_mem
  | OStack (m, t) -> valid_src_stack64 (eval_maddr m s) s.ms_stack

let valid_src_operand64_and_taint (o:operand64) (s:machine_state) : bool =
  match o with
  | OConst n -> true
  | OReg r -> true
  | OMem (m, t) ->
    let ptr = eval_maddr m s in
    valid_addr64 ptr s.ms_mem && match_n ptr 8 s.ms_memTaint t
  | OStack (m, t) ->
    let ptr = eval_maddr m s in
    valid_src_stack64 ptr s.ms_stack && match_n ptr 8 s.ms_stackTaint t

let valid_src_operand128_and_taint (o:operand128) (s:machine_state) : bool =
  match o with
  | OConst _ -> false
  | OReg i -> true // We leave it to the printer/assembler to object to invalid XMM indices
  | OMem (m, t) ->
    let ptr = eval_maddr m s in
    valid_addr128 ptr s.ms_mem && match_n ptr 16 s.ms_memTaint t
  | OStack (m, t) ->
    let ptr = eval_maddr m s in
    valid_src_stack128 ptr s.ms_stack && match_n ptr 16 s.ms_stackTaint t

let valid_ocmp (c:ocmp) (s:machine_state) : bool =
  match c with
  | BC.OEq o1 o2 -> valid_src_operand64_and_taint o1 s && valid_src_operand64_and_taint o2 s
  | BC.ONe o1 o2 -> valid_src_operand64_and_taint o1 s && valid_src_operand64_and_taint o2 s
  | BC.OLe o1 o2 -> valid_src_operand64_and_taint o1 s && valid_src_operand64_and_taint o2 s
  | BC.OGe o1 o2 -> valid_src_operand64_and_taint o1 s && valid_src_operand64_and_taint o2 s
  | BC.OLt o1 o2 -> valid_src_operand64_and_taint o1 s && valid_src_operand64_and_taint o2 s
  | BC.OGt o1 o2 -> valid_src_operand64_and_taint o1 s && valid_src_operand64_and_taint o2 s

unfold
let valid_dst_stack64 (rsp:nat64) (ptr:int) (st:stack) : bool =
  let Vale_stack init_rsp mem = st in
    // We are allowed to store anywhere between rRsp and the initial stack pointer
  ptr >= rsp && ptr + 8 <= init_rsp

unfold
let valid_dst_stack128 (rsp:nat64) (ptr:int) (st:stack) : bool =
  let Vale_stack init_rsp mem = st in
    // We are allowed to store anywhere between rRsp and the initial stack pointer
    ptr >= rsp && ptr + 16 <= init_rsp

let valid_dst_operand64 (o:operand64) (s:machine_state) : bool =
  match o with
  | OConst n -> false
  | OReg r -> not (rRsp = r)
  | OMem (m, _) -> valid_addr64 (eval_maddr m s) s.ms_mem
  | OStack (m, _) -> valid_dst_stack64 (eval_reg rRsp s) (eval_maddr m s) s.ms_stack

let valid_dst_operand128 (o:operand128) (s:machine_state) : bool =
  match o with
  | OConst _ -> false
  | OReg i -> true // We leave it to the printer/assembler to object to invalid XMM indices
  | OMem (m, _) -> valid_addr128 (eval_maddr m s) s.ms_mem
  | OStack (m, _) -> valid_dst_stack128 (eval_reg rRsp s) (eval_maddr m s) s.ms_stack

let update_operand64_preserve_flags'' (o:operand64) (v:nat64) (s_orig s:machine_state) : machine_state =
  match o with
  | OConst _ -> {s with ms_ok = false}
  | OReg r -> update_reg' r v s
  | OMem (m, t) -> update_mem_and_taint (eval_maddr m s_orig) v s t // see valid_maddr for how eval_maddr connects to b and i
  | OStack (m, t) -> update_stack_and_taint (eval_maddr m s_orig) v s t

let update_operand64_preserve_flags' (o:operand64) (v:nat64) (s:machine_state) : machine_state =
  update_operand64_preserve_flags'' o v s s

let update_operand128_preserve_flags'' (o:operand128) (v:quad32) (s_orig s:machine_state) : machine_state =
  match o with
  | OConst _ -> {s with ms_ok = false}
  | OReg i -> update_xmm' i v s
  | OMem (m, t) -> update_mem128_and_taint (eval_maddr m s_orig) v s t
  | OStack (m, t) -> update_stack128_and_taint (eval_maddr m s_orig) v s t

let update_operand128_preserve_flags' (o:operand128) (v:quad32) (s:machine_state) : machine_state =
  update_operand128_preserve_flags'' o v s s

// Default version havocs flags
let update_operand64' (o:operand64) (ins:ins) (v:nat64) (s:machine_state) : machine_state =
  { (update_operand64_preserve_flags' o v s) with ms_flags = havoc_state_ins s ins }

let update_rsp' (new_rsp:int) (s:machine_state) : machine_state =
  let Vale_stack init_rsp mem = s.ms_stack in
  // Only modify the stack pointer if the new value is valid, that is in the current stack frame, and in the same page
  if new_rsp >= init_rsp - 4096 && new_rsp <= init_rsp then
    update_reg' rRsp new_rsp s
  else
    s

// REVIEW: Will we regret exposing a mod here?  Should flags be something with more structure?
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
  let restricted_domain = Vale.Lib.Set.remove_between domain start finish in
  // The new domain of the stack does not contain elements between start and finish
  let new_mem = Map.restrict restricted_domain mem in
  Vale_stack init_rsp new_mem

// Define a stateful monad to simplify defining the instruction semantics
let st (a:Type) = machine_state -> a & machine_state

unfold
let return (#a:Type) (x:a) : st a =
  fun s -> (x, s)

unfold
let bind (#a:Type) (#b:Type) (m:st a) (f:a -> st b) : st b =
fun s0 ->
  let (x, s1) = m s0 in
  let (y, s2) = f x s1 in
  (y, {s2 with ms_ok = s0.ms_ok && s1.ms_ok && s2.ms_ok})

unfold
let get : st machine_state =
  fun s -> (s, s)

unfold
let set (s:machine_state) : st unit =
  fun _ -> ((), s)

unfold
let fail : st unit =
  fun s -> ((), {s with ms_ok = false})

unfold
let check_imm (valid:bool) : st unit =
  if valid then
    return ()
  else
    fail

unfold
let check (valid: machine_state -> bool) : st unit =
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
let run (f:st unit) (s:machine_state) : machine_state = snd (f s)

// Monadic update operations
unfold
let update_operand64_preserve_flags (dst:operand64) (v:nat64) : st unit =
  check (valid_dst_operand64 dst);;
  s <-- get;
  set (update_operand64_preserve_flags' dst v s)

unfold
let update_rsp (i:int) : st unit =
  // Only modify the stack pointer if the new value is valid, that is in the current stack frame, and in the same page
 check (fun s -> i >= s.ms_stack.initial_rsp - 4096);;
 check (fun s -> i <= s.ms_stack.initial_rsp);;
 s <-- get;
 set (update_rsp' i s)

let update_reg (r:reg) (v:nat64) : st unit =
  s <-- get;
  set (update_reg' r v s)

let update_xmm (x:xmm)  (ins:ins) (v:quad32) : st unit =
  s <-- get;
  set (  { (update_xmm' x v s) with ms_flags = havoc_state_ins s ins } )

let update_xmm_preserve_flags (x:xmm) (v:quad32) : st unit =
  s <-- get;
  set ( update_xmm' x v s )

let update_flags (new_flags:nat64) : st unit =
  s <-- get;
  set ( { s with ms_flags = new_flags } )

let update_cf (new_cf:bool) : st unit =
  s <-- get;
  set ( { s with ms_flags = update_cf' s.ms_flags new_cf } )

let update_of (new_of:bool) : st unit =
  s <-- get;
  set ( { s with ms_flags = update_of' s.ms_flags new_of } )

let update_cf_of (new_cf new_of:bool) : st unit =
  s <-- get;
  set ( { s with ms_flags = update_cf' (update_of' s.ms_flags new_of) new_cf } )

let free_stack (start finish:int) : st unit =
  s <-- get;
  set ( { s with ms_stack = free_stack' start finish s.ms_stack} )

let bind_option (#a #b:Type) (v:option a) (f:a -> option b) : option b =
  match v with
  | None -> None
  | Some x -> f x

let operand_obs (s:machine_state) (o:operand64) : list observation =
  match o with
  | OConst _ | OReg _ -> []
  | OMem (m, _) | OStack (m, _) ->
    match m with
    | MConst _ -> []
    | MReg reg _ -> [MemAccess (eval_reg reg s)]
    | MIndex base _ index _ -> [MemAccessOffset (eval_reg base s) (eval_reg index s)]

[@instr_attr]
let operand_obs128 (s:machine_state) (op:operand128) : list observation =
  match op with
  | OConst _ | OReg _ -> []
  | OStack (m, _) | OMem (m, _) ->
    match m with
    | MConst _ -> []
    | MReg reg _ -> [MemAccess (eval_reg reg s)]
    | MIndex base _ index _ -> [MemAccessOffset (eval_reg base s) (eval_reg index s)]

[@instr_attr]
let obs_operand_explicit
  (i:instr_operand_explicit)
  (o:instr_operand_t i)
  (s:machine_state) : list observation =
  match i with
  | IOp64 -> operand_obs s o
  | IOpXmm -> operand_obs128 s o

[@instr_attr]
let obs_operand_implicit
  (i:instr_operand_implicit)
  (s:machine_state) : list observation =
  match i with
  | IOp64One o -> operand_obs s o
  | IOpXmmOne o -> operand_obs128 s o
  | IOpFlagsCf | IOpFlagsOf -> []

[@instr_attr]
let rec obs_args
  (args:list instr_operand)
  (oprs:instr_operands_t_args args)
  (s:machine_state) : list observation =
  match args with
  | [] -> []
  | i::args ->
    match i with
    | IOpEx i ->
      let oprs = coerce oprs in
      obs_operand_explicit i (fst oprs) s @ obs_args args (snd oprs) s
    | IOpIm i ->
      obs_operand_implicit i s @ obs_args args (coerce oprs) s

[@instr_attr]
let rec obs_inouts
  (inouts:list instr_out)
  (args:list instr_operand)
  (oprs:instr_operands_t inouts args)
  (s:machine_state) : list observation =
  match inouts with
  | [] -> obs_args args oprs s
  | (_, i)::inouts ->
    let (v, oprs) =
      match i with
      | IOpEx i ->
        let oprs = coerce oprs in
        (obs_operand_explicit i (fst oprs) s), snd oprs
      | IOpIm i -> obs_operand_implicit i s, coerce oprs
    in v @ obs_inouts inouts args oprs s

[@instr_attr]
let ins_obs (ins:ins) (s:machine_state) : list observation =
  match ins with
  | BC.Instr (InstrTypeRecord #outs #args _) oprs _ -> obs_inouts outs args oprs s
  | BC.Push src _ -> operand_obs s src
  | BC.Pop dst _ -> operand_obs s dst
  | BC.Alloc _ | BC.Dealloc _ -> []

[@instr_attr]
let instr_eval_operand_explicit (i:instr_operand_explicit) (o:instr_operand_t i) (s:machine_state) : option (instr_val_t (IOpEx i)) =
  match i with
  | IOp64 -> if valid_src_operand64_and_taint o s then Some (eval_operand o s) else None
  | IOpXmm -> if valid_src_operand128_and_taint o s then Some (eval_mov128_op o s) else None

[@instr_attr]
let instr_eval_operand_implicit (i:instr_operand_implicit) (s:machine_state) : option (instr_val_t (IOpIm i)) =
  match i with
  | IOp64One o -> if valid_src_operand64_and_taint o s then Some (eval_operand o s) else None
  | IOpXmmOne o -> if valid_src_operand128_and_taint o s then Some (eval_mov128_op o s) else None
  | IOpFlagsCf -> Some (cf s.ms_flags)
  | IOpFlagsOf -> Some (overflow s.ms_flags)

[@instr_attr]
let rec instr_apply_eval_args
    (outs:list instr_out) (args:list instr_operand)
    (f:instr_args_t outs args) (oprs:instr_operands_t_args args) (s:machine_state)
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
    (f:instr_inouts_t outs inouts args) (oprs:instr_operands_t inouts args) (s:machine_state)
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
    (f:instr_eval_t outs args) (oprs:instr_operands_t outs args) (s:machine_state)
  : option (instr_ret_t outs) =
  instr_apply_eval_inouts outs outs args f oprs s

let state_or_fail (s:machine_state) (b:bool) (s':machine_state) : machine_state =
  if b then s' else {s with ms_ok = false}

[@instr_attr]
let rec instr_write_output_explicit
    (i:instr_operand_explicit) (v:instr_val_t (IOpEx i)) (o:instr_operand_t i) (s_orig s:machine_state)
  : machine_state =
  match i with
  | IOp64 ->
    state_or_fail s (valid_dst_operand64 o s_orig) (update_operand64_preserve_flags'' o v s_orig s)
  | IOpXmm ->
    state_or_fail s (valid_dst_operand128 o s_orig) (update_operand128_preserve_flags'' o v s_orig s)

[@instr_attr]
let rec instr_write_output_implicit
    (i:instr_operand_implicit) (v:instr_val_t (IOpIm i)) (s_orig s:machine_state)
  : machine_state =
  match i with
  | IOp64One o ->
    state_or_fail s (valid_dst_operand64 o s_orig) (update_operand64_preserve_flags'' o v s_orig s)
  | IOpXmmOne o ->
    state_or_fail s (valid_dst_operand128 o s_orig) (update_operand128_preserve_flags'' o v s_orig s)
  | IOpFlagsCf -> {s with ms_flags = update_cf' s.ms_flags v}
  | IOpFlagsOf -> {s with ms_flags = update_of' s.ms_flags v}

(*
For each output operand:
- compute the location of the operand in s_orig
- check that the operand is valid and update the current state (in order that the operands appear in "outs")
*)
[@instr_attr]
let rec instr_write_outputs
    (outs:list instr_out) (args:list instr_operand)
    (vs:instr_ret_t outs) (oprs:instr_operands_t outs args) (s_orig s:machine_state)
  : machine_state =
  match outs with
  | [] -> s
  | (_, i)::outs ->
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
    (it:instr_t_record) (oprs:instr_operands_t it.outs it.args) (ann:instr_annotation it)
    (s0:machine_state)
  : option machine_state =
  let InstrTypeRecord #outs #args #havoc_flags i = it in
  let vs = instr_apply_eval outs args (instr_eval i) oprs s0 in
  let s1 =
    match havoc_flags with
    | HavocFlags -> {s0 with ms_flags = havoc_state_ins s0 (BC.Instr it oprs ann)}
    | PreserveFlags -> s0
    in
  FStar.Option.mapTot (fun vs -> instr_write_outputs outs args vs oprs s0 s1) vs

// Core definition of instruction semantics
[@instr_attr]
let machine_eval_ins_st (ins:ins) : st unit =
  s <-- get;
  match ins with
  | BC.Instr it oprs ann ->
    apply_option (eval_instr it oprs ann s) set

  | BC.Push src t ->
    check (valid_src_operand64_and_taint src);;
    let new_src = eval_operand src s in            // Evaluate value on initial state
    let new_rsp = eval_reg rRsp s - 8 in           // Compute the new stack pointer
    update_rsp new_rsp;;                           // Actually modify the stack pointer
    let o_new = OStack (MConst new_rsp, t) in
    update_operand64_preserve_flags o_new new_src  // Store the element at the new stack pointer

  | BC.Pop dst t ->
    let stack_op = OStack (MReg rRsp 0, t) in
    check (valid_src_operand64_and_taint stack_op);;  // Ensure that we can read at the initial stack pointer
    let new_dst = eval_operand stack_op s in          // Get the element currently on top of the stack
    let new_rsp = (eval_reg rRsp s + 8) % pow2_64 in  // Compute the new stack pointer
    update_operand64_preserve_flags dst new_dst;;     // Store it in the dst operand
    free_stack (new_rsp - 8) new_rsp;;                // Free the memory that is popped
    update_rsp new_rsp                                // Finally, update the stack pointer

  | BC.Alloc n ->
    // We already check in update_rsp that the new stack pointer is valid
    update_rsp (eval_reg rRsp s - n)

  | BC.Dealloc n ->
    let old_rsp = eval_reg rRsp s in
    let new_rsp = old_rsp + n in
    update_rsp new_rsp;;
    // The deallocated stack memory should now be considered invalid
    free_stack old_rsp new_rsp

[@instr_attr]
let machine_eval_ins (i:ins) (s:machine_state) : machine_state =
  run (machine_eval_ins_st i) s

let machine_eval_ocmp (s:machine_state) (c:ocmp) : machine_state & bool =
  let s = run (check (valid_ocmp c)) s in
  (s, eval_ocmp s c)

(*
These functions return an option state
None case arises when the while loop runs out of fuel
*)
// TODO: IfElse and While should havoc the flags
val machine_eval_code (c:code) (fuel:nat) (s:machine_state) : Tot (option machine_state)
  (decreases %[fuel; c; 1])
val machine_eval_codes (l:codes) (fuel:nat) (s:machine_state) : Tot (option machine_state)
  (decreases %[fuel; l])
val machine_eval_while (c:code{While? c}) (fuel:nat) (s:machine_state) : Tot (option machine_state)
  (decreases %[fuel; c; 0])
let rec machine_eval_code c fuel s =
  match c with
  | Ins ins ->
    let obs = ins_obs ins s in
    // REVIEW: drop trace, then restore trace, to make clear that machine_eval_ins shouldn't depend on trace
    Some ({machine_eval_ins ins ({s with ms_trace = []}) with ms_trace = obs @ s.ms_trace})
  | Block l ->
    machine_eval_codes l fuel s
  | IfElse ifCond ifTrue ifFalse ->
    let (st, b) = machine_eval_ocmp s ifCond in
    let s' = {st with ms_trace = (BranchPredicate b)::s.ms_trace} in
    if b then machine_eval_code ifTrue fuel s' else machine_eval_code ifFalse fuel s'
  | While _ _ ->
    machine_eval_while c fuel s
and machine_eval_codes l fuel s =
  match l with
  | [] -> Some s
  | c::tl ->
    let s_opt = machine_eval_code c fuel s in
    if None? s_opt then None else machine_eval_codes tl fuel (Some?.v s_opt)
and machine_eval_while c fuel s0 =
  if fuel = 0 then None else
  let While cond body = c in
  let (s0, b) = machine_eval_ocmp s0 cond in
  if not b then Some ({s0 with ms_trace = (BranchPredicate false)::s0.ms_trace})
  else
    let s0 = {s0 with ms_trace = (BranchPredicate true)::s0.ms_trace} in
    let s_opt = machine_eval_code body (fuel - 1) s0 in
    match s_opt with
    | None -> None
    | Some s1 ->
      if s1.ms_ok then machine_eval_while c (fuel - 1) s1
      else Some s1
