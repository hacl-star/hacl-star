module Vale.Transformers.Locations

open Vale.X64.Bytes_Code_s
open Vale.X64.Instruction_s
open Vale.X64.Instructions_s
open Vale.X64.Machine_Semantics_s
open Vale.X64.Machine_s
open Vale.X64.Print_s

open Vale.Transformers.PossiblyMonad

module L = FStar.List.Tot

(* See fsti *)
type location : eqtype =
  | ALocMem : location
  | ALocStack: location
  | ALocReg : reg -> location
  | ALocXmm : xmm -> location
  | ALocCf : location
  | ALocOf : location

let locations_of_maddr (m:maddr) : locations =
  match m with
  | MConst _ -> []
  | MReg r _ -> [ALocReg r]
  | MIndex b _ i _ -> [ALocReg b; ALocReg i]

let locations_of_operand (o:operand) : locations & locations =
  match o with
  | OConst _ -> [], []
  | OReg r -> [ALocReg r], [ALocReg r]
  | OMem (m, _) -> locations_of_maddr m, [ALocMem]
  | OStack (m, _) -> locations_of_maddr m, [ALocStack]

let locations_of_operand128 (o:operand128) : locations & locations =
  match o with
  | OReg128 r -> [ALocXmm r], [ALocXmm r]
  | OMem128 (m, _) -> locations_of_maddr m, [ALocMem]
  | OStack128 (m, _) -> locations_of_maddr m, [ALocStack]

private
let both (x: locations & locations) =
  let a, b = x in
  a `L.append` b

let locations_of_explicit (t:instr_operand_explicit) (i:instr_operand_t t) : locations & locations =
  match t with
  | IOp64 -> locations_of_operand i
  | IOpXmm -> locations_of_operand128 i

let locations_of_implicit (t:instr_operand_implicit) : locations & locations =
  match t with
  | IOp64One i -> locations_of_operand i
  | IOpXmmOne i -> locations_of_operand128 i
  | IOpFlagsCf -> [ALocCf], [ALocCf]
  | IOpFlagsOf -> [ALocOf], [ALocOf]

let rec aux_read_set0 (args:list instr_operand) (oprs:instr_operands_t_args args) : locations =
  match args with
  | [] -> []
  | (IOpEx i) :: args ->
    let l, r = coerce #(instr_operand_t i & instr_operands_t_args args) oprs in
    both (locations_of_explicit i l) `L.append` aux_read_set0 args r
  | (IOpIm i) :: args ->
    both (locations_of_implicit i) `L.append` aux_read_set0 args (coerce #(instr_operands_t_args args) oprs)

let rec aux_read_set1
    (outs:list instr_out) (args:list instr_operand) (oprs:instr_operands_t outs args) : locations =
  match outs with
  | [] -> aux_read_set0 args oprs
  | (Out, IOpEx i) :: outs ->
    let l, r = coerce #(instr_operand_t i & instr_operands_t outs args) oprs in
    fst (locations_of_explicit i l) `L.append` aux_read_set1 outs args r
  | (InOut, IOpEx i) :: outs ->
    let l, r = coerce #(instr_operand_t i & instr_operands_t outs args) oprs in
    both (locations_of_explicit i l) `L.append` aux_read_set1 outs args r
  | (Out, IOpIm i) :: outs ->
    fst (locations_of_implicit i) `L.append` aux_read_set1 outs args (coerce #(instr_operands_t outs args) oprs)
  | (InOut, IOpIm i) :: outs ->
    both (locations_of_implicit i) `L.append` aux_read_set1 outs args (coerce #(instr_operands_t outs args) oprs)

let read_set (i:instr_t_record) (oprs:instr_operands_t i.outs i.args) : locations =
  aux_read_set1 i.outs i.args oprs

let rec aux_write_set
    (outs:list instr_out) (args:list instr_operand) (oprs:instr_operands_t outs args) : locations =
  match outs with
  | [] -> []
  | (_, IOpEx i) :: outs ->
    let l, r = coerce #(instr_operand_t i & instr_operands_t outs args) oprs in
    snd (locations_of_explicit i l) `L.append` aux_write_set outs args r
  | (_, IOpIm i) :: outs ->
    snd (locations_of_implicit i) `L.append` aux_write_set outs args (coerce #(instr_operands_t outs args) oprs)

let write_set (i:instr_t_record) (oprs:instr_operands_t i.outs i.args) : list location =
  let InstrTypeRecord #outs #args #havoc_flags _ = i in
  let ws = aux_write_set outs args oprs in
  match havoc_flags with
  | HavocFlags -> ALocCf :: ALocOf :: ws
  | PreserveFlags -> ws

(* See fsti *)
let rw_set_of_ins i =
  match i with
  | Instr i oprs _ ->
    read_set i oprs, write_set i oprs
  | Push src t ->
    ALocReg rRsp :: both (locations_of_operand src),
    [ALocReg rRsp; ALocStack]
  | Pop dst t ->
    ALocReg rRsp :: ALocStack :: fst (locations_of_operand dst),
    ALocReg rRsp :: snd (locations_of_operand dst)
  | Alloc _
  | Dealloc _ ->
    [ALocReg rRsp], [ALocReg rRsp]

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
    (r1 <> r2) /- ("register " ^ print_reg_name r1 ^ " not disjoint from itself")
  | ALocXmm r1, ALocXmm r2 ->
    (r1 <> r2) /- ("xmm-register " ^ print_reg_name r1 ^ " not disjoint from itself")
  | ALocReg _, _ | ALocXmm _, _ | _, ALocReg _ | _, ALocXmm _ -> ttrue

(* See fsti *)
let lemma_disjoint_location a1 a2 = ()

(* See fsti *)
let location_val_t a =
  match a with
  | ALocMem -> heap & memTaint_t
  | ALocStack -> stack & memTaint_t
  | ALocReg _ -> nat64
  | ALocXmm _ -> quad32
  | ALocCf -> bool
  | ALocOf -> bool

(* See fsti *)
let eval_location a s =
  match a with
  | ALocMem -> s.ms_mem, s.ms_memTaint
  | ALocStack -> s.ms_stack, s.ms_stackTaint
  | ALocReg r -> eval_reg r s
  | ALocXmm r -> eval_xmm r s
  | ALocCf -> cf s.ms_flags
  | ALocOf -> overflow s.ms_flags

(* See fsti *)
let update_location a v s =
  match a with
  | ALocMem ->
    let v = coerce v in
    { s with ms_mem = fst v ; ms_memTaint = snd v }
  | ALocStack ->
    let v = coerce v in
    { s with ms_stack = fst v ; ms_stackTaint = snd v }
  | ALocReg r ->
    update_reg' r v s
  | ALocXmm r ->
    update_xmm' r v s
  | ALocCf ->
    { s with ms_flags = update_cf' s.ms_flags v }
  | ALocOf ->
    { s with ms_flags = update_of' s.ms_flags v }

(* See fsti *)
let lemma_locations_truly_disjoint a a_change v s = ()
