module Vale.InstructionReorder

/// Open all the relevant modules from the x64 semantics.

open Vale.X64.Bytes_Code_s
open Vale.X64.Instruction_s
open Vale.X64.Instructions_s
open Vale.X64.Machine_Semantics_s
open Vale.X64.Machine_s
open Vale.X64.Print_s

/// Open the PossiblyMonad so that we can keep track of failure cases
/// for easier debugging.

open Vale.PossiblyMonad

/// Finally some convenience module renamings

module L = FStar.List.Tot

/// We first define what it means for two [operand]s to be
/// "disjoint".

let disjoint_operands (o1 o2:operand) : pbool =
  match o1, o2 with
  | OConst _, _ | _, OConst _ -> ttrue
  | OReg r1, OReg r2 -> (r1 <> r2) /- ("same register " ^ print_reg_name r1)
  | _ -> unimplemented "conservatively not disjoint"

/// For every instruction, we can define a write-set and a read-set

(* TODO FIXME

   The current version only models 64 bit operands, and completely
   ignores anything else that is input/output to an instruction.  *)
type access_location =
  operand

type read_set = list access_location

type write_set = list access_location

type rw_set = read_set * write_set

let rw_set_of_ins (i:ins) : rw_set =
  match i with
  | Instr i oprs annot ->
    admit ()
  | Push src _ ->
    admit ()
  | Pop dst _ ->
    admit ()
  | Alloc _
  | Dealloc _ ->
    [OReg rRsp], [OReg rRsp]

/// Given two read/write sets corresponding to two neighboring
/// instructions, we can say whether exchanging those two instructions
/// should be allowed.

let rw_exchange_allowed (rw1 rw2 : rw_set) : pbool =
  let (r1, w1), (r2, w2) = rw1, rw2 in
  let (&&.) (x y:pbool) : pbool =
    match x with
    | ttrue -> y
    | _ -> x in
  let rec for_all (f : 'a -> pbool) (l : list 'a) : pbool =
    match l with
    | [] -> ttrue
    | x :: xs -> f x &&. for_all f xs in
  let disjoint (l1 l2:list operand) r : pbool =
    match l1 with
    | [] -> ttrue
    | x :: xs ->
      (for_all (fun y -> (disjoint_operands x y)) l2) /+< (r ^ " because ") in
  (disjoint r1 w2 "read set of 1st not disjoint from write set of 2nd") &&.
  (disjoint r2 w2 "read set of 2nd not disjoint from write set of 1st") &&.
  (disjoint w1 w2 "write sets not disjoint")

let ins_exchange_allowed (i1 i2 : ins) : pbool =
  (rw_exchange_allowed (rw_set_of_ins i1) (rw_set_of_ins i2))
  /+> (" for instructions " ^ print_ins i1 gcc ^ " and " ^ print_ins i2 gcc)

/// First, we must define what it means for two states to be
/// equivalent. We currently assume that we can _completely_ ignore
/// the flags. This is a terrible idea, and should be fixed ASAP.
///
/// WARNING UNSOUND TODO FIXME

let equiv_states (s1 s2 : machine_state) : GTot Type0 =
  admit ()

private abstract
let sanity_check_equiv_states (s1 s2 s3 : machine_state) :
  Lemma
    (ensures (
        (equiv_states s1 s1) /\
        (equiv_states s1 s2 ==> equiv_states s2 s1) /\
        (equiv_states s1 s2 /\ equiv_states s2 s3 ==> equiv_states s1 s3))) =
  admit ()

/// If an exchange is allowed between two instructions based off of
/// their read/write sets, then both orderings of the two instructions
/// behave exactly the same, as per the previously defined
/// [equiv_states] relation.

let lemma_instruction_exchange (i1 i2 : ins) (s1 s2 : machine_state) :
  Lemma
    (requires (
        !!(ins_exchange_allowed i1 i2) /\
        (equiv_states s1 s2)))
    (ensures (
        (let s1', s2' =
           machine_eval_ins i1 (machine_eval_ins i2 s1),
           machine_eval_ins i2 (machine_eval_ins i1 s2) in
         equiv_states s1' s2'))) =
  admit ()

/// Given that we can perform simple swaps between instructions, we
/// can define a relation that tells us if a sequence of instructions
/// can be transformed into another using only swaps allowed via the
/// [ins_exchange_allowed] relation.

let reordering_allowed (c1 c2 : codes) : pbool =
  admit ()

/// If there are two sequences of instructions that can be transformed
/// amongst each other, then they behave identically as per the
/// [equiv_states] relation.

let lemma_reordering (c1 c2 : codes) (fuel:nat) (s1 s2 : machine_state) :
  Lemma
    (requires (
        !!(reordering_allowed c1 c2) /\
        (equiv_states s1 s2) /\
        (Some? (machine_eval_codes c1 fuel s1))))
    (ensures (
        (Some? (machine_eval_codes c2 fuel s2)) /\
        (let Some s1', Some s2' =
           machine_eval_codes c1 fuel s1,
           machine_eval_codes c2 fuel s2 in
         equiv_states s1' s2'))) =
  admit ()
