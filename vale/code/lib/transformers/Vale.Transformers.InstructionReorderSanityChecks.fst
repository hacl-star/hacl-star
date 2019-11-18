module Vale.Transformers.InstructionReorderSanityChecks

open Vale.X64.Bytes_Code_s
open Vale.X64.Instruction_s
open Vale.X64.Instructions_s
open Vale.X64.Machine_Semantics_s
open Vale.X64.Machine_s
open Vale.X64.Print_s

open Vale.X64.InsLemmas // this one is from [code]; is that ok?; we use it primarily for the sanity checks

open Vale.Def.PossiblyMonad

open Vale.Transformers.Locations
friend Vale.Transformers.Locations

open Vale.Transformers.BoundedInstructionEffects
friend Vale.Transformers.BoundedInstructionEffects

open Vale.Transformers.InstructionReorder

#push-options "--lax" (* XXX: This part of the file causes an F* SMTEncoding bug. I've reported it, and once it is fixed, we should remove this --lax *)
let ins_exchange_sanity_check1_1 : pbool =
  normalize_term (
    ins_exchange_allowed
      (make_instr ins_IMul64 (OReg rRax) (OReg rRbx))
      (make_instr ins_IMul64 (OReg rRcx) (OReg rRdx))
    )

let ins_exchange_sanity_check1_2 : pbool =
  normalize_term (
    ins_exchange_allowed
      (make_instr ins_Mov64 (OReg rRax) (OConst 100))
      (make_instr ins_Add64 (OReg rRbx) (OConst 299))
  )

let ins_exchange_sanity_check1 =
  assert_norm !!(ins_exchange_sanity_check1_1);
  assert_norm !!(ins_exchange_sanity_check1_2)
#pop-options

[@expect_failure]
let ins_exchange_sanity_check2 =
  assert_norm (!!(
    ins_exchange_allowed
      (make_instr ins_Mov64 (OReg rRax) (OConst 100))
      (make_instr ins_Add64 (OReg rRax) (OConst 299))))

let equiv_states_sanity_check (s1 s2 s3 : machine_state) =
  assert_norm (equiv_states s1 s1);
  assert_norm (equiv_states s1 s2 ==> equiv_states s2 s1);
  assert_norm (equiv_states s1 s2 /\ equiv_states s2 s3 ==> equiv_states s1 s3);
  assert_norm (
    forall trace. (
        (
          (({s1 with ms_trace = trace}) == ({s2 with ms_trace = trace})) ==>
          (equiv_states s1 s2)
        )
      )
  )

#push-options "--initial_fuel 2 --max_fuel 2 --initial_ifuel 1 --max_ifuel 1"
let sanity_check_unchanged_except1 s =
  assert (unchanged_except [] s s);
  assert (unchanged_except [ALocCf] s s);
  assert (unchanged_except [ALocCf; ALocOf] s ({s with ms_flags = havoc_flags}))
#pop-options

[@expect_failure]
let sanity_check_unchanged_except2 s =
  assert (unchanged_except [] s ({s with ms_flags = havoc_flags}))
