module Vale.Transformers.InstructionReorderSanityChecks

open Vale.X64.Bytes_Code_s
open Vale.X64.Instruction_s
open Vale.X64.Instructions_s
open Vale.X64.Machine_Semantics_s
open Vale.X64.Machine_s
open Vale.X64.Print_s

open Vale.X64.InsLemmas // this one is from [code]; is that ok?; we use it primarily for the sanity checks

open Vale.Transformers.PossiblyMonad

open Vale.Transformers.Locations
friend Vale.Transformers.Locations

open Vale.Transformers.InstructionReorder

private abstract
let ins_exchange_sanity_check1 =
  assert_norm (!!(
    ins_exchange_allowed
      (make_instr ins_Mov64 (OReg rRax) (OConst 100))
      (make_instr ins_Add64 (OReg rRbx) (OConst 299))))

private abstract
[@expect_failure]
let ins_exchange_sanity_check2 =
  assert_norm (!!(
    ins_exchange_allowed
      (make_instr ins_Mov64 (OReg rRax) (OConst 100))
      (make_instr ins_Add64 (OReg rRax) (OConst 299))))

private abstract
let sanity_check_unchanged_except1 s =
  assert (unchanged_except [] s s);
  assert (unchanged_except [ALocCf] s s);
  assert (unchanged_except [ALocCf; ALocOf] s ({s with ms_flags = 0}))

private abstract
[@expect_failure]
let sanity_check_unchanged_except2 s =
  assert (unchanged_except [] s ({s with ms_flags = 0}))
