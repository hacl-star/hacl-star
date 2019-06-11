module Vale.Transformers.BoundedInstructionEffects

open Vale.X64.Bytes_Code_s
open Vale.X64.Instruction_s
open Vale.X64.Instructions_s
open Vale.X64.Machine_Semantics_s
open Vale.X64.Machine_s
open Vale.X64.Print_s

open Vale.Transformers.Locations
friend Vale.Transformers.Locations

module L = FStar.List.Tot

private
let both (x: locations & locations) =
  let a, b = x in
  a `L.append` b

(* See fsti *)
let rw_set_of_ins i =
  match i with
  | Instr i oprs _ ->
    read_set i oprs, write_set i oprs
  | Push src t ->
    ALocReg (Reg 0 rRsp) :: both (locations_of_operand64 src),
    [ALocReg (Reg 0 rRsp); ALocStack]
  | Pop dst t ->
    ALocReg (Reg 0 rRsp) :: ALocStack :: fst (locations_of_operand64 dst),
    ALocReg (Reg 0 rRsp) :: snd (locations_of_operand64 dst)
  | Alloc _
  | Dealloc _ ->
    [ALocReg (Reg 0 rRsp)], [ALocReg (Reg 0 rRsp)]
