module Vale.X64.Bytes_Code_s

open FStar.Mul
open Vale.X64.Machine_s
open Vale.X64.Instruction_s
open Vale.Arch.HeapTypes_s
open Vale.Arch.Heap

type instr_annotation_t = instr_t_record -> Type0

noeq type instruction_t (a:instr_annotation_t) =
  // Generic instruction (should be able to express most instructions)
  | Instr :
      i:instr_t_record ->
      oprs:instr_operands_t i.outs i.args ->
      annotation:a i ->
      instruction_t a
  // Stack operations
  | Push       : src:operand64 -> t:taint -> instruction_t a
  | Pop        : dst:operand64 -> t:taint -> instruction_t a
  | Alloc      : n:nat64 -> instruction_t a
  | Dealloc    : n:nat64 -> instruction_t a

type ocmp:eqtype =
  | OEq: o1:operand64{not (OMem? o1 || OStack? o1)} -> o2:operand64{not (OMem? o2 || OStack? o2)} -> ocmp
  | ONe: o1:operand64{not (OMem? o1 || OStack? o1)} -> o2:operand64{not (OMem? o2 || OStack? o2)} -> ocmp
  | OLe: o1:operand64{not (OMem? o1 || OStack? o1)} -> o2:operand64{not (OMem? o2 || OStack? o2)} -> ocmp
  | OGe: o1:operand64{not (OMem? o1 || OStack? o1)} -> o2:operand64{not (OMem? o2 || OStack? o2)} -> ocmp
  | OLt: o1:operand64{not (OMem? o1 || OStack? o1)} -> o2:operand64{not (OMem? o2 || OStack? o2)} -> ocmp
  | OGt: o1:operand64{not (OMem? o1 || OStack? o1)} -> o2:operand64{not (OMem? o2 || OStack? o2)} -> ocmp

type code_t (a:instr_annotation_t) = precode (instruction_t a) ocmp
type codes_t (a:instr_annotation_t) = list (code_t a)
