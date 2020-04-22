(**

   This module defines a control flow lowering transform, which
   eliminates all cases of [IfElse] and [While], making them
   [Unstructured] instead.

   This is generally expected the be the last transformer to be used.

*)
module Vale.Transformers.ControlFlowLowering

open Vale.Transformers.Common


open Vale.X64.Decls
open Vale.X64.Lemmas
open Vale.X64.StateLemmas
open Vale.Transformers.Common

open Vale.X64.Bytes_Code_s
open Vale.X64.Instruction_s
open Vale.X64.Instructions_s
open Vale.X64.Machine_Semantics_s
open Vale.X64.Machine_s
open Vale.X64.Print_s

module L = FStar.List.Tot

open Vale.Transformers.InstructionReorder // open so that we don't
                                          // need to redefine things
                                          // equivalence etc.

open Vale.X64.InsLemmas

let lower_if (cond:ocmp) (ifTrue ifFalse:code) : code =
  (*
     start:
       if not cond, jump to label_false
       ifTrue code
       jump to done
     label_false:
       ifFalse code
     done:
  *)
  let c0 = Block [] in
  let j0 = {jump_cond = JIfFalse cond; jump_target = 2} in
  let c1 = ifTrue in
  let j1 = {jump_cond = JAlways; jump_target = 3} in
  let c2 = ifFalse in
  let j2 = {jump_cond = JNever; jump_target = 3} in (* REVIEW: JAlways or JNever? *)
  Unstructured [
    c0, j0;
    c1, j1;
    c2, j2;
  ]

let lower_while (cond:ocmp) (body:code) : code =
  (*
     start:
       if not cond, jump to done
       body code
       jump to start
     done:
  *)
  let c0 = Block [] in
  let j0 = {jump_cond = JIfFalse cond; jump_target = 2} in
  let c1 = body in
  let j1 = {jump_cond = JAlways; jump_target = 0} in
  Unstructured [
    c0, j0;
    c1, j1;
  ]

let rec lower_code (c:code) : code =
  match c with
  | Ins _ -> c
  | Block l -> Block (lower_codes l)
  | IfElse c t f ->
    lower_if c (lower_code t) (lower_code f)
  | While c b ->
    lower_while c (lower_code b)
  | Unstructured blocks ->
    Unstructured (lower_unstructured blocks)

and lower_codes (cs:codes) : codes =
  match cs with
  | [] -> []
  | h :: t -> lower_code h :: lower_codes t

and lower_unstructured (blocks:list ublock) : list ublock =
  allow_inversion (ublock);
  match blocks with
  | [] -> []
  | (c, j) :: t ->
    (lower_code c, j) :: lower_unstructured t
