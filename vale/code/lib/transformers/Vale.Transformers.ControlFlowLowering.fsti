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

let rec lemma_more_fuel_code (c:code) (fuel1 fuel2:nat) (s:machine_state) :
  Lemma
    (requires (
        (fuel1 <= fuel2) /\
        (Some? (machine_eval_code c fuel1 s))))
    (ensures (
        (machine_eval_code c fuel2 s == machine_eval_code c fuel1 s)))
    (decreases %[fuel1; fuel2; c]) =
  match c with
  | Ins _ -> ()
  | Block l -> lemma_more_fuel_codes l fuel1 fuel2 s
  | IfElse c t f ->
    let (s1, b) = machine_eval_ocmp s c in
    if b then
      lemma_more_fuel_code t fuel1 fuel2 s1
    else
      lemma_more_fuel_code f fuel1 fuel2 s1
  | While c b ->
    lemma_more_fuel_while c b fuel1 fuel2 s
  | Unstructured blocks ->
    lemma_more_fuel_unstructured blocks 0 fuel1 fuel2 s

and lemma_more_fuel_codes (cs:codes) (fuel1 fuel2:nat) (s:machine_state) :
  Lemma
    (requires (
        (fuel1 <= fuel2) /\
        (Some? (machine_eval_codes cs fuel1 s))))
    (ensures (
        (machine_eval_codes cs fuel2 s == machine_eval_codes cs fuel1 s)))
    (decreases %[fuel1; fuel2; cs]) =
  match cs with
  | [] -> ()
  | h :: t ->
    lemma_more_fuel_code h fuel1 fuel2 s;
    let Some s1 = machine_eval_code h fuel1 s in
    lemma_more_fuel_codes t fuel1 fuel2 s1

and lemma_more_fuel_while (cond:ocmp) (body:code) (fuel1 fuel2:nat) (s:machine_state) :
  Lemma
    (requires (
        (fuel1 <= fuel2) /\
        (Some? (machine_eval_while cond body fuel1 s))))
    (ensures (
        (machine_eval_while cond body fuel2 s == machine_eval_while cond body fuel1 s)))
    (decreases %[fuel1; fuel2; body]) =
  let (s1, b) = machine_eval_ocmp s cond in
  if not b then () else (
    let Some s2 = machine_eval_code body (fuel1 - 1) s1 in
    lemma_more_fuel_code body (fuel1 - 1) (fuel2 - 1) s1;
    if not s2.ms_ok then () else (
      lemma_more_fuel_while cond body (fuel1 - 1) (fuel2 - 1) s2
    )
  )

and lemma_more_fuel_unstructured (blocks:list ublock) (n:nat) (fuel1 fuel2:nat) (s:machine_state) :
  Lemma
    (requires (
        (fuel1 <= fuel2) /\
        (Some? (machine_eval_unstructured blocks n fuel1 s))))
    (ensures (
        (machine_eval_unstructured blocks n fuel2 s ==
         machine_eval_unstructured blocks n fuel1 s)))
    (decreases %[fuel1; fuel2; blocks; remaining_blocks blocks n]) =
  if n >= List.Tot.length blocks then () else (
    let (c, j) = list_index blocks n in
    let Some s1 = machine_eval_code c fuel1 s in
    lemma_more_fuel_code c fuel1 fuel2 s;
    if not s1.ms_ok then () else (
      let (s2, jump_taken) = machine_eval_jump_condition s1 j.jump_cond in
      let n' = if jump_taken then j.jump_target else n + 1 in
      let fuel1' : int = if n < n' then fuel1 else fuel1 - 1 in
      let fuel2' : int = if n < n' then fuel2 else fuel2 - 1 in
      lemma_more_fuel_unstructured blocks n' fuel1' fuel2' s2
    )
  )

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

#push-options "--fuel 4 --ifuel 1"
let lemma_lower_if (cond:ocmp) (ifTrue ifFalse:code) (fuel:nat) (s:machine_state) :
  Lemma
    (requires (s.ms_ok))
    (ensures (
        let c0 = IfElse cond ifTrue ifFalse in
        let c1 = lower_if cond ifTrue ifFalse in
        machine_eval_code c0 fuel s ==
        machine_eval_code c1 fuel s)) =
  ()
#pop-options

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

#push-options "--fuel 4 --ifuel 0"
let rec lemma_lower_while (cond:ocmp) (body:code) (fuel:nat) (s:machine_state) :
  Lemma
    (requires (
        let c0 = While cond body in
        (s.ms_ok) /\
        (Some? (machine_eval_code c0 fuel s) /\ (
            let Some s1 = machine_eval_code c0 fuel s in
            s1.ms_ok
          )
        )))
    (ensures (
        let c0 = While cond body in
        let c1 = lower_while cond body in
        machine_eval_code c0 fuel s ==
        machine_eval_code c1 fuel s)) =
  let c0 = While cond body in
  let c1 = lower_while cond body in
  let (s0, b0) = machine_eval_ocmp s cond in
  if (b0 && fuel > 0) then (
    let Some s1 = machine_eval_code body (fuel - 1) s0 in
    lemma_lower_while cond body (fuel - 1) s1;
    // assert (machine_eval_code c0 (fuel - 1) s1 == machine_eval_code c1 (fuel - 1) s1);
    // assert (machine_eval_code c0 fuel s == machine_eval_code c0 (fuel - 1) s1);
    let Unstructured blocks = c1 in
    // assert (machine_eval_code c1 fuel s == machine_eval_unstructured blocks 0 fuel s);
    let (c, j) = list_index blocks 0 in
    let (ss, jt) = machine_eval_jump_condition s j.jump_cond in
    // assert (ss == s0);
    // assert (not jt);
    // assert (machine_eval_unstructured blocks 0 fuel s == machine_eval_unstructured blocks 1 fuel ss);
    let Some ss1 = machine_eval_code body (fuel - 1) ss in
    lemma_more_fuel_code body (fuel - 1) fuel ss;
    // assert (machine_eval_code body fuel ss == Some ss1);
    // assert (machine_eval_unstructured blocks 0 fuel s == machine_eval_unstructured blocks 0 (fuel - 1) s1);
    // assert (machine_eval_code c1 fuel s == machine_eval_code c1 (fuel - 1) s1);
    ()
  ) else (
    ()
  )
#pop-options

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
