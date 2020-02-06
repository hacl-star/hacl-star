(**

   This module defines a framework for peephole transformers. It needs
   to be instantiated with an actual pattern to generate a verified
   peephole transform. In particular, it needs to be provided a
   [peephole] to obtain a new transformer.

   See the movbe elimination transformer for examples of how to use
   this framework.

*)
module Vale.Transformers.PeepHole

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

let coerce_to_normal (#a:Type0) (x:a) : y:(normal a){x == y} = x

let rec eval_inss (is:list ins) (s:machine_state) : GTot machine_state =
  match is with
  | [] -> s
  | i :: is' -> eval_inss is' (machine_eval_ins i s)

/// Define what a peephole means, and what it means to be correct.

type pre_peephole = list ins -> Tot (option (list ins))

let peephole_correct (p:pre_peephole) (is:list ins) (s:machine_state) : GTot Type0 =
  match p is with
  | None -> True
  | Some is' ->
    equiv_states_or_both_not_ok
      (eval_inss is s)
      (eval_inss is' s)

type peephole = (p:pre_peephole{forall is s. peephole_correct p is s})

/// Now for the framework portion. This uses the provided [peephole]
/// to produce a new transformer that is proven correct. We also
/// require a "input_hint" which specifies the size of data that
/// should be passed into the peephole function, in terms of number of
/// instructions. This allows us to make the transformer faster.

/// First off, some metrics for proving termination.

let rec num_ins_in_code (c:code) : nat =
  match c with
  | Ins _ -> 1
  | Block l -> num_ins_in_codes l
  | IfElse c t f -> num_ins_in_code t + num_ins_in_code f
  | While c b -> num_ins_in_code b

and num_ins_in_codes (c:codes) : nat =
  match c with
  | [] -> 0
  | h :: t -> num_ins_in_code h + num_ins_in_codes t

let rec lemma_num_ins_in_codes_append (c1 c2:codes) :
  Lemma
    (ensures (num_ins_in_codes (c1 `L.append` c2) == num_ins_in_codes c1 + num_ins_in_codes c2)) =
  match c1 with
  | [] -> ()
  | x :: xs -> lemma_num_ins_in_codes_append xs c2

/// Next, we want to be able to "pull off" some instructions from
/// given code, and if necessary, "wrap" them back into code.

let rec pull_instructions_from_codes (cs:codes) (num:pos) :
  Pure (option (list ins & codes))
    (requires (True))
    (ensures (function
         | None -> True
         | Some (_, cs') -> num_ins_in_codes cs' < num_ins_in_codes cs))
    (decreases %[num_blocks_in_codes cs; num]) =
  match cs with
  | [] -> None
  | c :: cs' ->
    match c with
    | Ins i -> if num = 1 then (
        assert_norm (num_ins_in_codes cs' < num_ins_in_codes cs); (* OBSERVE *)
        Some ([i], cs')
      ) else (
        match pull_instructions_from_codes cs' (num - 1) with
        | None -> None
        | Some (is2, cs'') ->
          Some (i :: is2, cs'')
      )
    | Block l ->
      lemma_num_ins_in_codes_append l cs';
      assert_norm (num_ins_in_codes l + num_ins_in_codes cs' == num_ins_in_codes cs);
      pull_instructions_from_codes (l `L.append` cs') num
    | IfElse _ _ _ -> None
    | While _ _ -> None

let rec wrap_instructions (is:list ins) : Tot codes =
  match is with
  | [] -> []
  | i :: is' -> Ins i :: wrap_instructions is'

/// Finally, the implementation that repeatedly finds a group of
/// instructions and tries to apply the peephole transformation to
/// them.

let rec apply_peephole_to_code (input_hint:pos) (p:peephole) (c:code) :
  Tot code
    (decreases %[num_ins_in_code c; c]) =
  match c with
  | Ins i -> (
      if input_hint = 1 then (
        match p [i] with
        | None -> c
        | Some is -> Block (wrap_instructions is)
      ) else (
        c
      )
    )
  | Block l -> (
      let l' = apply_peephole_to_codes input_hint p l in
      Block l'
    )
  | IfElse c t f -> (
      let t' = apply_peephole_to_code input_hint p t in
      let f' = apply_peephole_to_code input_hint p f in
      IfElse c t' f'
    )
  | While c b -> (
      let b' = apply_peephole_to_code input_hint p b in
      While c b'
    )

and apply_peephole_to_codes (input_hint:pos) (p:peephole) (cs:codes) :
  Tot codes
    (decreases %[num_ins_in_codes cs; cs]) =
  match cs with
  | [] -> []
  | c :: cs' ->
    match pull_instructions_from_codes cs input_hint with
    | None -> c :: apply_peephole_to_codes input_hint p cs'
    | Some (is, cs'') ->
      match p is with
      | None -> c :: apply_peephole_to_codes input_hint p cs'
      | Some is' ->
        Block (wrap_instructions is') ::
        apply_peephole_to_codes input_hint p cs''

/// And now, for the proofs!

(* TODO *)
