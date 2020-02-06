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

type peephole = (p:pre_peephole{forall is s. {:pattern (peephole_correct p is s)}
                                  peephole_correct p is s})

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

let rec apply_peephole_to_codes (input_hint:pos) (p:peephole) (cs:codes) :
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

/// And now, for the proofs!

let rec lemma_wrap_instructions (is:list ins) (s:machine_state) (fuel:nat) :
  Lemma
    (requires True)
    (ensures (
        equiv_option_states
          (machine_eval_codes (wrap_instructions is) fuel s)
          (Some (eval_inss is s)))) =
  match is with
  | [] -> ()
  | i :: is' ->
    lemma_eval_ins_equiv_states i s ({s with ms_trace = []});
    let Some s1 = machine_eval_code (Ins i) fuel s in
    let s2 = machine_eval_ins i s in
    lemma_wrap_instructions is' s2 fuel;
    lemma_eval_codes_equiv_states (wrap_instructions is') fuel s1 s2

let rec lemma_pull_instructions_from_codes (cs:codes) (num:pos) (s:machine_state) (fuel:nat) :
  Lemma
    (requires (Some? (pull_instructions_from_codes cs num)))
    (ensures (
        let Some (is, cs1) = pull_instructions_from_codes cs num in
        equiv_option_states
          (machine_eval_codes cs fuel s)
          (machine_eval_codes cs1 fuel (eval_inss is s))))
    (decreases %[num_blocks_in_codes cs; num]) =
  match cs with
  | [] -> ()
  | c :: cs' ->
    match c with
    | Ins i -> (
        if num = 1 then (
          lemma_eval_ins_equiv_states i s ({s with ms_trace = []});
          assert (equiv_option_states
                    (machine_eval_code c fuel s)
                    (Some (machine_eval_ins i s)));
          assert_norm (machine_eval_ins i s == eval_inss [i] s);
          assert (equiv_option_states
                    (machine_eval_code c fuel s)
                    (Some (eval_inss [i] s)));
          let Some s1 = machine_eval_code c fuel s in
          let s2 = eval_inss [i] s in
          lemma_eval_codes_equiv_states cs' fuel s1 s2
        ) else (
          match pull_instructions_from_codes cs' (num - 1) with
          | None -> ()
          | Some (is2, cs'') ->
            lemma_eval_ins_equiv_states i s ({s with ms_trace = []});
            assert (equiv_option_states
                      (machine_eval_code c fuel s)
                      (Some (machine_eval_ins i s)));
            let Some s1 = machine_eval_code c fuel s in
            let s2 = machine_eval_ins i s in
            lemma_eval_codes_equiv_states cs' fuel s1 s2;
            lemma_pull_instructions_from_codes cs' (num - 1) s2 fuel
        )
      )
    | Block l -> (
        lemma_pull_instructions_from_codes (l `L.append` cs') num s fuel;
        lemma_machine_eval_codes_block_to_append l cs' fuel s
      )
    | IfElse _ _ _ -> ()
    | While _ _ -> ()

#push-options "--z3rlimit 10"
let rec lemma_apply_peephole_to_codes (input_hint:pos) (p:peephole) (cs:codes)
    (s:machine_state) (fuel:nat) :
  Lemma
    (requires True)
    (ensures (
        equiv_option_states
          (machine_eval_codes cs fuel s)
          (machine_eval_codes (apply_peephole_to_codes input_hint p cs) fuel s)))
    (decreases %[num_ins_in_codes cs; cs]) =
  match cs with
  | [] -> ()
  | c :: cs' ->
    match pull_instructions_from_codes cs input_hint with
    | None -> (
        match machine_eval_code c fuel s with
        | None -> ()
        | Some s1 ->
          lemma_apply_peephole_to_codes input_hint p cs' s1 fuel
      )
    | Some (is, cs'') -> (
        match p is with
        | None -> (
            match machine_eval_code c fuel s with
            | None -> ()
            | Some s1 ->
              lemma_apply_peephole_to_codes input_hint p cs' s1 fuel
          )
        | Some is' -> (
            lemma_pull_instructions_from_codes cs input_hint s fuel;
            assert (equiv_option_states
                     (machine_eval_codes cs fuel s)
                     (machine_eval_codes cs'' fuel (eval_inss is s)));
            assert (peephole_correct p is s); (* OBSERVE *)
            assert (equiv_states_or_both_not_ok
                     (eval_inss is s)
                     (eval_inss is' s));
            let s1 = eval_inss is s in
            let s2 = eval_inss is' s in
            lemma_wrap_instructions is' s fuel;
            let s3' = machine_eval_code (Block (wrap_instructions is')) fuel s in
            if s1.ms_ok then () else lemma_not_ok_propagate_codes cs'' fuel s1;
            if s1.ms_ok then (
              let Some s3 = s3' in
              lemma_eval_codes_equiv_states cs'' fuel s1 s3;
              lemma_apply_peephole_to_codes input_hint p cs'' s3 fuel
            ) else (
              match s3' with
              | None -> ()
              | Some s3 ->
                lemma_not_ok_propagate_codes cs'' fuel s3;
                assert (equiv_option_states
                         (machine_eval_codes cs'' fuel s1)
                         (machine_eval_codes cs'' fuel s3));
                assert (equiv_option_states
                         (machine_eval_codes cs fuel s)
                         (machine_eval_codes cs'' fuel s3));
                assert (equiv_option_states
                         (machine_eval_codes cs fuel s)
                         (machine_eval_codes (Block (wrap_instructions is') :: cs'') fuel s));
                assert ((apply_peephole_to_codes input_hint p cs) ==
                             (Block (wrap_instructions is') ::
                              (apply_peephole_to_codes input_hint p cs'')));
                lemma_apply_peephole_to_codes input_hint p cs'' s3 fuel;
                assert (equiv_option_states
                         (machine_eval_codes cs fuel s)
                         (machine_eval_codes (apply_peephole_to_codes input_hint p cs) fuel s))
            )
          )
      )
#pop-options

let rec lemma_apply_peephole_to_code (input_hint:pos) (p:peephole) (c:code)
    (s:machine_state) (fuel:nat) :
  Lemma
    (requires True)
    (ensures (
        equiv_option_states
          (machine_eval_code c fuel s)
          (machine_eval_code (apply_peephole_to_code input_hint p c) fuel s)))
    (decreases %[num_ins_in_code c; c; fuel; 1]) =
  match c with
  | Ins i -> (
      if input_hint = 1 then (
        match p [i] with
        | None -> ()
        | Some is ->
          assert (peephole_correct p [i] s); (* OBSERVE *)
          assert_norm (eval_inss [i] s == machine_eval_ins i s); (* OBSERVE *)
          lemma_wrap_instructions is s fuel;
          lemma_eval_ins_equiv_states i s ({s with ms_trace = []})
      ) else (
        ()
      )
    )
  | Block l -> (
      lemma_apply_peephole_to_codes input_hint p l s fuel
    )
  | IfElse cc tt ff -> (
      let (st, b) = machine_eval_ocmp s cc in
      let s' = {st with ms_trace = (BranchPredicate b)::s.ms_trace} in
      if b then (
        lemma_apply_peephole_to_code input_hint p tt s' fuel
      ) else (
        lemma_apply_peephole_to_code input_hint p ff s' fuel
      )
    )
  | While _ _ -> (
      lemma_apply_peephole_to_code_while input_hint p c s fuel
    )

and lemma_apply_peephole_to_code_while (input_hint:pos) (p:peephole) (c:code{While? c})
    (s:machine_state) (fuel:nat) :
  Lemma
    (requires True)
    (ensures (
        equiv_option_states
          (machine_eval_code c fuel s)
          (machine_eval_code (apply_peephole_to_code input_hint p c) fuel s)))
    (decreases %[num_ins_in_code c; c; fuel; 0]) =
  let c' = apply_peephole_to_code input_hint p c in
  if fuel = 0 then (
    assert_norm (machine_eval_code c fuel s == None);
    assert_norm (machine_eval_code c' fuel s == None)
  ) else (
    let While cond body = c in
    let (s0, b) = machine_eval_ocmp s cond in
    if not b then (
      assert_norm (machine_eval_code c fuel s ==
                   machine_eval_code c' fuel s)
    ) else (
      let s0 = {s0 with ms_trace = (BranchPredicate true)::s0.ms_trace} in
      let body' = apply_peephole_to_code input_hint p body in
      let s_opt1 = machine_eval_code body (fuel - 1) s0 in
      let s_opt2 = machine_eval_code body' (fuel - 1) s0 in
      lemma_apply_peephole_to_code input_hint p body s0 (fuel - 1);
      assert (equiv_option_states s_opt1 s_opt2);
      match s_opt1 with
      | None -> (
          assert_norm (machine_eval_code c fuel s == None);
          match s_opt2 with
          | None -> (
              assert_norm (machine_eval_code c fuel s ==
                           machine_eval_code c' fuel s)
            )
          | Some s2 -> (
              assert (~ s2.ms_ok);
              assert_norm (machine_eval_code c' fuel s == Some s2)
            )
        )
      | Some s1 -> (
          match s_opt2 with
          | None -> (
              assert_norm (machine_eval_code c fuel s == Some s1);
              assert_norm (machine_eval_code c' fuel s == None)
            )
          | Some s2 -> (
              assert (s1.ms_ok == s2.ms_ok);
              if not s1.ms_ok then (
                assert_norm (machine_eval_code c fuel s == Some s1);
                assert_norm (machine_eval_code c' fuel s == Some s2)
              ) else (
                assert_norm (machine_eval_code c fuel s == machine_eval_code c (fuel - 1) s1);
                assert_norm (machine_eval_code c' fuel s == machine_eval_code c' (fuel - 1) s2);
                lemma_eval_code_equiv_states c (fuel - 1) s1 s2;
                lemma_apply_peephole_to_code input_hint p c s2 (fuel - 1)
              )
            )
        )
    )
  )
