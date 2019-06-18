module Vale.Transformers.LiveAnalysis

open FStar.Calc

open Vale.X64.Bytes_Code_s
open Vale.X64.Instruction_s
open Vale.X64.Instructions_s
open Vale.X64.Machine_Semantics_s
open Vale.X64.Machine_s
open Vale.X64.Print_s

open Vale.Transformers.PossiblyMonad
open Vale.Transformers.Locations
open Vale.Transformers.BoundedInstructionEffects

module L = FStar.List.Tot

let implies x y = x ==> y

(* TODO: Is there a built-in for this? *)
irreducible
let rec locations_difference (a b:locations) : (res:locations{
    forall x. {:pattern (L.mem x res)}
      (L.mem x res) = ((L.mem x a) && (not (L.mem x b)))
  }) =
  match a with
  | [] -> []
  | x :: xs ->
    if L.mem x b then (
      locations_difference xs b
    ) else (
      x :: locations_difference xs b
    )

(* TODO: Is there a built-in for this? *)
irreducible
let rec locations_union (a b:locations) : (res:locations{
    forall x. {:pattern (L.mem x res)}
      (L.mem x res) = (L.mem x a || L.mem x b)
  }) =
  match a with
  | [] -> (
      match b with
      | [] -> []
      | y :: ys ->
        if L.mem y ys then (
          locations_union [] ys
        ) else (
          y :: locations_union [] ys
        )
    )
  | x :: xs ->
    if L.mem x b then (
      locations_union xs b
    ) else (
      x :: locations_union xs b
    )

unfold let (+++) = locations_union
unfold let (---) = locations_difference

let live_of_ins (i:ins) (post:locations) : locations =
  let r, w = rw_set_of_ins i in
  (post --- w) +++ r

let live_of_ocmp (o:ocmp) (post:locations) : locations =
  post +++ locations_of_ocmp o

let rec live_of_code (c:code) (post:locations) : locations =
  match c with
  | Ins i -> live_of_ins i post
  | Block l -> live_of_codes l post
  | IfElse c t f ->
    live_of_ocmp c
      (live_of_code t post +++
       live_of_code f post)
  | While c b ->
    post +++
    live_of_ocmp c
      (live_of_code b post)

and live_of_codes (c:codes) (post:locations) : locations =
  match c with
  | [] -> post
  | x :: xs ->
    live_of_code x (live_of_codes xs post)

(* REVIEW: There are some similarities of the following portion with
           the InstructionReorder module. Break out the common parts into a
           separate module? *)
let unchanged_at' (locs:locations) (s1 s2:machine_state) =
  (s1.ms_ok = s2.ms_ok) /\
  (s1.ms_ok ==>
   unchanged_at locs s1 s2)

unfold
let erroring_option_state (s:option machine_state) =
  match s with
  | None -> true
  | Some s -> not (s.ms_ok)

let unchanged_at'' (locs:locations) (s1 s2:option machine_state) =
  (erroring_option_state s1 == erroring_option_state s2) /\
  (not (erroring_option_state s1) ==>
   unchanged_at' locs (Some?.v s1) (Some?.v s2))

let rec lemma_not_ok_propagate_code (c:code) (fuel:nat) (s:machine_state) :
  Lemma
    (requires (not s.ms_ok))
    (ensures (erroring_option_state (machine_eval_code c fuel s)))
    (decreases %[fuel; c; 1]) =
  match c with
  | Ins _ -> ()
  | Block l ->
    lemma_not_ok_propagate_codes l fuel s
  | IfElse ifCond ifTrue ifFalse ->
    let (st, b) = machine_eval_ocmp s ifCond in
    let s' = {st with ms_trace = (BranchPredicate b)::s.ms_trace} in
    if b then lemma_not_ok_propagate_code ifTrue fuel s' else lemma_not_ok_propagate_code ifFalse fuel s'
  | While _ _ ->
    lemma_not_ok_propagate_while c fuel s

and lemma_not_ok_propagate_codes (l:codes) (fuel:nat) (s:machine_state) :
  Lemma
    (requires (not s.ms_ok))
    (ensures (erroring_option_state (machine_eval_codes l fuel s)))
    (decreases %[fuel; l]) =
  match l with
  | [] -> ()
  | x :: xs ->
    lemma_not_ok_propagate_code x fuel s;
    match machine_eval_code x fuel s with
    | None -> ()
    | Some s -> lemma_not_ok_propagate_codes xs fuel s

and lemma_not_ok_propagate_while (c:code{While? c}) (fuel:nat) (s:machine_state) :
  Lemma
    (requires (not s.ms_ok))
    (ensures (erroring_option_state (machine_eval_code c fuel s)))
    (decreases %[fuel; c; 0]) =
  if fuel = 0 then () else (
    let While cond body = c in
    let (s, b) = machine_eval_ocmp s cond in
    if not b then () else (
      let s = { s with ms_trace = (BranchPredicate true) :: s.ms_trace } in
      lemma_not_ok_propagate_code body (fuel - 1) s
    )
  )

let rec lemma_unchanged_at'_intro (locs:locations) (s1 s2:machine_state) :
  Lemma
    (requires (
        (s1.ms_ok = s2.ms_ok) /\
        (forall x. {:pattern (L.mem x locs)} s1.ms_ok /\ L.mem x locs ==> eval_location x s1 == eval_location x s2)))
    (ensures (unchanged_at' locs s1 s2)) =
  match locs with
  | [] -> ()
  | x :: xs ->
    assert (L.mem x locs); (* OBSERVE *)
    assert (forall x. L.mem x xs ==> L.mem x locs); (* OBSERVE *)
    lemma_unchanged_at'_intro xs s1 s2

let rec lemma_unchanged_at'_elim (locs:locations) (s1 s2:machine_state) :
  Lemma
    (requires (unchanged_at' locs s1 s2))
    (ensures (forall x. {:pattern (L.mem x locs)} s1.ms_ok /\ L.mem x locs ==> eval_location x s1 == eval_location x s2)) =
  match locs with
  | [] -> ()
  | x :: xs ->
    lemma_unchanged_at'_elim xs s1 s2

let lemma_unchanged_at'_smaller (locs locs_smaller:locations) (s1 s2:machine_state) :
  Lemma
    (requires (
        (unchanged_at' locs s1 s2) /\
        (forall x. L.mem x locs_smaller ==> L.mem x locs)))
    (ensures (unchanged_at' locs_smaller s1 s2)) =
  lemma_unchanged_at'_elim locs s1 s2;
  lemma_unchanged_at'_intro locs_smaller s1 s2

let rec lemma_live_of_code (c:code) (post:locations) (fuel:nat) (s1 s2:machine_state) :
  Lemma
    (requires (unchanged_at' (live_of_code c post) s1 s2))
    (ensures (unchanged_at'' post
                (machine_eval_code c fuel s1)
                (machine_eval_code c fuel s2)))
    (decreases %[c; fuel; 1]) =
  let pre = live_of_code c post in
  if s1.ms_ok then (
    match c with
    | Ins i ->
      admit () (* TODO: Prove *)
    | Block l ->
      lemma_live_of_codes l post fuel s1 s2
    | IfElse c t f ->
      lemma_unchanged_at'_smaller pre (locations_of_ocmp c) s1 s2;
      lemma_locations_of_ocmp c s1 s2;
      let st1, b1 = machine_eval_ocmp s1 c in
      let st2, b2 = machine_eval_ocmp s2 c in
      assert (unchanged_at' pre st1 st2);
      assert (b1 = b2);
      let s1' = { st1 with ms_trace = (BranchPredicate b1) :: st1.ms_trace } in
      let s2' = { st2 with ms_trace = (BranchPredicate b2) :: st2.ms_trace } in
      lemma_locations_same_with_filter st1 s1'.ms_flags s1'.ms_ok s1'.ms_trace;
      lemma_locations_same_with_filter st2 s2'.ms_flags s2'.ms_ok s2'.ms_trace;
      assert (FunctionalExtensionality.feq
                (filter_state st1 s1'.ms_flags s1'.ms_ok s1'.ms_trace).ms_flags
                s1'.ms_flags); (* OBSERVE *)
      assert (FunctionalExtensionality.feq
                (filter_state st2 s2'.ms_flags s2'.ms_ok s2'.ms_trace).ms_flags
                s2'.ms_flags); (* OBSERVE *)
      lemma_unchanged_at'_elim pre st1 st2;
      lemma_unchanged_at'_intro pre s1' s2';
      assert (unchanged_at' pre s1' s2');
      if b1 then (
        lemma_unchanged_at'_smaller pre (live_of_code t post) s1' s2';
        lemma_live_of_code t post fuel s1' s2'
      ) else (
        lemma_unchanged_at'_smaller pre (live_of_code f post) s1' s2';
        lemma_live_of_code f post fuel s1' s2'
      )
    | While _ _ ->
      lemma_live_of_while c post fuel s1 s2
  ) else (
    lemma_not_ok_propagate_code c fuel s1;
    lemma_not_ok_propagate_code c fuel s2
  )

and lemma_live_of_codes (c:codes) (post:locations) (fuel:nat) (s1 s2:machine_state) :
  Lemma
    (requires (unchanged_at' (live_of_codes c post) s1 s2))
    (ensures (unchanged_at'' post
                (machine_eval_codes c fuel s1)
                (machine_eval_codes c fuel s2)))
    (decreases %[c; fuel]) =
  match c with
  | [] -> ()
  | x :: xs ->
    lemma_live_of_code x (live_of_codes xs post) fuel s1 s2;
    match machine_eval_code x fuel s1, machine_eval_code x fuel s2 with
    | None, None -> ()
    | Some s1', None -> lemma_not_ok_propagate_codes xs fuel s1'
    | None, Some s2' -> lemma_not_ok_propagate_codes xs fuel s2'
    | Some s1', Some s2' ->
      lemma_live_of_codes xs post fuel s1' s2'

and lemma_live_of_while (c:code{While? c}) (post:locations) (fuel:nat) (s1 s2:machine_state) :
  Lemma
    (requires (unchanged_at' (live_of_code c post) s1 s2))
    (ensures (unchanged_at'' (live_of_code c post) (* Stronger than just for [post] *)
                (machine_eval_code c fuel s1)
                (machine_eval_code c fuel s2) /\
              unchanged_at'' post
                (machine_eval_code c fuel s1)
                (machine_eval_code c fuel s2)))
    (decreases %[c; fuel; 0]) =
  let pre = live_of_code c post in
  if s1.ms_ok then (
    if fuel = 0 then () else (
      let While cond body = c in
      lemma_unchanged_at'_smaller pre (locations_of_ocmp cond) s1 s2;
      lemma_locations_of_ocmp cond s1 s2;
      let (s01, b1) = machine_eval_ocmp s1 cond in
      let (s02, b2) = machine_eval_ocmp s2 cond in
      assert (b1 = b2);
      if not b1 then (
        let s01' = {s01 with ms_trace = (BranchPredicate false)::s01.ms_trace} in
        let s02' = {s02 with ms_trace = (BranchPredicate false)::s02.ms_trace} in
        assert (unchanged_at' pre s01 s02);
        assert ((FunctionalExtensionality.feq
                   (filter_state s01 s01'.ms_flags s01'.ms_ok s01'.ms_trace).ms_flags
                   s01'.ms_flags) /\
                (FunctionalExtensionality.feq
                   (filter_state s02 s02'.ms_flags s02'.ms_ok s02'.ms_trace).ms_flags
                   s02'.ms_flags)); (* OBSERVE *)
        lemma_locations_same_with_filter s01 s01'.ms_flags s01'.ms_ok s01'.ms_trace;
        lemma_locations_same_with_filter s02 s02'.ms_flags s02'.ms_ok s02'.ms_trace;
        lemma_unchanged_at'_elim pre s01 s02;
        lemma_unchanged_at'_intro pre s01' s02';
        lemma_unchanged_at'_smaller pre post s01' s02'
      ) else (
        let s01' = {s01 with ms_trace = (BranchPredicate true)::s01.ms_trace} in
        let s02' = {s02 with ms_trace = (BranchPredicate true)::s02.ms_trace} in
        assert (unchanged_at' pre s01 s02);
        assert ((FunctionalExtensionality.feq
                   (filter_state s01 s01'.ms_flags s01'.ms_ok s01'.ms_trace).ms_flags
                   s01'.ms_flags) /\
                (FunctionalExtensionality.feq
                   (filter_state s02 s02'.ms_flags s02'.ms_ok s02'.ms_trace).ms_flags
                   s02'.ms_flags));
        lemma_locations_same_with_filter s01 s01'.ms_flags s01'.ms_ok s01'.ms_trace;
        lemma_locations_same_with_filter s02 s02'.ms_flags s02'.ms_ok s02'.ms_trace;
        lemma_unchanged_at'_elim pre s01 s02;
        lemma_unchanged_at'_intro pre s01' s02';
        assert (unchanged_at' pre s01' s02'); (* OBSERVE *)
        admit ();
        (* The proof below won't ever work since we don't take a fixpoint :/ *)
        lemma_live_of_code body pre (fuel-1) s01' s02';
        admit ()
      )
    )
  ) else (
    lemma_not_ok_propagate_code c fuel s1;
    lemma_not_ok_propagate_code c fuel s2
  )
