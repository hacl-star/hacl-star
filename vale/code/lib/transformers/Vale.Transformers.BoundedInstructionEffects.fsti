module Vale.Transformers.BoundedInstructionEffects

open Vale.X64.Bytes_Code_s
open Vale.X64.Machine_s
open Vale.X64.Machine_Semantics_s

open Vale.Def.PossiblyMonad
open Vale.Transformers.Locations

module L = FStar.List.Tot

(** A [location_with_value] contains a location and the value it must hold *)
type location_with_value = l:location_eq & location_val_eqt l

(** A [locations_with_values] contains locations and values they must hold *)
type locations_with_values = list location_with_value

(** An [rw_set] contains information about what locations are read and
     written by a stateful operation. *)
type rw_set = {
     loc_reads: locations;
     loc_writes: locations;
     loc_constant_writes: locations_with_values;
}

(** [rw_set_of_ins i] returns the read/write sets for the execution of
    an instruction. *)
val rw_set_of_ins : i:ins -> rw_set

(** [locations_of_ocmp o] returns the read set for a comparison operator. *)
val locations_of_ocmp : o:ocmp -> locations

(** [unchanged_except exc s1 s2] means all locations that are disjoint
    from the exceptions [exc] have the same value in both [s1] and [s2]. *)
let unchanged_except (exceptions:locations) (s1 s2:machine_state) :
  GTot Type0 =
  (forall (a:location). {:pattern (eval_location a s2)} (
      (!!(disjoint_location_from_locations a exceptions) ==>
       (eval_location a s1 == eval_location a s2))
    ))

(** [only_affects locs f] means that running [f] leaves everything
    except [locs] unchanged. *)
let only_affects (locs:locations) (f:st unit) : GTot Type0 =
  forall s. {:pattern unchanged_except locs s (run f s)} (
    (run f s).ms_ok ==> unchanged_except locs s (run f s)
  )

(** [unchanged_at locs s1 s2] means the the value of any location in
    [locs] is same in both [s1] and [s2]. *)
let rec unchanged_at (locs:locations) (s1 s2:machine_state) : GTot Type0 =
  match locs with
  | [] -> True
  | x :: xs -> (
      (eval_location x s1 == eval_location x s2) /\
      (unchanged_at xs s1 s2)
    )

(** [constant_on_execution locv f s] means that running [f] on [s]
    ensures that the values of the locations in [locv] always match
    the values given to them in [locv]. *)
let rec constant_on_execution (locv:locations_with_values) (f:st unit) (s:machine_state) : GTot Type0 =
  (run f s).ms_ok ==> (
    match locv with
    | [] -> True
    | (|l, v|) :: xs -> (
        (eval_location l (run f s) == raise_location_val_eqt v) /\
        (constant_on_execution xs f s)
      )
  )

(** [bounded_effects rw f] means that the execution of [f] is bounded
    by the read-write [rw]. This means that whenever two different
    states are same at the locations in [rw.loc_reads], then the
    function will have the same effect, and that its effect is bounded
    to the set [rw.loc_writes]. Additionally, execution always causes
    the resultant state to cause the results to be written as per
    [rw.loc_constant_writes]. *)
let bounded_effects (rw:rw_set) (f:st unit) : GTot Type0 =
  (only_affects rw.loc_writes f) /\
  (forall s. {:pattern (constant_on_execution rw.loc_constant_writes f s)}
     constant_on_execution rw.loc_constant_writes f s) /\
  (forall l v. {:pattern (L.mem (|l,v|) rw.loc_constant_writes); (L.mem l rw.loc_writes)}
     L.mem (|l,v|) rw.loc_constant_writes ==> L.mem l rw.loc_writes) /\
  (
    forall s1 s2. {:pattern (run f s1); (run f s2)} (
      (s1.ms_ok = s2.ms_ok /\ unchanged_at rw.loc_reads s1 s2) ==> (
        ((run f s1).ms_ok = (run f s2).ms_ok) /\
        ((run f s1).ms_ok ==>
         unchanged_at rw.loc_writes (run f s1) (run f s2))
      )
    )
  )

(** Safely bounded instructions are instructions that we can guarantee
    [bounded_effects] upon their execution. For the rest of the
    instructions, we currently don't have proofs about
    [bounded_effects] for them. *)
let safely_bounded (i:ins) =
  Instr? i

(** The evaluation of an instruction [i] is bounded by the read/write
    set given by [rw_set_of_ins i]. *)
val lemma_machine_eval_ins_st_bounded_effects :
  (i:ins) ->
  Lemma
    (requires (safely_bounded i))
    (ensures (
        (bounded_effects (rw_set_of_ins i) (machine_eval_ins_st i))))

(** The evaluation of a [code] which is just an instruction [i] is
    bounded by the read/write set given by [rw_set_of_ins i]. *)
val lemma_machine_eval_code_Ins_bounded_effects :
  (i:ins) ->
  (fuel:nat) ->
  Lemma
    (requires (safely_bounded i))
    (ensures (
        (bounded_effects (rw_set_of_ins i)
           (fun s -> (), (Some?.v (machine_eval_code (Ins i) fuel s))))))

(** The evaluation of a comparison [o] depends solely upon its
    locations, given by [locations_of_ocmp o] *)
val lemma_locations_of_ocmp : o:ocmp -> s1:machine_state -> s2:machine_state ->
  Lemma
    (requires (unchanged_at (locations_of_ocmp o) s1 s2))
    (ensures (eval_ocmp s1 o == eval_ocmp s2 o))

(** Add more values into the reads portion of an [rw_set] *)
let add_r_to_rw_set (r:locations) (rw:rw_set) : rw_set =
  { rw with loc_reads = r `L.append` rw.loc_reads }

(** Merge two [rw_set]s that for executions that might go either
    way. *)
val rw_set_in_parallel : rw_set -> rw_set -> rw_set

(** Merge two [rw_set]s that for executions go through the first one
    and _then_ the second. *)
val rw_set_in_series : rw_set -> rw_set -> rw_set

(** [bounded_effects] is held correctly when adding to the reads *)
val lemma_add_r_to_rw_set :
  r:locations ->
  rw:rw_set ->
  f:st unit ->
  Lemma
    (requires (
        (bounded_effects rw f)))
    (ensures (
        (bounded_effects (add_r_to_rw_set r rw) f)))

(** [bounded_effects] is held correctly when applied in parallel *)
val lemma_bounded_effects_parallel :
  rw1:rw_set -> rw2:rw_set ->
  f1:st unit -> f2:st unit ->
  Lemma
    (requires (
        (bounded_effects rw1 f1) /\
        (bounded_effects rw2 f2)))
    (ensures (
        (bounded_effects (rw_set_in_parallel rw1 rw2) f1) /\
        (bounded_effects (rw_set_in_parallel rw1 rw2) f2)))

(** [bounded_effects] is held correctly when applied in series *)
val lemma_bounded_effects_series :
  rw1:rw_set -> rw2:rw_set ->
  f1:st unit -> f2:st unit ->
  Lemma
    (requires (
        (bounded_effects rw1 f1) /\
        (bounded_effects rw2 f2)))
    (ensures (
        let open Vale.X64.Machine_Semantics_s in
        (bounded_effects (rw_set_in_series rw1 rw2) (f1;;f2))))
