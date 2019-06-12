module Vale.Transformers.BoundedInstructionEffects

open Vale.X64.Machine_Semantics_s

open Vale.Transformers.PossiblyMonad
open Vale.Transformers.Locations

(** An [rw_set] is the pair of [locations] that are respectively read
    and written by an operation. *)
type rw_set = locations & locations

(** [rw_set_of_ins i] returns the read/write sets for the execution of
    an instruction. *)
val rw_set_of_ins : i:ins -> rw_set

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
    unchanged_except locs s (run f s)
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

(** [bounded_effects r w f] means that the execution of [f] is bounded
    by the read-set [r] and write-set [w]. This means that whenever
    two different states are same at the locations in [r], then the
    function will have the same effect, and that its effect is bounded
    to the set [w]. *)
let bounded_effects (reads writes:locations) (f:st unit) : GTot Type0 =
  (only_affects writes f) /\
  (
    forall s1 s2. {:pattern unchanged_at writes (run f s1) (run f s2)} (
      unchanged_at reads s1 s2 ==> (
        ((run f s1).ms_ok = (run f s2).ms_ok) /\
        ((run f s1).ms_ok ==>
         unchanged_at writes (run f s1) (run f s2))
      )
    )
  )

(** The evaluation of an instruction [i] is bounded by the read/write
    set given by [rw_set_of_ins i]. *)
val lemma_machine_eval_ins_st_bounded_effects :
  (i:ins) ->
  Lemma
    (ensures (
        (let r, w = rw_set_of_ins i in
         (bounded_effects r w (machine_eval_ins_st i)))))
