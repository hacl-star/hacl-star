module Vale.Transformers.BoundedInstructionEffects

open Vale.X64.Machine_Semantics_s

open Vale.Transformers.Locations

(** An [rw_set] is the pair of [locations] that are respectively read
    and written by an operation. *)
type rw_set = locations & locations

(** [rw_set_of_ins i] returns the read/write sets for the execution of
    an instruction. *)
val rw_set_of_ins : i:ins -> rw_set
