module Vale.Transformers.AccessLocations

open Vale.X64.Bytes_Code_s
open Vale.X64.Instruction_s
open Vale.X64.Instructions_s
open Vale.X64.Machine_Semantics_s
open Vale.X64.Machine_s
open Vale.X64.Print_s

open Vale.Transformers.PossiblyMonad

module L = FStar.List.Tot

(** An [access_location] is a portion of the [machine_state] that may
    be independently modified and/or accessed. *)
val access_location : eqtype

unfold
type access_locations = list access_location

(** An [rw_set] is the pair of [access_locations] that are
    respectively read and written by an operation. *)
type rw_set = access_locations & access_locations

(** [rw_set_of_ins i] returns the read/write sets for the execution of
    an instruction. *)
val rw_set_of_ins : i:ins -> rw_set

(** [disjoint_access_location a1 a2] is true whenever [a1] and [a2]
    are disjoint. When not disjoint, it gives a reason for why not. *)
val disjoint_access_location : access_location -> access_location -> pbool

(** Disjointness is the same as syntactic equality on the locations. *)
val lemma_disjoint_access_location :
  a1:access_location -> a2:access_location ->
  Lemma
    (ensures (!!(disjoint_access_location a1 a2) = (a1 <> a2)))

(** Disjointness of an [access_location] from [access_locations] *)
let disjoint_access_location_from_locations (a:access_location) (l:access_locations) : pbool =
  for_all (fun b ->
      disjoint_access_location a b
    ) l

(** Disjointness of [access_locations] *)
let disjoint_access_locations (l1 l2:access_locations) : pbool =
  for_all (fun x ->
      disjoint_access_location_from_locations x l2
  ) l1

(** [disjoint_access_locations] is symmetric *)
let rec lemma_disjoint_access_locations_symmetric l1 l2 :
  Lemma
    (ensures (
        (!!(disjoint_access_locations l1 l2) = !!(disjoint_access_locations l2 l1))))
    (decreases %[L.length l1 + L.length l2]) =
  match l1, l2 with
  | [], [] -> ()
  | [], x :: xs | x :: xs, [] ->
    lemma_disjoint_access_locations_symmetric xs []
  | x :: xs, y :: ys ->
    lemma_disjoint_access_location x y;
    lemma_disjoint_access_location y x;
    lemma_disjoint_access_locations_symmetric l1 ys;
    lemma_disjoint_access_locations_symmetric xs l2;
    lemma_disjoint_access_locations_symmetric xs ys

(** [access_location_val_t a] is the type of the value represented by the location [a]. *)
val access_location_val_t : access_location -> Type0

(** [eval_access_location a s] gives the value at location [a] in state [s]. *)
val eval_access_location :
  a:access_location ->
  machine_state ->
  access_location_val_t a

(** [update_access_location a v s0] gives a new state with [a] updated to [v]. *)
val update_access_location :
  a:access_location ->
  v:access_location_val_t a ->
  machine_state ->
  s:machine_state{eval_access_location a s == v}

(** Updating one access location does not affect other access locations *)
val lemma_access_locations_truly_disjoint :
  a:access_location ->
  a_change:access_location ->
  v:access_location_val_t a_change ->
  s:machine_state ->
  Lemma
    (requires (a <> a_change))
    (ensures (eval_access_location a s == eval_access_location a (update_access_location a_change v s)))
