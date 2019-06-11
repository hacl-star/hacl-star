module Vale.Transformers.Locations

open Vale.X64.Bytes_Code_s
open Vale.X64.Instruction_s
open Vale.X64.Instructions_s
open Vale.X64.Machine_Semantics_s
open Vale.X64.Machine_s
open Vale.X64.Print_s

open Vale.Transformers.PossiblyMonad

module L = FStar.List.Tot

(** An [location] is a portion of the [machine_state] that may be
    independently modified and/or accessed. *)
val location : eqtype

unfold
type locations = list location

(** [disjoint_location a1 a2] is true whenever locations [a1] and [a2]
    are disjoint. When not disjoint, it gives a reason for why not. *)
val disjoint_location : location -> location -> pbool

(** Disjointness is the same as syntactic equality on the locations. *)
val auto_lemma_disjoint_location :
  a1:location -> a2:location ->
  Lemma
    (ensures (!!(disjoint_location a1 a2) = (a1 <> a2)))
    [SMTPat (!!(disjoint_location a1 a2))]

(** Disjointness of a [location] from [locations] *)
let disjoint_location_from_locations (a:location) (l:locations) : pbool =
  for_all (fun b ->
      disjoint_location a b
    ) l

(** Disjointness of [locations] *)
let disjoint_locations (l1 l2:locations) : pbool =
  for_all (fun x ->
      disjoint_location_from_locations x l2
  ) l1

(** [disjoint_locations] is symmetric *)
let rec lemma_disjoint_locations_symmetric l1 l2 :
  Lemma
    (ensures (
        (!!(disjoint_locations l1 l2) = !!(disjoint_locations l2 l1))))
    (decreases %[L.length l1 + L.length l2]) =
  match l1, l2 with
  | [], [] -> ()
  | [], x :: xs | x :: xs, [] ->
    lemma_disjoint_locations_symmetric xs []
  | x :: xs, y :: ys ->
    lemma_disjoint_locations_symmetric l1 ys;
    lemma_disjoint_locations_symmetric xs l2;
    lemma_disjoint_locations_symmetric xs ys

(** [location_val_t a] is the type of the value represented by the location [a]. *)
val location_val_t : location -> Type0

(** [eval_location a s] gives the value at location [a] in state [s]. *)
val eval_location :
  a:location ->
  machine_state ->
  location_val_t a

(** [update_location a v s0] gives a new state with location [a] updated to [v]. *)
val update_location :
  a:location ->
  v:location_val_t a ->
  machine_state ->
  s:machine_state{eval_location a s == v}

(** Updating one location does not affect a different location. *)
val lemma_locations_truly_disjoint :
  a:location ->
  a_change:location ->
  v:location_val_t a_change ->
  s:machine_state ->
  Lemma
    (requires (a <> a_change))
    (ensures (eval_location a s == eval_location a (update_location a_change v s)))

(** The locations cover everything except some very explicitly mentioned parts of the state. *)
val lemma_locations_complete :
  s1:machine_state ->
  s2:machine_state ->
  ok:bool ->
  trace:list observation ->
  Lemma
    (requires (
        (forall a. eval_location a s1 == eval_location a s2)))
    (ensures (
        ({s1 with ms_ok = ok; ms_trace = trace}) ==
        ({s2 with ms_ok = ok; ms_trace = trace})))
