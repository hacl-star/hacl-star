module Vale.Transformers.Locations

open Vale.X64.Bytes_Code_s
open Vale.X64.Instruction_s
open Vale.X64.Instructions_s
open Vale.X64.Machine_Semantics_s
open Vale.X64.Machine_s
open Vale.X64.Print_s

open Vale.Def.PossiblyMonad

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

(** Inversion lemma based on FStar.Universe.downgrade_val_raise_val, with more liberal SMTPat *)
val downgrade_val_raise_val_u0_u1 :
  #a:Type0 ->
  x:a ->
  Lemma
    (ensures FStar.Universe.downgrade_val u#0 u#1 (FStar.Universe.raise_val x) == x)
    [SMTPat (FStar.Universe.raise_val x)]

(** [location_val_t a] is the type of the value represented by the location [a]. *)
val location_val_t : location -> Type u#1

(** Same as location_val_t in cases where location_val_t is an eqtype, otherwise arbitrary *)
val location_val_eqt : location -> eqtype

(** Locations where location_val_t is an eqtype *)
let location_eq = l:location{location_val_t l == FStar.Universe.raise_t (location_val_eqt l)}

(** Coerce location_val_eqt to location_val_t *)
let raise_location_val_eqt (#l:location_eq) (v:location_val_eqt l) : location_val_t l =
  coerce (FStar.Universe.raise_val v)

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

(** Filter out things we don't want to compare on two states *)
let filter_state (s:machine_state) (flags:flags_t) (ok:bool) (trace:list observation) =
  { s with
    ms_flags = FunctionalExtensionality.on_dom flag
        (fun f ->
           if f = fCarry then
             s.ms_flags fCarry
           else if f = fOverflow then
             s.ms_flags fOverflow
           else
             flags f ) ;
    ms_ok = ok ;
    ms_trace = trace }

(** The locations cover everything except some very explicitly mentioned parts of the state. *)
val lemma_locations_complete :
  s1:machine_state ->
  s2:machine_state ->
  flags:flags_t ->
  ok:bool ->
  trace:list observation ->
  Lemma
    (requires (
        (forall a. eval_location a s1 == eval_location a s2)))
    (ensures (
        filter_state s1 flags ok trace ==
        filter_state s2 flags ok trace))

(** Filtering the state does not affect it wrt locations. *)
val lemma_locations_same_with_filter :
  s:machine_state ->
  flags:flags_t ->
  ok:bool ->
  trace:list observation ->
  Lemma
    (ensures (
        let s' = filter_state s flags ok trace in
        (forall a. {:pattern (eval_location a s')}
           (eval_location a s == eval_location a s'))))
