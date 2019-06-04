module Vale.Transformers.AccessLocations

open Vale.X64.Bytes_Code_s
open Vale.X64.Instruction_s
open Vale.X64.Instructions_s
open Vale.X64.Machine_Semantics_s
open Vale.X64.Machine_s
open Vale.X64.Print_s

open Vale.Transformers.PossiblyMonad

module L = FStar.List.Tot


val access_location : eqtype

type access_locations = list access_location

type rw_set = access_locations & access_locations

val rw_set_of_ins : i:ins -> rw_set

val disjoint_access_location : access_location -> access_location -> pbool

val lemma_disjoint_access_location :
  a1:access_location -> a2:access_location ->
  Lemma
    (ensures (!!(disjoint_access_location a1 a2) = (a1 <> a2)))

val lemma_disjoint_access_location_symmetric :
  a1:access_location -> a2:access_location ->
  Lemma
    (ensures (!!(disjoint_access_location a1 a2) = !!(disjoint_access_location a2 a1)))

let disjoint_access_location_from_locations (a:access_location) (l:access_locations) : pbool =
  for_all (fun b ->
      disjoint_access_location a b
    ) l

let disjoint_access_locations (l1 l2:access_locations) (r:string) : pbool =
  for_all (fun x ->
      disjoint_access_location_from_locations x l2 /+< (r ^ " because ")
  ) l1

let rec lemma_disjoint_access_locations_reason l1 l2 r1 r2 :
  Lemma
    (!!(disjoint_access_locations l1 l2 r1) = !!(disjoint_access_locations l1 l2 r2)) =
  match l1 with
  | [] -> ()
  | _ :: xs -> lemma_disjoint_access_locations_reason xs l2 r1 r2

let rec lemma_disjoint_access_locations_symmetric l1 l2 r :
  Lemma
    (ensures (
        (!!(disjoint_access_locations l1 l2 r) = !!(disjoint_access_locations l2 l1 r))))
    (decreases %[L.length l1 + L.length l2]) =
  match l1, l2 with
  | [], [] -> ()
  | [], x :: xs | x :: xs, [] ->
    lemma_disjoint_access_locations_symmetric xs [] r
  | x :: xs, y :: ys ->
    lemma_disjoint_access_location_symmetric x y;
    lemma_disjoint_access_locations_symmetric l1 ys r;
    lemma_disjoint_access_locations_symmetric xs l2 r;
    lemma_disjoint_access_locations_symmetric xs ys r

val access_location_val_t : access_location -> Type0

val eval_access_location :
  a:access_location ->
  machine_state ->
  access_location_val_t a
