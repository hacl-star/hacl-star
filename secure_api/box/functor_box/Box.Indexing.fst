(**
   This module contains functions and various lemmas concerning indices. Indices (ids) are used to link keys and plaintexts to a
   certain instance in the cryptographic model. This module also contains tables to reflect freshness and honesty of ids.
   TODO: Remove all state from this module.
   * move honesty information into the AE and DH module
   * use "registered" instead of fresh
   * remove unused lemmas
   * get rid of the assumes
*)
module Box.Indexing

open FStar.Set
open FStar.Seq
open FStar.HyperHeap
open FStar.HyperStack
open FStar.HyperStack.ST

open Box.Flags

module MR = FStar.Monotonic.RRef
module MM = MonotoneMap
module Curve = Spec.Curve25519


type id_log_region = (r:MR.rid{extends r root /\ is_eternal_region r /\ is_below r root})

type honesty =
  | UNDEFINED
  | HONEST
  | DISHONEST

type id_log_value = honesty
let id_log_range = fun id_log_key -> id_log_value
let id_log_inv (id_log_kt:Type0) (m:MM.map' id_log_kt id_log_range) = True

type id_log_t (rgn:id_log_region) (id_log_kt:Type0) = MM.t rgn id_log_kt id_log_range (id_log_inv id_log_kt)

abstract noeq type index_module =
  | IM:
    rgn: (id_log_region) ->
    subId: (t:Type0{hasEq t}) -> // express that there is a total order on ids
    compose_ids: (subId -> subId -> (subId*subId)) ->
    id_log: (id_log_t rgn subId) ->
    index_module


type id (im:index_module) = i:(im.subId*im.subId) // add refinement once total order on subids is established{fst i <= snd i}

noeq type meta_id (im:index_module) =
  | ID of id im
  | SUBID of im.subId

// Anything below here should probably be in the "user-module"
#set-options "--z3rlimit 300 --max_ifuel 1 --max_fuel 1"
assume val symmetric_id_generation (im:index_module): i1:im.subId -> i2:im.subId -> Lemma
  (requires (True))
  (ensures (forall id1 id2. im.compose_ids id1 id2 = im.compose_ids id2 id1))
  [SMTPat (im.compose_ids i1 i2)]
//let symmetric_id_generation i1 i2 = ()

private let measure_id (im:index_module) (i:meta_id im) =
  match i with
  | SUBID i' -> 0
  | _ -> 1

val registered: (im:index_module) -> (i:meta_id im) -> Tot Type0 (decreases (measure_id im i))
let rec registered (im:index_module) (i:meta_id im) =
  match i with
  | SUBID i' -> MR.witnessed (MM.defined im.id_log i')
  | ID (i1,i2) -> registered im (SUBID i1) /\ registered im (SUBID i2)

// Put the correct flag here, as soon as we have flags for proof steps
val honest: (im:index_module) -> (i:meta_id im) -> Tot (t:Type0{t ==> registered im i}) (decreases (measure_id im i))
let rec honest (im:index_module) (i:meta_id im) =
  match i with
  | SUBID i' -> MR.witnessed (MM.contains im.id_log i' HONEST) /\ MR.witnessed (MM.defined im.id_log i')
  | ID (i1,i2) -> honest im (SUBID i1) /\ honest im (SUBID i2)

val dishonest: (im:index_module) -> (i:meta_id im) -> Tot (t:Type0{(t /\ SUBID? i) ==> registered im i}) (decreases (measure_id im i))
let rec dishonest im i =
  match i with
  | SUBID i' -> MR.witnessed (MM.contains im.id_log i' DISHONEST) /\ MR.witnessed (MM.defined im.id_log i')
  | ID (i1,i2) -> dishonest im (SUBID i1) \/ dishonest im (SUBID i2)

val undefined: (im:index_module) -> (i:meta_id im) -> Tot (t:Type0{(t /\ SUBID? i) ==> registered im i}) (decreases (measure_id im i))
let rec undefined im i =
  match i with
  | SUBID i' -> MR.witnessed (MM.contains im.id_log i' UNDEFINED) /\ MR.witnessed (MM.defined im.id_log i')
  | ID (i1,i2) -> (undefined im (SUBID i1) /\ honest im (SUBID i2))
                 \/ (honest im (SUBID i1) /\ undefined im (SUBID i2))
                 \/ (undefined im (SUBID i1) /\ undefined im (SUBID i2))


type absurd_honest (im:index_module) (i:meta_id im{registered im i /\ (undefined im i \/ dishonest im i)}) = honest im i
type absurd_dishonest (im:index_module) (i:meta_id im{registered im i /\ (undefined im i \/ honest im i)}) = dishonest im i
type absurd_undefined (im:index_module) (i:meta_id im{registered im i /\ (honest im i \/ dishonest im i)}) = undefined im i
assume val lemma_honest_and_others_tot: im:index_module -> i:meta_id im{registered im i /\ (undefined im i \/ dishonest im i)} -> absurd_honest im i -> Lemma (False)
assume val lemma_dishonest_and_others_tot: im:index_module -> i:meta_id im{registered im i /\ (undefined im i \/ honest im i)} -> absurd_dishonest im i -> Lemma (False)
assume val lemma_undefined_and_others_tot: im:index_module -> i:meta_id im{registered im i /\ (honest im i \/ dishonest im i)} -> absurd_undefined im i -> Lemma (False)


val lemma_dishonest_not_others: (im:index_module) -> (i:meta_id im) -> ST unit
  (requires (fun h0 ->
    registered im i
    /\ dishonest im i
  ))
  (ensures (fun h0 _ h1 ->
    ~(honest im i)
    /\ ~(undefined im i)
    /\ h0==h1
  ))
let lemma_dishonest_not_others im i =
  let (j:(i:meta_id im{registered im i /\ dishonest im i})) = i in
  FStar.Classical.impl_intro (lemma_honest_and_others_tot im j);
  FStar.Classical.impl_intro (lemma_undefined_and_others_tot im j);
  assert((honest im i \/ undefined im i)==> False)

val lemma_honest_not_others: (im:index_module) -> (i:meta_id im) -> ST unit
  (requires (fun h0 ->
    registered im i
    /\ honest im i
  ))
  (ensures (fun h0 _ h1 ->
    ~(dishonest im i)
    /\ ~(undefined im i)
    /\ h0==h1
  ))
let lemma_honest_not_others im i =
  let (j:(i:meta_id im{registered im i /\ honest im i})) = i in
  FStar.Classical.impl_intro (lemma_dishonest_and_others_tot im j);
  FStar.Classical.impl_intro (lemma_undefined_and_others_tot im j);
  assert((dishonest im i \/ undefined im i) ==> False)

val lemma_undefined_not_others: (im:index_module) -> (i:meta_id im) -> ST unit
  (requires (fun h0 ->
    registered im i
    /\ undefined im i
  ))
  (ensures (fun h0 _ h1 ->
    ~(dishonest im i)
    /\ ~(honest im i)
    /\ h0==h1
  ))
let lemma_undefined_not_others im i =
  let (j:(i:meta_id im{registered im i /\ undefined im i})) = i in
  FStar.Classical.impl_intro (lemma_dishonest_and_others_tot im j);
  FStar.Classical.impl_intro (lemma_honest_and_others_tot im j);
  assert((dishonest im i \/ honest im i) ==> False)

let merge_honesty_states h1 h2 =
  match h1,h2 with
  | HONEST,HONEST -> HONEST
  | _,DISHONEST -> DISHONEST
  | DISHONEST,_ -> DISHONEST
  | _,_ -> UNDEFINED

#set-options "--z3rlimit 500 --max_ifuel 2 --max_fuel 2"
val get_honesty: im:index_module -> i:meta_id im{registered im i} -> ST(h:honesty{(HONEST? h <==> (honest im i)) /\ (DISHONEST? h <==> dishonest im i) /\ (UNDEFINED? h <==> undefined im i)}) (decreases (measure_id im i))
  (requires (fun h0 -> True))
  (ensures (fun h0 b h1 ->
    modifies_none h0 h1
    /\ h0==h1
  ))
let rec get_honesty im i =
  MR.m_recall im.id_log;
  match i with
  | SUBID i' ->
    (MR.testify (MM.defined im.id_log i');
    match MM.lookup im.id_log i' with
    |Some h ->
      (match h with
      | HONEST ->
        lemma_honest_not_others im i;
        h
      | DISHONEST ->
        lemma_dishonest_not_others im i;
        h
      | UNDEFINED ->
        lemma_undefined_not_others im i;
        h))
  | ID (i1,i2) ->
    let h1 = get_honesty im (SUBID i1) in
    let h2 = get_honesty im (SUBID i2) in
    match merge_honesty_states h1 h2 with
    | HONEST ->
      lemma_honest_not_others im i;
      HONEST
    | DISHONEST ->
      lemma_dishonest_not_others im i;
      DISHONEST
    | UNDEFINED ->
      lemma_undefined_not_others im i;
      UNDEFINED
