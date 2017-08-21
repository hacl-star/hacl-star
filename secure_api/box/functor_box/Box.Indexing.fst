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


type id_log_region = (r:MR.rid{extends r root /\ is_eternal_region r /\ is_below r root})

type id_log_value = bool
let id_log_range = fun id_log_key -> id_log_value
let id_log_inv (id_log_kt:Type0) (m:MM.map' id_log_kt id_log_range) = True

type id_log_t (rgn:id_log_region) (id_log_kt:Type0) = MM.t rgn id_log_kt id_log_range (id_log_inv id_log_kt)


abstract noeq type index_module =
  | IM:
    rgn: (id_log_region) ->
    subId: (t:Type0{hasEq t}) -> // express that there is a total order on ids
    smaller: (i1:subId -> i2:subId -> t:Type0{t ==> i1 <> i2}) ->
    total_order_lemma: (i1:subId -> i2:subId -> Lemma
      (requires smaller i1 i2)
      (ensures forall i. i <> i1 /\ i <> i2 /\ smaller i i1 ==> smaller i i2)
      [SMTPat (smaller i1 i2)]) ->
    compose_ids: (i1:subId -> i2:subId -> i:(subId*subId){smaller (fst i) (snd i) /\ (i = (i1,i2) \/ i = (i2,i1))}) ->
    symmetric_id_generation: (i1:subId -> i2:subId -> Lemma
    (requires (i1<>i2))
    (ensures (forall id1 id2. compose_ids id1 id2 = compose_ids id2 id1))
    [SMTPat (compose_ids i1 i2)]) ->
    id_log: (id_log_t rgn subId) ->
    index_module

let create rgn subId smaller total_order_lemma compose_ids symmetric_id_generation id_log =
  IM rgn subId smaller total_order_lemma compose_ids symmetric_id_generation id_log

val get_rgn: im:index_module -> GTot id_log_region
let get_rgn im =
  im.rgn

val get_log: im:index_module -> GTot (id_log_t im.rgn im.subId)
let get_log im =
  im.id_log

val get_subId: im:index_module -> Type0
let get_subId im =
  im.subId

val recall_log: im:index_module -> ST unit
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 ->
    h0 == h1
    /\ MR.m_contains im.id_log h1
  ))
let recall_log im =
  MR.m_recall im.id_log

type id (im:index_module) = i:(im.subId*im.subId){im.smaller (fst i) (snd i)}

val compose_ids: im:index_module -> i1:im.subId -> i2:im.subId -> (i:id im)
let compose_ids im i1 i2 =
  im.compose_ids i1 i2


val symmetric_id_generation: im:index_module -> i1:im.subId -> i2:im.subId -> Lemma
(requires (i1<>i2))
(ensures (forall id1 id2. im.compose_ids id1 id2 = im.compose_ids id2 id1))
[SMTPat (compose_ids im i1 i2)]
let symmetric_id_generation im i1 i2 =
im.symmetric_id_generation i1 i2

noeq type meta_id (im:index_module) =
  | ID of id im
  | SUBID of im.subId

private let measure_id (im:index_module) (i:meta_id im) =
  match i with
  | SUBID i' -> 0
  | _ -> 1

val registered: (im:index_module) -> (i:meta_id im) -> Tot Type0 (decreases (measure_id im i))
let rec registered (im:index_module) (i:meta_id im) =
  match i with
  | SUBID i' -> MR.witnessed (MM.defined im.id_log i')
  | ID (i1,i2) -> registered im (SUBID i1) /\ registered im (SUBID i2)

val lemma_registered: im:index_module -> i:id im -> Lemma
  (requires registered im (ID i))
  (ensures
    (let i1,i2 = i in
    registered im (SUBID (i2))
    /\ registered im (SUBID (i1))))
  [SMTPat (registered im (ID i))]
let lemma_registered im i =
  ()

val lemma_registered2: im:index_module -> i:id im -> Lemma
    (requires (let i1,i2 = i in
    registered im (SUBID (i2))
    /\ registered im (SUBID (i1))))
  (ensures registered im (ID i))
  [SMTPat (registered im (ID i))]
let lemma_registered2 im i =
  ()

// Put the correct flag here, as soon as we have flags for proof steps
val honest: (im:index_module) -> (i:meta_id im) -> Tot (t:Type0{t ==> registered im i}) (decreases (measure_id im i))
let rec honest (im:index_module) (i:meta_id im) =
  match i with
  | SUBID i' -> MR.witnessed (MM.contains im.id_log i' true) /\ MR.witnessed (MM.defined im.id_log i')
  | ID (i1,i2) -> honest im (SUBID i1) /\ honest im (SUBID i2)

val lemma_both_ids_honest: im:index_module -> i:id im -> Lemma
  (requires (honest im (ID i)))
  (ensures (
    (let i1,i2 = i in
    honest im (SUBID i1) /\ honest im (SUBID i2))
  ))
  [SMTPat (honest im (ID i))]
let lemma_both_ids_honest im i = ()

val lemma_single_id_honest: im:index_module -> i1:im.subId -> Lemma
  (requires (honest im (SUBID i1)))
  (ensures (
    (forall (i2:im.subId) .
      (honest im (SUBID i2)) ==> (let ID i = ID (im.compose_ids i1 i2) in honest im (ID i)))
  ))
  [SMTPat (honest im (SUBID i1))]
let lemma_single_id_honest im i1 = ()

val dishonest: (im:index_module) -> (i:meta_id im) -> Tot (t:Type0{(t /\ SUBID? i) ==> registered im i}) (decreases (measure_id im i))
let rec dishonest im i =
  match i with
  | SUBID i' -> MR.witnessed (MM.contains im.id_log i' false) /\ MR.witnessed (MM.defined im.id_log i')
  | ID (i1,i2) -> dishonest im (SUBID i1) \/ dishonest im (SUBID i2)

type absurd_honest (im:index_module) (i:meta_id im{dishonest im i}) = honest im i
type absurd_dishonest (im:index_module) (i:meta_id im{honest im i}) = dishonest im i
assume val lemma_honest_and_others_tot: im:index_module -> i:meta_id im{dishonest im i} -> absurd_honest im i -> Lemma (False)
assume val lemma_dishonest_and_others_tot: im:index_module -> i:meta_id im{honest im i} -> absurd_dishonest im i -> Lemma (False)


val lemma_dishonest_not_others: (im:index_module) -> (i:meta_id im) -> ST unit
  (requires (fun h0 ->
    dishonest im i
  ))
  (ensures (fun h0 _ h1 ->
    ~(honest im i)
    ///\ ~(undefined im i)
    /\ h0==h1
  ))
let lemma_dishonest_not_others im i =
  let (j:(i:meta_id im{dishonest im i})) = i in
  FStar.Classical.impl_intro (lemma_honest_and_others_tot im j);
  assert(honest im i==> False)

val lemma_honest_not_others: (im:index_module) -> (i:meta_id im) -> ST unit
  (requires (fun h0 ->
    honest im i
  ))
  (ensures (fun h0 _ h1 ->
    ~(dishonest im i)
    /\ h0==h1
  ))
let lemma_honest_not_others im i =
  let (j:(i:meta_id im{registered im i /\ honest im i})) = i in
  FStar.Classical.impl_intro (lemma_dishonest_and_others_tot im j);
  assert(dishonest im i ==> False)

val lemma_honest_or_dishonest: im:index_module -> (i:meta_id im) -> ST unit
  (requires (fun h0 ->
    registered im i
  ))
  (ensures (fun h0 _ h1 ->
    (honest im i \/ dishonest im i)
    /\ h0==h1
  ))
let rec lemma_honest_or_dishonest im i =
  MR.m_recall im.id_log;
  match i with
  | ID (i1,i2) -> lemma_honest_or_dishonest im (SUBID i1) ; lemma_honest_or_dishonest im (SUBID i2)
  | SUBID i' ->
    MR.testify (MM.defined im.id_log i');
    match MM.lookup im.id_log i' with
    | Some b ->
      if b then
  MR.testify (MM.contains im.id_log i' true)
             else
  MR.testify (MM.contains im.id_log i' false)

val fresh: im:index_module ->
           i:meta_id im ->
           h:mem ->
           (t:Type0{
             (t <==>
               ((ID? i ==>
                 (let ID (i1,i2) = i in
                 MM.fresh im.id_log i1 h
                 /\ MM.fresh im.id_log i2 h))
               /\ (SUBID? i ==>
                  (let SUBID i' = i in
                  MM.fresh im.id_log i' h
                  /\ ~(MM.contains im.id_log i' true h)))))
            /\ (~t /\ SUBID? i ==> (let SUBID i' = i in MM.defined im.id_log i' h))
           })

let fresh im i h =
  match i with
  | SUBID i' ->
    MM.fresh im.id_log i' h
  | ID i' ->
    MM.fresh im.id_log (fst i') h
    /\ MM.fresh im.id_log (snd i') h


val lemma_fresh: im:index_module -> i:id im -> h:mem -> Lemma
  (requires fresh im (ID i) h)
  (ensures
    (let i1,i2 = i in
    fresh im (SUBID i2) h
    /\ fresh im (SUBID i1) h))
  [SMTPat (fresh im (ID i) h)]
let lemma_fresh im i h =
  ()

val lemma_fresh2: im:index_module -> i:id im -> h:mem -> Lemma
    (requires (let i1,i2 = i in
    fresh im (SUBID i2) h
    /\ fresh im (SUBID i1) h))
    (ensures fresh im (ID i) h)
    [SMTPat (fresh im (ID i) h)]
let lemma_fresh2 im i h =
  ()

#set-options "--z3rlimit 900 --max_ifuel 1 --max_fuel 2"
val get_honesty: im:index_module -> i:meta_id im -> ST(b:bool) (decreases (measure_id im i))
  (requires (fun h0 ->
    registered im i
  ))
  (ensures (fun h0 b h1 ->
    modifies_none h0 h1
    /\ h0==h1
    /\ (b <==> (honest im i))
    /\ (~b <==> dishonest im i)
  ))
let rec get_honesty im i =
  MR.m_recall im.id_log;
  match i with
  | SUBID i' ->
    MR.testify (MM.defined im.id_log i');
    (match MM.lookup im.id_log i' with
    | Some b ->
      (match b with
      | true ->
        lemma_honest_not_others im (SUBID i');
        true
      | false ->
        lemma_dishonest_not_others im (SUBID i');
        false))
  | ID i' ->
    let b1 = get_honesty im (SUBID (fst i')) in
    let b2 = get_honesty im (SUBID (snd i')) in
    match b1 && b2 with
    | true ->
      lemma_honest_not_others im (ID i');
      true
    | false ->
      lemma_dishonest_not_others im (ID i');
      false


#set-options "--z3rlimit 2000 --max_ifuel 1 --max_fuel 1"
val set_honesty: im:index_module -> i:meta_id im -> b:bool -> ST unit
  (requires (fun h0 ->
    fresh im i h0
  ))
  (ensures (fun h0 _ h1 ->
    (b ==> honest im i)
    /\ (~b ==> dishonest im i)
    /\ (SUBID? i ==>
              (let SUBID i' = i in
              MR.m_sel h1 im.id_log == MM.upd (MR.m_sel h0 im.id_log) i' b
              /\ modifies (Set.singleton im.rgn) h0 h1
              ))
    /\ (ID? i ==>
           (let ID (i1,i2) = i in
           MR.m_sel h1 im.id_log == MM.upd (MM.upd (MR.m_sel h0 im.id_log) i1 b) i2 b /\ modifies (Set.singleton im.rgn) h0 h1))
  ))
let rec set_honesty im i b =
  match i with
    | SUBID i' ->
      (match MM.lookup im.id_log i' with
      | Some b -> ()
      | None ->
        MM.extend im.id_log i' b)
    | ID (i1,i2) ->
    set_honesty im (SUBID i1) b;
    set_honesty im (SUBID i2) b

val lemma_index_module: im:index_module -> i:meta_id im -> ST unit
  (requires (fun h0 -> registered im i))
  (ensures (fun h0 _ h1 ->
    (honest im i ==> (~(dishonest im i)))
    /\ (dishonest im i ==> (~(honest im i)))
  ))
let lemma_index_module im i =
  match get_honesty im i with
  | false ->
    ()
  | true ->
    ()
  

noeq type index_module' = 
  | SIM':
    rgn: (id_log_region) ->
    id_t: (t:eqtype) ->
    registered: (id_t -> Tot Type0) ->
    get_honesty: (id_t -> ST(bool) (requires (fun h0 -> True)) (ensures (fun h0 r h1 -> modifies (Set.singleton rgn) h0 h1))) ->
    // id_log_t: Type0 ->
    // id_log: id_log_t ->
    index_module'
    

val smaller_int: i1:int -> i2:int -> t:Type0{t ==> i1 <> i2}
let smaller_int i1 i2 = let b = i1 < i2 in b2t b

assume val total_order_lemma_int: (i1:int -> i2:int -> Lemma
  (requires i1 < i2)
  (ensures forall i. i <> i1 /\ i <> i2 /\ i < i1 ==> i < i2)
  [SMTPat (i1 < i2)])
   
assume val compose_int: i1:int -> i2:int -> i:(int*int){(fst i) < (snd i) /\ (i = (i1,i2) \/ i = (i2,i1))}

assume val symmetric_id_generation_int: i1:int -> i2:int -> Lemma
(requires (i1<>i2))
(ensures (compose_int i1 i2 = compose_int i2 i1))
[SMTPat (compose_int i1 i2)]

let create' rgn id_t =
  let id_log = MM.alloc #rgn #id_t #id_log_range #(id_log_inv id_t) in
  let im = create rgn int smaller_int total_order_lemma_int compose_int symmetric_id_generation_int id_log in
  SIM' rgn id_t (fun id -> registered im (SUBID id)) (fun id -> get_honesty im (SUBID id))

let compose' rgn (im1:index_module'{im1.rgn=rgn}) (im2:index_module'{im2.rgn=rgn}) =
  SIM' rgn (im1.id_t * im2.id_t) 
    (fun id -> im1.registered (fst id) /\ im2.registered (snd id))
    (fun id -> let (h1,h2) = (im1.get_honesty (fst id), im2.get_honesty (snd id)) in h1 && h2)
 
