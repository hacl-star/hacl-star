(**
   This module contains functions and various lemmas concerning indices. Indices (ids)
   are used to link keys and plaintexts to a
   certain instance in the cryptographic model. This module also contains tables to
   reflect freshness and honesty of ids.
   TODO: Remove all state from this module.
   * move honesty information into the AE and DH module
   * use "registered" instead of fresh
   * remove unused lemmas
   * get rid of the assumes
*)
module Box.Index

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

noeq type index_module =
  | IM:
    im_rgn: id_log_region ->
    subId: eqtype -> 
    id_log: (id_log_t im_rgn subId) ->
    index_module

noeq type index_module' = 
  | IM':
    rgn: id_log_region ->
    id_t: eqtype ->
    registered: (id_t -> Tot Type0) ->
    honest:    (i:id_t -> Tot (t:Type0{t ==> registered i})) ->
    dishonest: (i:id_t -> Tot (t:Type0)) ->
    get_honesty: (i:id_t -> ST(bool)
      (requires (fun h0 -> registered i))
      (ensures  (fun h0 b h1 ->
          modifies_none h0 h1
        /\ h0==h1
        /\ (b <==> honest i)
        /\ (~b <==> dishonest i)))) ->
    fresh: (i:id_t -> h:mem -> Tot Type0) ->
    set_honesty: (i:id_t -> b:bool -> ST unit
      (requires (fun h0 -> fresh i h0))
      (ensures (fun h0 _ h1 ->
        True
        /\ (forall (i':id_t). ( i' =!= i /\ fresh i' h0 ) ==> fresh i' h1)
        /\ (b ==> honest i)
        /\ (~b ==> dishonest i)))) ->
    index_module'

let create rgn subId id_log =
  IM rgn subId id_log

val recall_log: im:index_module -> ST unit
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 ->
    h0 == h1
    /\ MR.m_contains im.id_log h1
  ))
let recall_log im =
  MR.m_recall im.id_log

val registered: (im:index_module) -> (i:im.subId) -> Tot Type0
let registered (im:index_module) (i:im.subId) =
  MR.witnessed (MM.defined im.id_log i)

// Put the correct flag here, as soon as we have flags for proof steps
val honest: (im:index_module) -> (i:im.subId) -> Tot (t:Type0 {t ==> registered im i}
  ) 
let honest (im:index_module) (i:im.subId) =
  let _=() in MR.witnessed (MM.contains im.id_log i true) /\ MR.witnessed (MM.defined
  im.id_log i)


val dishonest: (im:index_module) -> (i:im.subId) -> Tot (t:Type0{t ==> registered im i}) 
let rec dishonest im i =
  let _=() in MR.witnessed (MM.contains im.id_log i false) /\ MR.witnessed (MM.defined im.id_log i)

type absurd_honest (im:index_module) (i:im.subId{dishonest im i}) = honest im i
type absurd_dishonest (im:index_module) (i:im.subId{honest im i}) = dishonest im i
assume val lemma_honest_and_others_tot: im:index_module -> i:im.subId{dishonest im i} -> absurd_honest im i -> Lemma (False)
assume val lemma_dishonest_and_others_tot: im:index_module -> i:im.subId{honest im i} -> absurd_dishonest im i -> Lemma (False)


val lemma_dishonest_not_others: (im:index_module) -> (i:im.subId) -> ST unit
  (requires (fun h0 ->
    dishonest im i
  ))
  (ensures (fun h0 _ h1 ->
    ~(honest im i)
    ///\ ~(undefined im i)
    /\ h0==h1
  ))
let lemma_dishonest_not_others im i =
  let (j:(i:im.subId{dishonest im i})) = i in
  FStar.Classical.impl_intro (lemma_honest_and_others_tot im j);
  assert(honest im i==> False)

val lemma_honest_not_others: (im:index_module) -> (i:im.subId) -> ST unit
  (requires (fun h0 ->
    honest im i
  ))
  (ensures (fun h0 _ h1 ->
    ~(dishonest im i)
    /\ h0==h1
  ))
let lemma_honest_not_others im i =
  let (j:(i:im.subId{registered im i /\ honest im i})) = i in
  FStar.Classical.impl_intro (lemma_dishonest_and_others_tot im j);
  assert(dishonest im i ==> False)

val lemma_honest_or_dishonest: im:index_module -> (i:im.subId) -> ST unit
  (requires (fun h0 ->
    registered im i
  ))
  (ensures (fun h0 _ h1 ->
    (honest im i \/ dishonest im i)
    /\ h0==h1
  ))
let rec lemma_honest_or_dishonest im i =
  MR.m_recall im.id_log;
  MR.testify (MM.defined im.id_log i);
  match MM.lookup im.id_log i with
  | Some b ->
    if b then
      MR.testify (MM.contains im.id_log i true)
    else
      MR.testify (MM.contains im.id_log i false)

 val fresh: im:index_module ->
           i:im.subId ->
           h:mem ->
           (t:Type0{
             (t <==>
                  MM.fresh im.id_log i h
                  /\ ~(MM.contains im.id_log i true h))
            /\ (~t ==> (MM.defined im.id_log i h))
           })

let fresh im i h =
    MM.fresh im.id_log i h

#set-options "--z3rlimit 900 --max_ifuel 1 --max_fuel 2"
val get_honesty: im:index_module -> i:im.subId -> ST(b:bool)
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
  MR.testify (MM.defined im.id_log i);
  (match MM.lookup im.id_log i with
  | Some b ->
    (match b with
    | true ->
      lemma_honest_not_others im i;
      true
    | false ->
      lemma_dishonest_not_others im i;
      false))


#set-options "--z3rlimit 2000 --max_ifuel 1 --max_fuel 1"
val set_honesty: im:index_module -> i:im.subId -> b:bool -> ST unit
  (requires (fun h0 ->
    fresh im i h0
  ))
  (ensures (fun h0 _ h1 ->
      (b ==> honest im i)
    /\ (~b ==> dishonest im i)
    /\ (forall (i':im.subId). ( i' =!= i /\ fresh im i' h0 ) ==> fresh im i' h1)
    /\ MR.m_sel h1 im.id_log == MM.upd (MR.m_sel h0 im.id_log) i b
              /\ modifies (Set.singleton im.im_rgn) h0 h1
  ))
let rec set_honesty im i b =
    (match MM.lookup im.id_log i with
    | Some b -> ()
    | None ->
        MM.extend im.id_log i b)

val lemma_index_module: im:index_module -> i:im.subId -> ST unit
  (requires (fun h0 -> registered im i ))
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

val smaller_int: i1:int -> i2:int -> t:Type0{t ==> i1 <> i2}
let smaller_int i1 i2 = let b = i1 < i2 in b2t b

val total_order_lemma_int: (i1:int -> i2:int -> Lemma
  (requires i1 < i2)
  (ensures forall i. i <> i1 /\ i <> i2 /\ i < i1 ==> i < i2)
  [SMTPat (i1 < i2)])
let total_order_lemma_int i1 i2 = ()

val compose_int: i1:int -> i2:int{i2 <> i1} -> i:(int*int){(fst i) < (snd i) /\ (i = (i1,i2) \/ i = (i2,i1))}
let compose_int i1 i2 =
  if i1 < i2 then (i1,i2) else (i2,i1)

val symmetric_id_generation_int: i1:int -> i2:int -> Lemma
(requires (i1<>i2))
(ensures (i1 <> i2 /\ compose_int i1 i2 = compose_int i2 i1))
[SMTPat (compose_int i1 i2)]
let symmetric_id_generation_int i1 i2 = ()

val create': rgn:id_log_region -> St index_module'
let create' rgn =
  let id_log:id_log_t rgn int = MM.alloc #rgn #int #id_log_range #(id_log_inv int) in
  let im = create rgn int id_log in
  // assert(False);
  IM' rgn int
      (fun i -> registered im i)
      (fun i -> let b = honest im i in b)
      (fun i -> dishonest im i)
      (fun i -> get_honesty im i)
      (fun i h -> fresh im i h)
      (fun i b -> set_honesty im i b)


val get_honesty': im:index_module' -> 
                  i:(im.id_t * im.id_t){fst i <> snd i} ->
                  ST(bool)
    (requires (fun h0 -> im.registered (fst i) /\ im.registered (snd i)))
    (ensures  (fun h0 b h1 ->
            modifies_none h0 h1
            /\ h0==h1
            /\ (b <==> im.honest (fst i) /\ im.honest (snd i))
  /\ (~b <==> im.dishonest (fst i) \/ im.dishonest (snd i)))) 
let get_honesty' im id =
  let (h1,h2) = (im.get_honesty (fst id), im.get_honesty (snd id)) in h1 && h2

val fresh': im:index_module' -> i:(im.id_t * im.id_t) -> h:mem -> Tot Type0
let fresh' im i h =
  let _ = () in
  im.fresh (fst i) h /\ im.fresh (snd i) h

val set_honesty': im:index_module' -> i:(im.id_t * im.id_t){fst i <> snd i} -> b:bool -> ST unit
  (requires (fun h0 ->
   im.fresh (fst i) h0 /\ im.fresh (snd i) h0
   ))
   (ensures (fun h0 _ h1 ->
   True
   /\ (forall (i':(im.id_t * im.id_t)). ( i' =!= i /\ im.fresh (fst i') h0 /\ im.fresh (snd i') h0 ) 
     ==> im.fresh(fst i') h1 /\ im.fresh (snd i') h1)
   /\ (b ==> im.honest (fst i) /\ im.honest (snd i))
   /\ (~b ==> im.dishonest (fst i) \/ im.dishonest (snd i)))) 
let set_honesty' im i b = im.set_honesty (fst i) b; admit(); im.set_honesty (snd i) b

val compose: rgn:id_log_region -> 
             im:index_module'{im.rgn=rgn} ->
             smaller: (i1:im.id_t -> i2:im.id_t -> t:Type0{t ==> i1 <> i2}) ->
             im':index_module'
let compose rgn (im:index_module'{im.rgn=rgn}) smaller=
  IM' rgn 
      (i:(im.id_t * im.id_t){smaller (fst i) (snd i)})
      (fun id -> im.registered (fst id) /\ im.registered (snd id))
      (fun id -> im.honest (fst id) /\ im.honest (snd id)) 
      (fun id -> im.dishonest (fst id) \/ im.dishonest (snd id)) 
      (fun id -> get_honesty' im id)
      (fun id h -> fresh' im id h) 
      (fun id b -> set_honesty' im id b)
