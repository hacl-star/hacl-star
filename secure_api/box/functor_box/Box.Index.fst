(**
   This module contains functions and various lemmas concerning indices. Indices (ids)
   are used to link keys and plaintexts to a
   certain instance in the cryptographic model. This module also contains tables to
   reflect freshness and honesty of ids.
   TODO: 
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


type id_log_region = (r:MR.rid{is_eternal_region r /\ is_below r root})

type id_log_value = bool
let id_log_range = fun id_log_key -> id_log_value
let id_log_inv (id_log_kt:Type0) (m:MM.map' id_log_kt id_log_range) = True

type id_log_t (rgn:id_log_region) (id_log_kt:Type0) = MM.t rgn id_log_kt id_log_range (id_log_inv id_log_kt)

abstract noeq type index_module = 
  | IM:
    rgn: id_log_region ->
    id: eqtype ->
    registered: (id -> Tot Type0) ->
    parent_honest: (id -> Tot Type0) ->
    honest:    (i:id -> Tot (t:Type0{t ==> registered i})) ->
    dishonest: (i:id -> Tot (t:Type0{t ==> registered i})) ->
    get_honest: (i:id -> ST(bool)
      (requires (fun h0 -> registered i))
      (ensures  (fun h0 b h1 ->
          modifies_none h0 h1
        /\ h0==h1
        /\ (b <==> honest i)
        /\ (~b <==> dishonest i)))) ->
    fresh: (i:id -> h:mem -> Tot Type0) ->
    lemma_registered_not_fresh: (i:id -> ST unit
      (requires fun h0 -> registered i)
      (ensures fun h0 _ h1 -> h0 == h1 /\ ~(fresh i h1))) ->
    lemma_honest_or_dishonest: (i:id -> ST unit
      (requires (fun h0 ->
        registered i
      )) 
      (ensures (fun h0 _ h1 ->
        (honest i \/ dishonest i)
        /\ h0==h1
      ))) ->    
    set_honest: (i:id -> b:bool -> ST unit
      (requires (fun h0 -> fresh i h0 /\ (b ==> parent_honest i)))
      (ensures (fun h0 _ h1 ->
          (b ==> honest i)
        /\ (~b ==> dishonest i)  
        /\ modifies (Set.singleton rgn) h0 h1)
      ))->
    // lemma_index_module: (i:id -> ST unit
    // (requires (fun h0 -> registered i ))
    // (ensures (fun h0 _ h1 ->
    //   (honest i ==> (~(dishonest i)))
    //   /\ (dishonest i ==> (~(honest i)))
    // ))) ->
    id_log: (id_log_t rgn id) ->
    index_module

let get_rgn im =
  im.rgn

val id: im:index_module -> t:eqtype{t==im.id}
let id im =
  im.id

val get_log: im:index_module -> id_log_t im.rgn (id im)
let get_log im = im.id_log
  
val recall_log: im:index_module -> ST unit
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 ->
    h0 == h1
    /\ (let id_log: (id_log_t im.rgn im.id) = im.id_log in MR.m_contains id_log h1)
  ))
let recall_log im =
  let id_log:FStar.Monotonic.RRef.m_rref (im.rgn)
    (MM.map (im.id) id_log_range (id_log_inv (im.id)))
    MM.grows = im.id_log in
  MR.m_recall im.id_log

private val registered_log: (#rgn:id_log_region) -> #id:eqtype -> id_log:(id_log_t rgn id) -> (i:id) -> Tot Type0
let registered_log #rgn #id id_log i =
  MR.witnessed (MM.defined id_log i)

val registered: im:index_module -> i:im.id -> Tot Type0
let registered im i = im.registered i

// Put the correct flag here, as soon as we have flags for proof steps
val honest_log: (#rgn:id_log_region) -> #id:eqtype -> id_log:(id_log_t rgn id) -> (i:id) -> Tot (t:Type0 {t ==> registered_log id_log i}
  ) 
let honest_log #rgn #id id_log i =
  let _=() in MR.witnessed (MM.contains id_log i true) /\ MR.witnessed (MM.defined
  id_log i)

val honest: im:index_module -> i:id im -> Tot (t:Type0 {t ==> registered im i})
let honest im i = im.honest i

val dishonest_log: (#rgn:id_log_region) -> #id:eqtype -> id_log:(id_log_t rgn id) -> (i:id) -> Tot (t:Type0{t ==> registered_log id_log i}) 
let rec dishonest_log #rgn #id id_log i =
  let _=() in MR.witnessed (MM.contains id_log i false) /\ MR.witnessed (MM.defined id_log i)

val dishonest: im:index_module -> i:id im -> Tot (t:Type0 {t ==> registered im i})
let dishonest im i = im.dishonest i

type absurd_honest (#rgn:id_log_region) (#id:eqtype) (id_log:(id_log_t rgn id)) (i:id{dishonest_log id_log i}) = honest_log id_log i
type absurd_dishonest (#rgn:id_log_region) (#id:eqtype) (id_log:(id_log_t rgn id)) (i:id{honest_log id_log i}) = dishonest_log id_log i
assume val lemma_honest_and_others_tot: #rgn:id_log_region -> #id:eqtype -> id_log:(id_log_t rgn id) -> i:id{dishonest_log id_log i} -> absurd_honest id_log i -> Lemma (False)
assume val lemma_dishonest_and_others_tot: #rgn:id_log_region -> #id:eqtype -> id_log:(id_log_t rgn id) -> i:id{honest_log id_log i} -> absurd_dishonest id_log i -> Lemma (False)


val lemma_dishonest_not_others: #rgn:id_log_region -> #id:eqtype -> id_log: id_log_t rgn id -> (i:id) -> ST unit
  (requires (fun h0 ->
    dishonest_log id_log i
  ))
  (ensures (fun h0 _ h1 ->
    ~(honest_log id_log i)
    ///\ ~(undefined im i)
    /\ h0==h1
  ))
let lemma_dishonest_not_others #rgn #id id_log i =
  let (j:(i:id{dishonest_log id_log i})) = i in
  FStar.Classical.impl_intro (lemma_honest_and_others_tot id_log j);
  assert(honest_log id_log i==> False)

val lemma_honest_not_others: #rgn:id_log_region -> #id:eqtype -> id_log: id_log_t rgn id -> (i:id) -> ST unit
  (requires (fun h0 ->
    honest_log id_log i
  ))
  (ensures (fun h0 _ h1 ->
    ~(dishonest_log id_log i)
    /\ h0==h1
  ))
let lemma_honest_not_others #rgn #id id_log i =
  let (j:(i:id{registered_log id_log i /\ honest_log id_log i})) = i in
  FStar.Classical.impl_intro (lemma_dishonest_and_others_tot id_log j);
  assert(dishonest_log id_log i ==> False)

  val lemma_honest_or_dishonest_log: #rgn:id_log_region -> #id:eqtype -> id_log: id_log_t rgn id -> i:id -> ST unit
  (requires (fun h0 ->
    registered_log id_log i
  ))
  (ensures (fun h0 _ h1 ->
    (honest_log id_log i \/ dishonest_log id_log i)
    /\ h0==h1
  ))
let rec lemma_honest_or_dishonest_log #rgn #id id_log i =
  MR.m_recall id_log;
  MR.testify (MM.defined id_log i);
  match MM.lookup id_log i with
  | Some b ->
    if b then
      MR.testify (MM.contains id_log i true)
    else
      MR.testify (MM.contains id_log i false)

val lemma_honest_or_dishonest: im:index_module -> (i:im.id) -> ST unit
  (requires (fun h0 ->
    registered im i
  ))
  (ensures (fun h0 _ h1 ->
    (honest im i \/ dishonest im i)
    /\ h0==h1
  ))
let lemma_honest_or_dishonest im i = 
  im.lemma_honest_or_dishonest i

private val fresh_log: #rgn:id_log_region -> #id:eqtype -> id_log:(id_log_t rgn id) ->
           i:id ->
           h:mem ->
           (t:Type0{
             (t <==>
                  MM.fresh id_log i h
                  /\ ~(MM.contains id_log i true h))
            /\ (~t ==> (MM.defined id_log i h))
           })

let fresh_log #rgn #id id_log i h =
    MM.fresh id_log i h

val fresh: im:index_module -> i:id im -> h:mem -> 
                           t:Type0
                           // {
                           // (t <==>
                           // MM.fresh im.id_log i h
                           // /\ ~(MM.contains im.id_log i true h))
                           // /\ (~t ==> (MM.defined im.id_log i h))
                           // }
let fresh im i h = im.fresh i h

val lemma_registered_not_fresh_log: #rgn:id_log_region -> #id:eqtype -> id_log:(id_log_t rgn id) -> i:id -> ST unit
(requires fun h0 -> registered_log id_log i)
(ensures fun h0 _ h1 -> h0 == h1 /\ ~(fresh_log id_log i h1))
let lemma_registered_not_fresh_log #rgn #id id_log i = 
  assert(registered_log id_log i); 
  let h = get() in
  MR.testify (MM.defined id_log i);
  assert(~(MM.fresh id_log i h));
  ()

val lemma_registered_not_fresh: im:index_module -> i:id im -> ST unit
                            (requires fun h0 -> registered im i)
                            (ensures fun h0 _ h1 -> h0 == h1 /\ ~(fresh im i h1))
let lemma_registered_not_fresh im i =
  im.lemma_registered_not_fresh i

#set-options "--z3rlimit 900 --max_ifuel 1 --max_fuel 2"
val get_honest_log: #rgn:id_log_region -> #id:eqtype -> id_log: id_log_t rgn id -> i:id -> ST(b:bool)
  (requires (fun h0 ->
    registered_log id_log i 
  ))
  (ensures (fun h0 b h1 ->
    modifies_none h0 h1
    /\ h0==h1
      /\ (b <==> (honest_log id_log i))
      /\ (~b <==> dishonest_log id_log i)
  ))


let get_honest_log #rgn #id id_log i =
  MR.m_recall id_log;
  MR.testify (MM.defined id_log i);
  (match MM.lookup id_log i with
  | Some b ->
    (match b with
    | true ->
      lemma_honest_not_others id_log i;
      true
    | false ->
      lemma_dishonest_not_others id_log i;
      false))

val get_honest: im:index_module -> i:id im -> ST(b:bool)
  (requires (fun h0 ->
    registered im i
  ))
  (ensures (fun h0 b h1 ->
    modifies_none h0 h1
    /\ h0==h1
      /\ (b <==> (honest im i))
      /\ (~b <==> dishonest im i)
  ))
let get_honest im i = im.get_honest i



#set-options "--z3rlimit 2000 --max_ifuel 1 --max_fuel 1"
private val set_honest_log: #rgn:id_log_region -> #id:eqtype -> id_log: id_log_t rgn id -> i:id -> b:bool -> ST unit
  (requires (fun h0 ->
    fresh_log id_log i h0   
  ))
  (ensures (fun h0 _ h1 ->
      (b ==> honest_log id_log i)
    /\ (~b ==> dishonest_log id_log i)
    /\ (forall (i':id). ( i' =!= i /\ fresh_log id_log i' h0 ) ==> fresh_log id_log i' h1)
    /\ MR.m_sel h1 id_log == MM.upd (MR.m_sel h0 id_log) i b
              /\ modifies (Set.singleton rgn) h0 h1
  ))
let set_honest_log #rgn #id id_log i b =
    (match MM.lookup id_log i with
    | Some b -> ()
    | None ->
        MM.extend id_log i b)


val set_honest: im:index_module -> i:id im -> b:bool -> ST unit
(requires (fun h0 ->
  fresh im i h0
))
(ensures (fun h0 _ h1 ->
         (b ==> honest im i)
         /\ (~b ==> dishonest im i)
         /\ (forall (i':id im). ( i' =!= i /\ fresh im i' h0 ) ==> fresh im i' h1)
         /\ MR.m_sel h1 im.id_log == MM.upd (MR.m_sel h0 im.id_log) i b
           /\ modifies (Set.singleton (get_rgn im)) h0 h1
))
let set_honest im i b =
  im.set_honest i b

val lemma_index_module: im:index_module -> i:im.id -> ST unit
  (requires (fun h0 -> registered im i ))
  (ensures (fun h0 _ h1 ->
    (honest im i ==> (~(dishonest im i)))
    /\ (dishonest im i ==> (~(honest im i)))
  ))
let lemma_index_module im i =
  match get_honest im i with
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

val create_int: rgn:id_log_region -> St index_module
let create_int rgn =
  let id_log:id_log_t rgn int = MM.alloc #rgn #int #id_log_range #(id_log_inv int) in
  // assert(False);
  IM rgn int
      (fun i -> registered_log id_log i)
      (fun i -> True)
      (fun i -> let b = honest_log id_log i in b)
      (fun i -> dishonest_log id_log i)
      (fun i -> get_honest_log id_log i)
      (fun i h -> fresh_log id_log i h)
      (fun i -> lemma_registered_not_fresh_log id_log i)
      (fun i -> lemma_honest_or_dishonest_log id_log i)
      (fun i b -> set_honest_log id_log i b)
      id_log

val create: rgn:id_log_region -> id_t:eqtype -> St (im:index_module{get_rgn im=rgn /\ id im ==id_t })
let create rgn id =
  let id_log:id_log_t rgn id = MM.alloc #rgn #id #id_log_range #(id_log_inv id) in
  // assert(False);
  IM rgn id 
     (fun i -> registered_log id_log i)
     (fun i -> True)
     (fun i -> let b = honest_log id_log i in b)
     (fun i -> dishonest_log id_log i)
     (fun i -> get_honest_log id_log i)
     (fun i h -> fresh_log id_log i h)
     (fun i -> lemma_registered_not_fresh_log id_log i)
     (fun i -> lemma_honest_or_dishonest_log id_log i)
     (fun i b -> set_honest_log id_log i b)
     id_log


#set-options "--print_effect_args  --print_full_names --print_implicits --print_universes"
val compose: rgn:id_log_region -> 
             im:index_module{im.rgn=rgn} ->
             smaller: (i1:im.id -> i2:im.id -> b:bool{b ==> i1 <> i2}) ->
             St (im':index_module{id im' == i:(id im * id im){b2t (smaller (fst i) (snd i))}})
let compose rgn (im:index_module{im.rgn=rgn}) smaller =
  let fst_imp = fst #im.id #im.id in
  let snd_imp = snd #im.id #im.id in
  let id_t:eqtype = i:(id im * id im){b2t (smaller (fst i) (snd i))} in
  let id_log:id_log_t rgn id_t = MM.alloc #rgn #id_t #id_log_range #(id_log_inv id_t) in
    let im':(im':index_module{id im' == i:(id im * id im){b2t (smaller (fst i) (snd i))}}) = IM rgn 
      id_t
      (fun i -> registered_log id_log i)
      (fun i -> im.honest (fst_imp i) /\ im.honest (snd_imp i))
      (fun i -> honest_log id_log i) 
      (fun i -> dishonest_log id_log i) 
      (fun i -> get_honest_log id_log i)
      (fun i h -> fresh_log id_log i h) 
      (fun i -> lemma_registered_not_fresh_log id_log i)
      (fun i -> lemma_honest_or_dishonest_log id_log i)
      (fun i b -> set_honest_log id_log i b)
      id_log in
  im'
 
