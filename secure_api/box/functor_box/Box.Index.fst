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


type id_log_region = (r:MR.rid{extends r root /\ is_eternal_region r /\ is_below r root})

type id_log_value = bool
let id_log_range = fun id_log_key -> id_log_value
let id_log_inv (id_log_kt:Type0) (m:MM.map' id_log_kt id_log_range) = True

abstract type id_log_t (rgn:id_log_region) (id_log_kt:Type0) = MM.t rgn id_log_kt id_log_range (id_log_inv id_log_kt)

noeq type index_module = 
  | IM:
    rgn: id_log_region ->
    id: eqtype ->
    registered: (id -> Tot Type0) ->
    parent_honest: (id -> Tot Type0) ->
    honest:    (i:id -> Tot (t:Type0{t ==> registered i})) ->
    dishonest: (i:id -> Tot (t:Type0)) ->
    get_honesty: (i:id -> ST(bool)
      (requires (fun h0 -> registered i))
      (ensures  (fun h0 b h1 ->
          modifies_none h0 h1
        /\ h0==h1
        /\ (b <==> honest i)
        /\ (~b <==> dishonest i)))) ->
    fresh: (i:id -> h:mem -> Tot Type0) ->
    set_honesty: (i:id -> b:bool -> ST unit
      (requires (fun h0 -> fresh i h0 /\ (b ==> parent_honest i)))
      (ensures (fun h0 _ h1 ->
          (b ==> honest i)
        /\ (~b ==> dishonest i)))) ->
    id_log: (id_log_t rgn id) ->
    index_module

val recall_log: im:index_module -> ST unit
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 ->
    h0 == h1
    /\ MR.m_contains im.id_log h1
  ))
let recall_log im =
  MR.m_recall im.id_log

val registered: (#rgn:id_log_region) -> #id:eqtype -> id_log:(id_log_t rgn id) -> (i:id) -> Tot Type0
let registered #rgn #id id_log i =
  MR.witnessed (MM.defined id_log i)

// Put the correct flag here, as soon as we have flags for proof steps
val honest: (#rgn:id_log_region) -> #id:eqtype -> id_log:(id_log_t rgn id) -> (i:id) -> Tot (t:Type0 {t ==> registered id_log i}
  ) 
let honest #rgn #id id_log i =
  let _=() in MR.witnessed (MM.contains id_log i true) /\ MR.witnessed (MM.defined
  id_log i)


val dishonest: (#rgn:id_log_region) -> #id:eqtype -> id_log:(id_log_t rgn id) -> (i:id) -> Tot (t:Type0{t ==> registered id_log i}) 
let rec dishonest #rgn #id id_log i =
  let _=() in MR.witnessed (MM.contains id_log i false) /\ MR.witnessed (MM.defined id_log i)

type absurd_honest (#rgn:id_log_region) (#id:eqtype) (id_log:(id_log_t rgn id)) (i:id{dishonest id_log i}) = honest id_log i
type absurd_dishonest (#rgn:id_log_region) (#id:eqtype) (id_log:(id_log_t rgn id)) (i:id{honest id_log i}) = dishonest id_log i
assume val lemma_honest_and_others_tot: #rgn:id_log_region -> #id:eqtype -> id_log:(id_log_t rgn id) -> i:id{dishonest id_log i} -> absurd_honest id_log i -> Lemma (False)
assume val lemma_dishonest_and_others_tot: #rgn:id_log_region -> #id:eqtype -> id_log:(id_log_t rgn id) -> i:id{honest id_log i} -> absurd_dishonest id_log i -> Lemma (False)


val lemma_dishonest_not_others: #rgn:id_log_region -> #id:eqtype -> id_log: id_log_t rgn id -> (i:id) -> ST unit
  (requires (fun h0 ->
    dishonest id_log i
  ))
  (ensures (fun h0 _ h1 ->
    ~(honest id_log i)
    ///\ ~(undefined im i)
    /\ h0==h1
  ))
let lemma_dishonest_not_others #rgn #id id_log i =
  let (j:(i:id{dishonest id_log i})) = i in
  FStar.Classical.impl_intro (lemma_honest_and_others_tot id_log j);
  assert(honest id_log i==> False)

val lemma_honest_not_others: #rgn:id_log_region -> #id:eqtype -> id_log: id_log_t rgn id -> (i:id) -> ST unit
  (requires (fun h0 ->
    honest id_log i
  ))
  (ensures (fun h0 _ h1 ->
    ~(dishonest id_log i)
    /\ h0==h1
  ))
let lemma_honest_not_others #rgn #id id_log i =
  let (j:(i:id{registered id_log i /\ honest id_log i})) = i in
  FStar.Classical.impl_intro (lemma_dishonest_and_others_tot id_log j);
  assert(dishonest id_log i ==> False)

val lemma_honest_or_dishonest: im:index_module -> (i:im.id) -> ST unit
  (requires (fun h0 ->
    registered im.id_log i
  ))
  (ensures (fun h0 _ h1 ->
    (honest im.id_log i \/ dishonest im.id_log i)
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

val fresh: #rgn:id_log_region -> #id:eqtype -> id_log:(id_log_t rgn id) ->
           i:id ->
           h:mem ->
           (t:Type0{
             (t <==>
                  MM.fresh id_log i h
                  /\ ~(MM.contains id_log i true h))
            /\ (~t ==> (MM.defined id_log i h))
           })

let fresh #rgn #id id_log i h =
    MM.fresh id_log i h

#set-options "--z3rlimit 900 --max_ifuel 1 --max_fuel 2"
val get_honesty: #rgn:id_log_region -> #id:eqtype -> id_log: id_log_t rgn id -> i:id -> ST(b:bool)
  (requires (fun h0 ->
    registered id_log i
  ))
  (ensures (fun h0 b h1 ->
    modifies_none h0 h1
    /\ h0==h1
      /\ (b <==> (honest id_log i))
      /\ (~b <==> dishonest id_log i)
  ))


let rec get_honesty #rgn #id id_log i =
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


#set-options "--z3rlimit 2000 --max_ifuel 1 --max_fuel 1"
private val set_honesty: #rgn:id_log_region -> #id:eqtype -> id_log: id_log_t rgn id -> i:id -> b:bool -> ST unit
  (requires (fun h0 ->
    fresh id_log i h0
  ))
  (ensures (fun h0 _ h1 ->
      (b ==> honest id_log i)
    /\ (~b ==> dishonest id_log i)
    /\ (forall (i':id). ( i' =!= i /\ fresh id_log i' h0 ) ==> fresh id_log i' h1)
    /\ MR.m_sel h1 id_log == MM.upd (MR.m_sel h0 id_log) i b
              /\ modifies (Set.singleton rgn) h0 h1
  ))
let rec set_honesty #rgn #id id_log i b =
    (match MM.lookup id_log i with
    | Some b -> ()
    | None ->
        MM.extend id_log i b)

val lemma_index_module: im:index_module -> i:im.id -> ST unit
  (requires (fun h0 -> registered im.id_log i ))
  (ensures (fun h0 _ h1 ->
    (honest im.id_log i ==> (~(dishonest im.id_log i)))
    /\ (dishonest im.id_log i ==> (~(honest im.id_log i)))
  ))
let lemma_index_module im i =
  match get_honesty im.id_log i with
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

val create: rgn:id_log_region -> St index_module
let create rgn =
  let id_log:id_log_t rgn int = MM.alloc #rgn #int #id_log_range #(id_log_inv int) in
  // assert(False);
  IM rgn int
      (fun i -> registered id_log i)
      (fun i -> True)
      (fun i -> let b = honest id_log i in b)
      (fun i -> dishonest id_log i)
      (fun i -> get_honesty id_log i)
      (fun i h -> fresh id_log i h)
      (fun i b -> set_honesty id_log i b)
      id_log

val compose: rgn:id_log_region -> 
             im:index_module{im.rgn=rgn} ->
             smaller: (i1:im.id -> i2:im.id -> t:Type0{t ==> i1 <> i2}) ->
             St index_module
let compose rgn (im:index_module{im.rgn=rgn}) smaller =
  let fst = fst #im.id #im.id in
  let snd = snd #im.id #im.id in
  let id:eqtype = i:(im.id * im.id){smaller (fst i) (snd i)} in
  let id_log:id_log_t rgn id = MM.alloc #rgn #id #id_log_range #(id_log_inv id) in
  IM rgn 
      id
      (fun i -> registered id_log i)
      (fun i -> im.honest (fst i) /\ im.honest (snd i))
      (fun i -> honest id_log i) 
      (fun i -> dishonest id_log i) 
      (fun i -> get_honesty id_log i)
      (fun i h -> fresh id_log i h) 
      (fun i b -> set_honesty id_log i b)
      id_log 
 
