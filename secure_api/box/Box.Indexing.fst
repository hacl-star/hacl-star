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
open FStar.Endianness

open Box.Flags

module MR = FStar.Monotonic.RRef
module MM = MonotoneMap
module Curve = Spec.Curve25519

let lbytes (l:nat) = b:Seq.seq UInt8.t {Seq.length b = l}

type dh_id = Curve.serialized_point // same as dh_share

#set-options "--z3rlimit 500 --max_ifuel 2 --max_fuel 1"
//val smaller_equal: b1:bytes -> b2:bytes{Seq.length b1 = Seq.length b2} -> Tot bool (decreases (Seq.length b1))
//let rec smaller_equal b1 b2 =
//  if Seq.length b1 = 0 then
//    false
//  else
//    if UInt8.v (head b1) <= UInt8.v (head b2) then
//      true
//    else
//      smaller_equal (tail b1) (tail b2)


val smaller_equal: i1:dh_id -> i2:dh_id{length i1 = length i2} -> Tot bool
let smaller_equal i1 i2 =
  let id1 = little_endian i1 in
  let id2 = little_endian i2 in
  id1 <= id2

(** This lemma is necessary to prove symmetric id generation *)
val nat_smaller_equal_anti_symmetric: i1:nat -> i2:nat -> Lemma
    (requires (True))
    (ensures (i1 <= i2 /\ i2 <= i1 ==> i1 = i2))
    let nat_smaller_equal_anti_symmetric i1 i2 = ()

(* This lemma is necessary to prove symmetric id generation *)
val smaller_equal_anti_symmetric: i1:dh_id -> i2:dh_id{length i1 = length i2}-> Lemma
  (requires (smaller_equal i1 i2 /\ smaller_equal i2 i1 ))
  (ensures (i1 = i2))
let smaller_equal_anti_symmetric i1 i2 =
  lemma_little_endian_inj i1 i2

val larger: i1:dh_id -> i2:dh_id{length i1 = length i2} -> Tot bool
let larger i1 i2 =
  let id1 = little_endian i1 in
  let id2 = little_endian i2 in
  id1 > id2

abstract type ae_id = (i:(dh_id*dh_id){smaller_equal (fst i) (snd i)})

type id =
  | DH_id of dh_id
  | AE_id of ae_id


val generate_ae_id: i1:id{DH_id? i1} -> i2:id{DH_id? i2} -> Tot (i3:id{AE_id? i3})
let generate_ae_id i1 i2 =
  match i1,i2 with
  | DH_id i1',DH_id i2' ->
    if smaller_equal i1' i2' then (
    assert((smaller_equal i1' i2'));
    AE_id (i1',i2')
    ) else (
    AE_id (i2',i1'))


val symmetric_id_generation: i1:id{DH_id? i1} -> i2:id{DH_id? i2} -> Lemma
  (requires (True))
  (ensures (generate_ae_id i1 i2 = generate_ae_id i2 i1))
  [SMTPat (generate_ae_id i1 i2)]
let symmetric_id_generation i1 i2 =
  match i1,i2 with
  | DH_id i1',DH_id i2' ->
    if smaller_equal i1' i2' && smaller_equal i2' i1' then (
      smaller_equal_anti_symmetric i1' i2';
      ()
    )
    else (
      ()
    )

let id_log_range = fun id -> unit
let id_log_inv = fun (_:MM.map' id id_log_range) -> True

val id_log_region: (r:MR.rid{extends r root /\ is_eternal_region r /\ is_below r root})
let id_log_region = new_region root

val id_log: MM.t id_log_region
  id           (*domain*)
  id_log_range (*range*)
  id_log_inv   (*invariant*)
let id_log = MM.alloc #id_log_region #id #id_log_range #id_log_inv


let id_honesty_log_range = fun dh_id -> b:bool{~prf_odh ==> b=false}
let id_honesty_log_inv = fun (_:MM.map' dh_id id_honesty_log_range) -> True

val id_honesty_log_region: (r:MR.rid{ extends r root /\ is_eternal_region r /\ is_below r root /\ disjoint r id_log_region})
let id_honesty_log_region =
    recall_region id_log_region;
    new_region root

val id_honesty_log: MM.t id_honesty_log_region
  dh_id                (*domain*)
  id_honesty_log_range (*range*)
  id_honesty_log_inv   (*invariant*)
let id_honesty_log = MM.alloc #id_honesty_log_region #dh_id #id_honesty_log_range #id_honesty_log_inv


let fresh (i:id) h =
  MM.fresh id_log i h

type unfresh (i:id) =
  MR.witnessed (MM.defined id_log i)

val fresh_unfresh_contradiction: i:id -> ST unit
  (requires (fun h0 ->
    unfresh i
  ))
  (ensures (fun h0 _ h1 ->
    ~(fresh i h1)
    /\ h0 == h1
  ))
let fresh_unfresh_contradiction i =
  MR.m_recall id_log;
  MR.testify (MM.defined id_log i);
  match MM.lookup id_log i with
  | Some () -> ()


val freshST: (i:id) -> ST unit
  (requires (fun h0 -> ~(unfresh i)))
  (ensures (fun h0 b h1 ->
    fresh i h1
  ))
let freshST i =
  MR.m_recall id_log;
  match MM.lookup id_log i with
  | None -> ()

val makes_unfresh_just: i:id -> h0:mem -> h1:mem -> Tot Type0
let makes_unfresh_just i h0 h1 =
  let current_table = MR.m_sel h0 id_log in
  (MM.fresh id_log i h0 ==> MR.m_sel h1 id_log == MM.upd current_table i ())
  /\ (MM.defined id_log i h0 ==> current_table == MR.m_sel h1 id_log)
  /\ unfresh i

val make_unfresh: (i:id) -> ST (unit)
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 ->
    modifies (Set.singleton id_log_region) h0 h1
    /\ makes_unfresh_just i h0 h1
  ))
let make_unfresh i =
  MR.m_recall id_log;
  match MM.lookup id_log i with
  | Some i' -> ()
  | None ->
    MM.extend id_log i ()

private let measure_id (i:id) =
  match i with
  | DH_id i' -> 0
  | _ -> 1

val registered: (i:id) -> Tot Type0 (decreases (measure_id i))
let rec registered (i:id) =
  match i with
  | DH_id i' -> MR.witnessed (MM.defined id_honesty_log i')
  | AE_id (i1,i2) -> registered (DH_id i1) /\ registered (DH_id i2)

val honest: (i:id) -> Tot (t:Type0{t ==> registered i}) (decreases (measure_id i))
let rec honest (i:id) =
  if prf_odh then
    match i with
    | DH_id i' -> MR.witnessed (MM.contains id_honesty_log i' true) /\ MR.witnessed (MM.defined id_honesty_log i')
    | AE_id (i1,i2) -> honest (DH_id i1) /\ honest (DH_id i2)
  else
    False

val state_lemma: i:id -> Lemma
  (requires True)
  (ensures (honest i ==> b2t state))
  [SMTPat (honest i)]
let state_lemma i = ()

val dishonest: (i:id) -> Tot (t:Type0{(t /\ DH_id? i) ==> registered i}) (decreases (measure_id i))
let rec dishonest (i:id) =
  match i with
  | DH_id i' -> MR.witnessed (MM.contains id_honesty_log i' false) /\ MR.witnessed (MM.defined id_honesty_log i')
  | AE_id (i1,i2) -> dishonest (DH_id i1) \/ dishonest (DH_id i2)

val lemma_honest_or_dishonest: (i:id) -> ST unit
  (requires (fun h0 ->
    registered i
  ))
  (ensures (fun h0 _ h1 ->
    (honest i \/ dishonest i)
    /\ h0==h1
  ))
let rec lemma_honest_or_dishonest i =
  MR.m_recall id_honesty_log;
  match i with
  | AE_id (i1,i2) -> lemma_honest_or_dishonest (DH_id i1) ; lemma_honest_or_dishonest (DH_id i2)
  | DH_id i' ->
    MR.testify (MM.defined id_honesty_log i');
    match MM.lookup id_honesty_log i' with
    | Some b ->
      if b then
  MR.testify (MM.contains id_honesty_log i' true)
      else
  MR.testify (MM.contains id_honesty_log i' false)


type absurd_honest (i:id{registered i /\ dishonest i}) = honest i
type absurd_dishonest (i:id{registered i /\ honest i}) = dishonest i
assume val lemma_honest_and_dishonest_tot: i:id{registered i /\ dishonest i} -> absurd_honest i -> Lemma (False)
assume val lemma_dishonest_and_honest_tot: i:id{registered i /\ honest i} -> absurd_dishonest i -> Lemma (False)


val lemma_dishonest_not_honest: (i:id) -> ST unit
  (requires (fun h0 ->
    registered i
    /\ dishonest i
  ))
  (ensures (fun h0 _ h1 ->
    ~(honest i)
    /\ h0==h1
  ))
let lemma_dishonest_not_honest i =
  let (j:(i:id{registered i /\ dishonest i})) = i in
  FStar.Classical.impl_intro (lemma_honest_and_dishonest_tot j);
  assert(honest i ==> False)

val lemma_honest_not_dishonest: (i:id) -> ST unit
  (requires (fun h0 ->
    registered i
    /\ honest i
  ))
  (ensures (fun h0 _ h1 ->
    ~(dishonest i)
    /\ h0==h1
  ))
let lemma_honest_not_dishonest i =
  let (j:(i:id{registered i /\ honest i})) = i in
  FStar.Classical.impl_intro (lemma_dishonest_and_honest_tot j);
  assert(dishonest i ==> False)

val is_honest: i:id{registered i} -> ST(b:bool{(b <==> (honest i)) /\ (not b <==> dishonest i)}) (decreases (measure_id i))
  (requires (fun h0 -> True))
  (ensures (fun h0 b h1 ->
    modifies_none h0 h1
    /\ h0==h1
    /\ (honest i \/ dishonest i)
  ))
let rec is_honest i =
  MR.m_recall id_honesty_log;
  match i with
  | DH_id i' -> (
    MR.testify (MM.defined id_honesty_log i');
    match MM.lookup id_honesty_log i' with
    |Some b ->
      if b then (
        lemma_honest_not_dishonest i;
        b
      ) else (
        lemma_dishonest_not_honest i;
        b
      )
      )
  | AE_id (i1,i2) ->
    let b1 = is_honest (DH_id i1) in
    let b2 = is_honest (DH_id i2) in
    let b  = b1 && b2 in
    if b then (
      lemma_honest_not_dishonest i;
      b
    ) else (
      lemma_dishonest_not_honest i;
      b
    )

val honest_dishonest_lemma: dh_i:dh_id -> ST(unit)
  (requires (fun h -> registered (DH_id dh_i)))
  (ensures (fun h0 _ h1 ->
    let i = DH_id dh_i in
    modifies_none h0 h1
    /\ ( dishonest i \/ honest i )
    /\ ( ~(honest i) ==> dishonest i )
    /\ ( ~(dishonest i) ==> honest i )
  ))
let honest_dishonest_lemma i =
  let h = get() in
  MR.testify (MM.defined id_honesty_log i);
  match MM.lookup id_honesty_log i with
  |Some v -> ()

val honest_dishonest_contradiction_lemma: i:dh_id -> ST(unit)
  (requires (fun h -> honest (DH_id i) /\ dishonest (DH_id i)))
  (ensures (fun h0 _ h1 -> False
  ))
let honest_dishonest_contradiction_lemma i =
  MR.testify(MM.contains id_honesty_log i true);
  MR.testify(MM.contains id_honesty_log i false)
