module Box.Indexing

open FStar.Set
open FStar.HyperHeap
open FStar.HyperStack
open FStar.Endianness

open Box.Flags

module MR = FStar.Monotonic.RRef
module MM = MonotoneMap
module Curve = Spec.Curve25519

let lbytes (l:nat) = b:Seq.seq UInt8.t {Seq.length b = l}

type dh_id = Curve.serialized_point // same as dh_share
abstract type ae_id = (i:(dh_id*dh_id){little_endian (fst i) <= little_endian (snd i)})

type id =
  | DH_id of dh_id
  | AE_id of ae_id

val generate_ae_id: i1:id{DH_id? i1} -> i2:id{DH_id? i2} -> Tot (i3:id{AE_id? i3})
let generate_ae_id i1 i2 =
  match i1,i2 with
  | DH_id i1',DH_id i2' ->
  if little_endian i1' <= little_endian i2' then
    AE_id (i1',i2')
  else
    AE_id (i2',i1')

#set-options "--z3rlimit 100"
//TODO: Fix this!
//val symmetric_id_generation: i1:id{AE_id? i1} -> i2:id{AE_id? i2} -> Lemma
//  (requires (True))
//  (ensures (forall id1 id2. generate_ae_id id1 id2 = generate_ae_id id2 id1))
//  [SMTPat (generate_ae_id i1 i2)]
//let symmetric_id_generation i1 i2 = ()

assume Index_hasEq: hasEq id
assume AE_Index_hasEq: hasEq ae_id

type id_log_key = id
type id_log_value = unit
type id_log_range = fun id_log_key -> id_log_value
let id_log_inv (f:MM.map' id_log_key id_log_range) = True

assume val id_log_region: (r:MR.rid{extends r root /\ is_eternal_region r /\ is_below r root})

assume val id_log: MM.t id_log_region id_log_key id_log_range id_log_inv


type id_honesty_log_key = dh_id
type id_honesty_log_value = b:bool{~prf_odh ==> b=false}
type id_honesty_log_range = fun id_honesty_log_key -> id_honesty_log_value
let id_honesty_log_inv (m:MM.map' id_honesty_log_key id_honesty_log_range) = True
       
assume val id_honesty_log_region: (r:MR.rid{ extends r root /\ is_eternal_region r /\ is_below r root /\ disjoint r id_log_region})

assume val id_honesty_log: MM.t id_honesty_log_region id_honesty_log_key id_honesty_log_range id_honesty_log_inv

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
