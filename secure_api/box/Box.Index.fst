module Box.Index

open FStar.HyperStack
open FStar.HyperStack.ST

open FStar.Endianness

module MM = FStar.Monotonic.Map

let id_length = 32

type pk = lbytes id_length
type id =
  | PK_id of pk
  | Instance_id of (id:(pk*pk))

let pk_id = i:id{PK_id? i}
let inst_id = i:id{Instance_id? i}

val compose_id: i1:pk_id -> i2:pk_id{i1 <> i2} -> i:inst_id
let compose_id i1 i2 =
  let i1,i2 =
    match i1,i2 with
    | PK_id i1,PK_id i2 -> i1,i2
  in
  let int_i1 = little_endian i1 in
  let int_i2 = little_endian i2 in
  if int_i1 < int_i2 then
    Instance_id (i1,i2)
  else
    Instance_id (i2,i1)

#set-options "--z3rlimit 300 --max_ifuel 1 --max_fuel 1"
val lemma_symmetric_id:  i1:pk_id -> i2:pk_id{i1 <> i2} -> Lemma
  (requires True)
  (ensures compose_id i1 i2 = compose_id i2 i1)
  [SMTPat (compose_id i1 i2)]
let lemma_symmetric_id i1 i2 =
  let i1,i2 =
    match i1,i2 with
    | PK_id i1,PK_id i2 -> i1,i2
  in
  lemma_little_endian_bij i1 i2


type index_log_key = i:pk_id
let index_log_value = bool
let index_log_range (k:index_log_key) = index_log_value
let index_log_inv (f:MM.map' (index_log_key) (index_log_range)) = True

let index_log (rgn:erid) =
  MM.t rgn (index_log_key) (index_log_range) (index_log_inv)

noeq type index_package (rgn:erid) =
  | IP:
  id_log_rgn : erid{extends id_log_rgn rgn} ->
  id_log: index_log id_log_rgn ->
  index_package rgn

val create_index_package: rgn:erid -> ST (index_package rgn)
  (requires (fun h0 -> True))
  (ensures (fun h0 ip h1 ->
    modifies (Set.singleton rgn) h0 h1
    /\ contains h1 ip.id_log
  ))
let create_index_package rgn =
  let log_rgn = new_region rgn in
  let log = MM.alloc #log_rgn #index_log_key #index_log_range #index_log_inv in
  IP log_rgn log

val fresh: #rgn:erid -> ip:index_package rgn -> i:pk_id -> h:mem -> Type0
let fresh #rgn ip i h =
  MM.fresh ip.id_log i h
  //match i with
  //| PK_id i' -> MM.fresh ip.id_log (PK_id i') h
  //| Instance_id i' -> MM.fresh ip.id_log (PK_id (fst i')) h \/ MM.fresh ip.id_log (PK_id (snd i')) h

val registered: #rgn:erid -> ip:index_package rgn -> i:id -> Type0
let registered #rgn ip i =
  match i with
  | PK_id i' -> witnessed (MM.defined ip.id_log (PK_id i'))
  | Instance_id i' -> witnessed (MM.defined ip.id_log (PK_id (fst i'))) /\ witnessed (MM.defined ip.id_log (PK_id (snd i')))

#set-options "--z3rlimit 300 --max_ifuel 2 --max_fuel 1"
val honest: #rgn:erid -> ip:index_package rgn -> i:id -> t:Type0//{t ==> PK_id? i ==> registered_pk ip i}
let honest #rgn ip i =
  match i with
  | PK_id i' ->
    witnessed (MM.contains ip.id_log (PK_id i') true)
  | Instance_id i' -> witnessed (MM.contains ip.id_log (PK_id (fst i')) true) /\ witnessed (MM.contains ip.id_log (PK_id (snd i')) true)

val dishonest: #rgn:erid -> ip:index_package rgn -> i:id -> Type0
let dishonest #rgn ip i =
  match i with
  | PK_id i' ->
    witnessed (MM.contains ip.id_log (PK_id i') false)
  | Instance_id i' -> witnessed (MM.contains ip.id_log (PK_id (fst i')) false) \/ witnessed (MM.contains ip.id_log (PK_id (snd i')) false)

let extend_id_log (#rgn:erid) (ip:index_package rgn) (i:pk_id) (b:bool) (h0:mem) (h1:mem) =
  (sel h1 ip.id_log == MM.upd (sel h0 ip.id_log) i b
  /\ witnessed (MM.defined ip.id_log i)
  /\ witnessed (MM.contains ip.id_log i b))


val register: #rgn:erid -> ip:index_package rgn -> i:pk_id -> b:bool -> ST unit
  (requires (fun h0 ->
    MM.fresh ip.id_log i h0
  ))
  (ensures (fun h0 _ h1 ->
    (b ==> honest ip i)
    /\ (~b ==> dishonest ip i)
    /\ extend_id_log ip i b h0 h1
  ))
let register #rgn ip i b =
  MM.extend ip.id_log i b


#set-options "--z3rlimit 300 --max_ifuel 3 --max_fuel 3"
val get_honesty: #rgn:erid -> ip:index_package rgn -> i:id -> ST bool
  (requires (fun h0 ->
    registered ip i
  ))
  (ensures (fun h0 b h1 ->
    h0 == h1
    /\ ((b2t b) ==> honest ip i)
    /\ (~(b2t b) ==> dishonest ip i)
    /\ (PK_id? i ==> MM.contains ip.id_log i b h0)
  ))
let rec get_honesty #rgn ip i =
  match i with
  | PK_id i' ->
    testify (MM.defined ip.id_log (PK_id i'));
    (match MM.lookup ip.id_log i with
    | Some b -> (
      (if b then
        testify (MM.contains ip.id_log i true)
      else
        testify (MM.contains ip.id_log i false));
      b))
  | Instance_id i' ->
    let b1 = get_honesty ip (PK_id (fst i')) in
    let b2 = get_honesty ip (PK_id (snd i')) in
    b1 && b2

type absurd_honest (#rgn:erid) (ip:index_package rgn) (i:id{dishonest ip i}) = honest ip i
type absurd_dishonest (#rgn:erid) (ip:index_package rgn) (i:id{honest ip i}) = dishonest ip i
assume val lemma_honest_and_others_tot: #rgn:erid -> ip:index_package rgn -> i:id{dishonest ip i} -> absurd_honest ip i -> Lemma (False)
assume val lemma_dishonest_and_others_tot: #rgn:erid -> ip:index_package rgn -> i:id{honest ip i} -> absurd_dishonest ip i -> Lemma (False)


val lemma_dishonest_not_others: #rgn:erid -> ip:index_package rgn -> (i:id) -> Lemma
  (requires (
    dishonest ip i
  ))
  (ensures (
    ~(honest ip i)
  ))
  [SMTPat (dishonest ip i)]
let lemma_dishonest_not_others #rgn ip i =
  let (j:(i:id{dishonest ip i})) = i in
  FStar.Classical.impl_intro (lemma_honest_and_others_tot ip j);
  assert(honest ip i==> False)

val lemma_honest_not_others: #rgn:erid -> ip:index_package rgn -> (i:id) -> Lemma
  (requires (
    honest ip i
  ))
  (ensures (
    ~(dishonest ip i)
  ))
  [SMTPat (honest ip i)]
let lemma_honest_not_others #rgn ip i =
  let (j:(i:id{honest ip i})) = i in
  FStar.Classical.impl_intro (lemma_dishonest_and_others_tot ip j);
  assert(dishonest ip i ==> False)


val lemma_honest_or_dishonest: #rgn:erid -> ip:index_package rgn -> (i:id) -> Lemma
  (requires (
    registered ip i
  ))
  (ensures (
    ~(dishonest ip i)
  ))
  [SMTPat (honest ip i)]
let lemma_honest_not_others #rgn ip i =
  let (j:(i:id{honest ip i})) = i in
  FStar.Classical.impl_intro (lemma_dishonest_and_others_tot ip j);
  assert(dishonest ip i ==> False)

//val lemma_honest_dishonest: #rgn:erid -> ip:index_package rgn -> i:id -> ST unit
//  (requires (fun h0 ->
//    ~(honest ip i) /\ registered ip i
//  ))
//  (ensures (fun h0 _ h1 ->
//    (dishonest ip i)
//  ))
//let rec lemma_honest_dishonest #rgn ip i =
//  match i with
//  | PK_id i' -> testify (MM.defined ip.id_log (PK_id i'));
//    (match MM.lookup ip.id_log i with
//    | Some b -> assert(b = false))
//  | Instance_id i' ->
//    lemma_honest_dishonest ip (PK_id (fst i'));
//    lemma_honest_dishonest ip (PK_id (snd i'))
