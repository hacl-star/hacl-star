module Box.Index

open FStar.HyperStack
open FStar.HyperStack.ST

open FStar.Endianness

module MM = FStar.Monotonic.Map
module Flags = Box.Flags

#set-options "--z3rlimit 300 --max_ifuel 2 --max_fuel 1"
let index_log_key (t:Type0{hasEq t}) = i:t
let index_log_value = bool
let index_log_range (#t:Type0{hasEq t}) (k:index_log_key t) = index_log_value
let index_log_inv (#t:Type0{hasEq t}) (f:MM.map' (index_log_key t) (index_log_range)) = True

let i_index_log (t:eqtype) (rgn:erid) = MM.t rgn (index_log_key t) (index_log_range) (index_log_inv)
let index_log (t:eqtype) (rgn:erid) =
  if Flags.model then
    i_index_log t rgn
  else
    unit

noeq
type index_package =
  | Leaf_IP:
    t:Type u#0{hasEq t} ->
    rgn : erid ->
    log: index_log t rgn ->
    index_package
  | Node_IP:
    children:list index_package{children =!= []} ->
    index_package

val id: ip:index_package -> t:Type u#0{hasEq t}
val unfold_id: l:list index_package{l =!= []} -> t:Type u#0{hasEq t}

let rec id ip =
  match ip with
  | Leaf_IP t _ _ -> t
  | Node_IP ips -> unfold_id ips
and unfold_id = function
  | [ip] -> id ip
  | hd :: tl -> id hd * unfold_id tl

#set-options "--z3rlimit 300 --max_ifuel 2 --max_fuel 2"
val compose_ips: (ip1:index_package) -> (ip2:index_package) -> ip:index_package{
  ip == Node_IP [ip1;ip2]
  /\ id ip == id ip1 * id ip2
  }
let compose_ips ip1 ip2 =
  let ip = Node_IP [ip1;ip2] in
  assert(unfold_id [ip1;ip2] == id ip1 * id ip2);
  assert(unfold_id [ip1;ip2] == id ip);
  ip

type logical_operator =
  | CONJ
  | DISJ

val apply_predicate: #ip:index_package -> i:id ip -> predicate:(#rgn:erid -> #t:eqtype -> i:t -> index_log t rgn -> Type0) -> op:logical_operator -> t:Type0
val all_apply_predicate: #ips:list index_package{Nil? ips = false} -> unfold_id ips -> (#rgn:erid -> #t:eqtype -> i:t -> index_log t rgn -> Type0) -> op:logical_operator -> Type0

let rec apply_predicate #ip x predicate op =
  match ip with
  | Leaf_IP t rgn log -> predicate #rgn #t x log
  | Node_IP childs -> all_apply_predicate #childs x predicate op
and all_apply_predicate #ips x predicate op =
  match ips with
  | [ip'] -> apply_predicate #ip' x predicate op
  | ip' :: tl ->
    let v, vs : id ip' * unfold_id tl = x in
    match op with
    | CONJ -> apply_predicate v predicate op /\ all_apply_predicate vs predicate op
    | DISJ -> apply_predicate v predicate op \/ all_apply_predicate vs predicate op


private let fresh_predicate =
  fun (h:mem)
    (#rgn:erid)
    (#t:eqtype)
    (i:t)
    (log:i_index_log t rgn) ->
    MM.fresh log i h
val fresh: #ip:index_package{Leaf_IP? ip} -> i:id ip -> h:mem -> Type0
let fresh #ip i h =
  if Flags.model then
    apply_predicate i (fresh_predicate h) CONJ
  else
    False

#set-options "--z3rlimit 300 --max_ifuel 4 --max_fuel 3"
private let registered_predicate =
  fun (#rgn:erid)
    (#t:eqtype)
    (i:t)
    (log:i_index_log t rgn) ->
    witnessed (MM.defined log i)
val registered: #ip:index_package -> i:id ip -> t:Type0{
  t /\ Flags.model /\ Leaf_IP? ip ==>
  (match ip with
  | Leaf_IP t rgn log ->
    (let log:i_index_log t rgn = log in
    witnessed (MM.defined log i)))
  }
let registered #ip i =
  if Flags.model then
    apply_predicate i registered_predicate CONJ
  else
    True

private let honest_predicate =
  fun (#rgn:erid)
    (#t:eqtype)
    (i:t)
    (log:i_index_log t rgn) ->
    witnessed (MM.contains log i true)
val honest: #ip:index_package -> i:id ip -> Type0
let honest #ip i =
  if Flags.model then
    apply_predicate i honest_predicate CONJ
  else
    True

private let corrupt_predicate =
  fun (#rgn:erid)
    (#t:eqtype)
    (i:t)
    (log:i_index_log t rgn) ->
    witnessed (MM.contains log i false)
val corrupt: #ip:index_package -> i:id ip -> Type0
let corrupt #ip i =
  if Flags.model then
    apply_predicate i corrupt_predicate DISJ
  else
    True

let create_leaf_index_package_footprint (rgn:erid) (t:eqtype) (ip:index_package{Leaf_IP? ip}) (h0:mem) (h1:mem) =
  match ip with
  | Leaf_IP t' rgn' log' ->
    t == t'
    /\ Flags.model ==>
      (let log: i_index_log t' rgn' = log' in
      (modifies (Set.singleton rgn) h0 h1
      /\ extends rgn' rgn
      /\ contains h1 log
      /\ (forall i . fresh #ip i h1)))

val create_leaf_index_package: rgn:erid -> t:eqtype -> ST (ip:index_package)
  (requires (fun h0 -> True))
  (ensures (fun h0 ip h1 ->
    Leaf_IP? ip
    /\ (match ip with
      | Leaf_IP t' rgn' log' ->
      t == t'
      /\ (if Flags.model then
          (let log: i_index_log t' rgn' = log' in
          (modifies (Set.singleton rgn) h0 h1
          /\ extends rgn' rgn
          /\ contains h1 log
          /\ (forall i . fresh #ip i h1)))
        else
          modifies_none h0 h1))
  ))
let create_leaf_index_package rgn t =
  let log_rgn = new_region rgn in
  let log =
    if Flags.model then
      MM.alloc #log_rgn #(index_log_key t) #(index_log_range #t) #index_log_inv
    else
      ()
  in
  Leaf_IP t log_rgn log

val create_node_index_package: l:list index_package{l =!= []} -> ST (ip:index_package{Node_IP? ip})
  (requires (fun h0 -> True))
  (ensures (fun h0 ip h1 ->
    h0 == h1
  ))
let create_node_index_package l =
  Node_IP l

val extend_id_log: (#ip:index_package{Leaf_IP? ip}) -> (i:id ip) -> (b:bool) -> (h0:mem) -> (h1:mem) -> Type0
let extend_id_log #ip i b h0 h1 =
  match ip with
  | Leaf_IP t rgn log ->
    Flags.model ==>
    (let log: i_index_log t rgn = log in
    witnessed (MM.defined log i)
    /\ witnessed (MM.contains log i b)
    /\ sel h1 log == MM.upd (sel h0 log) i b
    )

let register_footprint (ip:index_package{Leaf_IP? ip}) (h0:mem) (h1:mem) =
  match ip with
  | Leaf_IP t rgn log ->
    modifies (Set.singleton rgn) h0 h1

val register: #ip:index_package{Leaf_IP? ip} -> i:id ip -> b:bool -> ST unit
  (requires (fun h0 ->
    Flags.model /\ fresh i h0
  ))
  (ensures (fun h0 _ h1 ->
    extend_id_log i b h0 h1
    /\ (b ==> honest i)
    /\ (~b ==> corrupt i)
    /\ registered i
    /\ register_footprint ip h0 h1
  ))
let register #ip i b =
  match ip with
  | Leaf_IP t rgn log ->
    let log: i_index_log t rgn = log in
    MM.extend log i b;
    assert(b ==> apply_predicate i honest_predicate CONJ);
    assert(~b ==> apply_predicate i corrupt_predicate DISJ)

#set-options "--z3rlimit 300 --max_ifuel 1 --max_fuel 1"
val get_honesty: #ip:index_package -> i:id ip -> ST bool
  (requires (fun h0 ->
    registered i
  ))
  (ensures (fun h0 b h1 ->
    h0 == h1
    /\ ((b2t b) ==> honest i)
    /\ (~(b2t b) ==> corrupt i)
  ))
val all_get_honesty: #ips:list index_package{ips =!= []} -> i:unfold_id ips -> ST bool
  (requires (fun h0 ->
    Flags.model
    /\ all_apply_predicate #ips i registered_predicate CONJ
  ))
  (ensures (fun h0 b h1 ->
    h0 == h1
    /\ (b2t b ==> all_apply_predicate #ips i honest_predicate CONJ)
    /\ (~(b2t b) ==> all_apply_predicate #ips i corrupt_predicate DISJ)
  ))
let rec get_honesty #ip i =
  if Flags.model then
    begin
    match ip with
    | Leaf_IP t rgn log ->
      let log: i_index_log t rgn = log in
      testify (MM.defined log i);
      (match MM.lookup log i with
      | Some b -> (
        (if b then
          testify (MM.contains log i true)
        else
          testify (MM.contains log i false));
        assert(b2t b ==> apply_predicate i honest_predicate CONJ);
        assert(~(b2t b) ==> apply_predicate i corrupt_predicate DISJ);
        b))
    | Node_IP ips ->
      let b = all_get_honesty #ips i in
      assert(b2t b ==> all_apply_predicate #ips i honest_predicate CONJ);
      assert(~(b2t b) ==> all_apply_predicate #ips i corrupt_predicate DISJ);
      b
    end
  else
    false
and all_get_honesty #ips i =
  match ips with
  | [ip'] -> get_honesty #ip' i
  | ip' :: tl ->
    let v, vs : id ip' * unfold_id tl = i in
    let b1 = get_honesty #ip' v in
    assert(b2t b1 ==> apply_predicate #ip' v honest_predicate CONJ);
    assert(~(b2t b1) ==> apply_predicate #ip' v corrupt_predicate DISJ);
    let b2 = all_get_honesty #tl vs in
    assert(b2t b2 ==> all_apply_predicate #tl vs honest_predicate CONJ);
    assert(~(b2t b2) ==> all_apply_predicate #tl vs corrupt_predicate DISJ);
    b1 && b2


type absurd_honest (#ip:index_package) (i:id ip{corrupt i}) = honest i
type absurd_corrupt (#ip:index_package) (i:id ip{honest i}) = corrupt i
assume val lemma_honest_and_others_tot: #ip:index_package -> i:id ip{corrupt i} -> absurd_honest i -> Lemma (False)
assume val lemma_corrupt_and_others_tot: #ip:index_package -> i:id ip{honest i} -> absurd_corrupt i -> Lemma (False)


val lemma_corrupt_not_others: #ip:index_package -> (i:id ip) -> Lemma
  (requires (
    corrupt i
  ))
  (ensures (
    ~(honest i)
  ))
  [SMTPat (corrupt i)]
let lemma_corrupt_not_others #ip i =
  let (j:(i:id ip{corrupt i})) = i in
  FStar.Classical.impl_intro (lemma_honest_and_others_tot j);
  assert(honest i==> False)

val lemma_honest_not_others: #ip:index_package -> (i:id ip) -> Lemma
  (requires (
    honest i
  ))
  (ensures (
    ~(corrupt i)
  ))
  [SMTPat (honest i)]
let lemma_honest_not_others #ip i =
  let (j:(i:id ip{honest i})) = i in
  FStar.Classical.impl_intro (lemma_corrupt_and_others_tot j);
  assert(corrupt i ==> False)
