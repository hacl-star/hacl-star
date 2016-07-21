module HMAC.Ideal.WIP

open FStar.Heap
//open FStar.HyperHeap
open FStar.Seq
open FStar.SeqProperties
open FStar.BaseTypes
open FStar.List.Tot



(* Define base types *)
new type u32 = FStar.UInt32.t
new type sbytes = Seq.seq FStar.UInt8.t

// abstract new type id = nat
abstract new type data = sbytes
abstract new type sig = sbytes
abstract new type tag = sbytes
abstract new type key = sbytes

(* Define security games available in that module *)
new type security_game =
  | UF_CMA
  | SUF_CMA


(* Concrete generation of the tag from hash agnostic hmac function *)
assume val mac: (k:key) -> (d:data) -> Tot (tag)
//let mac (k:key) (d:data) : Tot tag = HMAC.Pure.hmac_core k d

(* Concrete verification of the tag *)
let macverify (k:key) (d:data) (t:tag) : Tot bool = (Seq.eq (mac k d) t)


(* Define an abstract key property for assess authentication *)
assume new unfoldable type key_property : key -> data -> Type
type pkey (p:(data -> Type)) = k:key{key_property k == p}

(* Abstract leakage function for keys *)
assume val leaked: k:key -> Tot (b:bool{ b ==> (forall d. key_property k d)})


(* Abstract representation of a log element *)
noeq type logelt = | Logelt: (k:key) -> (d:data) -> (t:tag) -> logelt
new type glog = Seq.seq logelt

(* Create the global log *)
let log = Seq.createEmpty #logelt


(* Matching function for Perfect Unforgeability under Chosen Message Attack security game *)
val fails_UF_CMA: k:key -> d:data -> t:tag -> logelt -> Tot bool
let fails_UF_CMA k d t (Logelt k' d' _) = Seq.eq k k' && Seq.eq d d'

(* Matching function for Perfect Strong Unforgeability under Chosen Message Attack security game *)
val fails_SUF_CMA: k:key -> d:data -> t:tag -> logelt -> Tot bool
let fails_SUF_CMA k d t (Logelt k' d' t') = Seq.eq k k' && Seq.eq d d' && Seq.eq t t'


(* Ideal mac oracle *)
let oracle_mac (k:key) (d:data) (log:glog) : Tot (t:tag * log:glog)=
  let t = mac k d in
  let log = snoc log (Logelt k d t) in
  t,log


(* Ideal verification oracle *)
let oracle_verify (g:security_game) (k:key) (d:data) (t:tag) (l:glog): Tot (b:bool{b ==> key_property k d}) =
  let game = 
    match g with
    | UF_CMA -> fails_UF_CMA
    | SUF_CMA -> fails_SUF_CMA
  in
  let lookup =
    match seq_find (game k d t) l with
    | Some _ -> true
    | _ -> leaked k
  in
  macverify k d t && lookup // BB. Has to be done properly
