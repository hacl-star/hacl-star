(**
  This module contains the plaintext type of AE and functions to access it.
*)
module Box.Plain

open FStar.Seq
open FStar.HyperHeap
open FStar.HyperStack
open FStar.HyperStack.ST

open Box.Flags
open Box.Index

(**
  The protected plaintext type of AE. It is associated with an id and acts as a wrapper around a protected pkae plaintext.
  The ids associated with both plaintexts must be equal.
*)

#set-options "--z3rlimit 300 --max_ifuel 1 --max_fuel 0"
abstract noeq type plain_module =
  | PM:
    plain: Type0 ->
    //repr: ((#i:id im) -> (protected_plain_t i) -> (p:plain_type{dishonest im (ID i) \/ not ae_ind_cpa})) ->
    //coerce: (#i:id im -> plain_type -> (p:protected_plain_t i{dishonest im (ID i) \/ not ae_int_ctxt})) ->
    valid_length: (nat -> bool)->
    length: (plain -> n:nat{valid_length n}) ->
    plain_module

val create: plain:Type0 -> valid_length:(nat -> bool)-> length:(plain -> n:nat{valid_length n}) -> p:plain_module{p.plain==plain /\ p.valid_length == valid_length /\ p.length==length}
let create plain valid_length length =
  PM plain valid_length length

abstract type protected_plain_t (im:index_module) (pt:Type0) (id:id im) = pt

val lemma_index_module: im:index_module -> i:id im -> ST unit
  (requires (fun h0 -> registered im i))
  (ensures (fun h0 _ h1 ->
    (honest im i ==> (~(dishonest im i)))
    /\ (dishonest im i ==> (~(honest im i)))
  ))

let lemma_index_module im i =
  lemma_index_module im i

val get_plain: pm:plain_module -> (t:Type0{t == pm.plain})
let get_plain pm =
  pm.plain

val reprGT: #im:index_module -> #pm:plain_module -> #i:id im -> protected_plain_t im pm.plain i -> (p:pm.plain)
let reprGT #im #pm #i p =
  p


val repr: #im:index_module -> #pm:plain_module -> #i:id im{dishonest im i \/ not ae_ind_cpa} -> protected_plain_t im pm.plain i -> (p:pm.plain)
let repr #im #pm #i p =
  p

val coerce: #im:index_module -> #pm:plain_module -> #i:id im{dishonest im i \/ not ae_int_ctxt} -> pm.plain -> (p:protected_plain_t im pm.plain i)
let coerce #im #pm #i p =
  p

val valid_length: #pm:plain_module -> n:nat -> b:bool//{b=pm.valid_length n}
let valid_length #pm n = pm.valid_length n

val lemma_valid_length: pm:plain_module -> Lemma (requires True) (ensures pm.valid_length == valid_length #pm)
let lemma_valid_length pm = 
  assert (FStar.FunctionalExtensionality.feq (pm.valid_length) (valid_length #pm));
  ()

val length: #im:index_module -> #pm:plain_module -> #i:id im -> (p:protected_plain_t im pm.plain i) -> n:nat{n=pm.length p /\ pm.valid_length n}
let length #im #pm #i p =
  pm.length p

 val rec_repr: #im:index_module ->
              #inner_pm:plain_module ->
              #pm:plain_module ->
              #i:id im{dishonest im i \/ not ae_ind_cpa} ->
              p:protected_plain_t im pm.plain i{protected_plain_t im pm.plain i === protected_plain_t im inner_pm.plain i}
              -> Tot (inner_pm.plain)
let rec_repr #im #inner_pm #pm #i p =
  repr #im #inner_pm #i p

val message_wrap: #im:index_module -> #inner_pm:plain_module -> #pm:plain_module -> #i:id im -> p:inner_pm.plain{protected_plain_t im pm.plain i === protected_plain_t im inner_pm.plain i} -> protected_plain_t im pm.plain i
let message_wrap #im #inner_pm #pm #i p =
  p

val message_unwrap: #im:index_module -> #inner_pm:plain_module -> #pm:plain_module -> #i:id im -> p:pm.plain{protected_plain_t im pm.plain i === protected_plain_t im inner_pm.plain i} -> protected_plain_t im inner_pm.plain i
let message_unwrap #im #inner_pm #pm #i p =
  p
