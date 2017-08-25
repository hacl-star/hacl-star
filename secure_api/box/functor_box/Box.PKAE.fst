(**
  This module represents the PKAE cryptographic security game expressed in terms of the underlying cryptobox construction.
*)
module Box.PKAE


open FStar.Set
open FStar.HyperHeap
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Monotonic.RRef
open FStar.Seq
open FStar.Monotonic.Seq
open FStar.List.Tot

open Crypto.Symmetric.Bytes

open Box.Flags

module MR = FStar.Monotonic.RRef
module MM = MonotoneMap
module HS = FStar.HyperStack
module HH = FStar.HyperHeap
module HSalsa = Spec.HSalsa20
module Curve = Spec.Curve25519
module SPEC = Spec.SecretBox
module Plain = Box.Plain
module Key = Box.Key
module ID = Box.Indexing
module ODH = Box.ODH
module AE = Box.AE
module LE = FStar.Endianness

let nonce = AE.nonce
let cipher = AE.cipher
let subId_t = ODH.dh_share
let plain_t = AE.ae_plain

//let message_log_range (im:index_module) = AE.message_log_range im
//let message_log_inv (im:index_module) (pm:plain_module) (f:MM.map' (message_log_key im) (message_log_range im pm)) = AE.message_log_inv im pm f

let pkey = ODH.pkey
let skey = ODH.skey

#set-options "--z3rlimit 1900 --max_ifuel 2 --max_fuel 1"
private noeq type aux_t' (im:index_module{ID.get_subId im == subId_t}) (pm:plain_module) (rgn:log_region im) =
  | AUX:
    am:AE.ae_module im ->
    km:Key.key_module im{km == AE.instantiate_km am} ->
    om:ODH.odh_module im km ->
    aux_t' im pm rgn

let aux_t im pm = aux_t' im pm



type efun2 (a:Type) (b:Type) (c:Type) = a -> b -> Tot c

type feq2 (#a:Type) (#b:Type) (#c:Type) (f:efun2 a b c) (g:efun2 a b c) =
(forall x. forall y. {:pattern (f x y) \/ (g x y)} f x y == g x y)

assume Extensionality2 : forall (a:Type) (b:Type) (c:Type) (f: efun2 a b c) (g: efun2 a b c).
{:pattern feq2 #a #b #c f g} feq2 #a #b #c f g <==> f==g


val coerce: t1:Type -> t2:Type{t1 == t2} -> x:t1 -> t2
let coerce t1 t2 x = x

#set-options "--z3rlimit 200 --max_ifuel 1 --max_fuel 0"
val message_log_lemma: im:index_module -> rgn:log_region im -> Lemma
  (requires True)
  (ensures message_log im rgn === AE.message_log im rgn)
let message_log_lemma im rgn =
  assert(FStar.FunctionalExtensionality.feq (message_log_value im) (AE.message_log_value im));
  assert(FStar.FunctionalExtensionality.feq (message_log_range im) (AE.message_log_range im));
  let inv = message_log_inv im in
  let map_t =MM.map' (message_log_key im) (message_log_range im) in
  let inv_t = map_t -> Type0 in
  let ae_inv = AE.message_log_inv im in
  let ae_inv:map_t -> Type0 = ae_inv in
  assert(FStar.FunctionalExtensionality.feq
    #map_t #Type
    inv ae_inv);
  assert(message_log im rgn == AE.message_log im rgn);
  ()


let get_message_log_region pkm = AE.get_message_log_region pkm.aux.am

let get_message_logGT pkm =
  let (ae_log:AE.message_log pkm.im (get_message_log_region pkm)) = AE.get_message_logGT #pkm.im pkm.aux.am in
  let (ae_rgn:log_region pkm.im) = AE.get_message_log_region pkm.aux.am in
  message_log_lemma pkm.im ae_rgn;
  let log:message_log pkm.im ae_rgn = coerce (AE.message_log pkm.im ae_rgn) (message_log pkm.im ae_rgn) ae_log in
  //admit()
  log


(* "Box.PKAE.message_log
    (PKAE?.im pkm)
    (Box.AE.get_message_log_region (AUX?.am (PKAE?.aux pkm)))"

"(ml:Box.AE.message_log
    (PKAE?.im pkm)
    (AM?.message_log_region (AUX?.am (PKAE?.aux pkm)))
    { ml == AM?.message_log (AUX?.am (PKAE?.aux pkm)) })"
*)
// "(ml:Box.AE.message_log (PKAE?.im pkm)
//  (AM?.message_log_region (AUX?.am (PKAE?.aux pkm)))
//  { ml == AM?.message_log (AUX?.am (PKAE?.aux pkm)) })"
//  effect "GTot"

//     "Box.PKAE.message_log (PKAE?.im pkm)
//  (PKAE?.rgn pkm)"
//  effect "GTot"

val create_aux: (im:index_module{ID.get_subId im == subId_t}) -> (pm:plain_module{Plain.get_plain pm == plain_t}) -> rgn:log_region im -> St (aux_t im pm rgn)
let create_aux im pm rgn =
  let am = AE.create im pm rgn in
  let km = AE.instantiate_km am in
  let om = ODH.create im km rgn in
  AUX am km om

let create rgn =
  let im = ID.create rgn subId_t  in
  ()

let get_message_log pkm =
  pkm.message_log

type key (pkm:pkae_module) = AE.key pkm.im

let zero_bytes = AE.create_zero_bytes

let pkey_to_subId #pkm pk = ODH.pk_get_share pk
let pkey_to_subId_inj #pkm pk = ODH.lemma_pk_get_share_inj pk

let nonce_is_fresh (pkm:pkae_module) (i:id pkm.im) (n:nonce) (h:mem) =
  AE.nonce_is_fresh pkm.aux.am i n h

let pkey_from_skey sk = ODH.get_pkey sk

let gen pkm =
  ODH.keygen()

let compatible_keys sk pk = ODH.compatible_keys sk pk



#set-options "--z3rlimit 100 --max_ifuel 0 --max_fuel 0"
let encrypt pkm #i n sk pk m =
  let k = ODH.prf_odh pkm.im pkm.aux.km pkm.aux.om sk pk in
  let c = AE.encrypt pkm.aux.am #i n k m in
  let h = get() in
  assert(FStar.FunctionalExtensionality.feq (message_log_range pkm.im) (AE.message_log_range pkm.im));
  MM.contains_eq_compat (pkm.message_log) (AE.get_message_logGT pkm.aux.am) (n,i) (c,m) h;
  MM.contains_stable pkm.message_log (n,i) (c,m);
  MR.witness pkm.message_log (MM.contains pkm.message_log (n,i) (c,m));
  c

//val decrypt: pkm:pkae_module -> #i:id pkm -> n:nonce -> sk:skey -> pk:pkey{ODH.compatible_keys sk pk /\ i = ID.compose_ids pkm.im (ODH.pk_get_share pk) (ODH.sk_get_share sk)} -> c:cipher -> ST (option (message pkm i))
//  (requires (fun h0 ->
//    registered pkm i
//    /\ Key.invariant pkm.im pkm.km h0
//  ))
//  (ensures  (fun h0 c h1 ->
//    Key.invariant pkm.im pkm.km h1
//  ))
let decrypt pkm #i n sk pk c =
  let k = ODH.prf_odh pkm.im pkm.km pkm.om sk pk in
  let m = AE.decrypt pkm.am #i n k c in
  m
