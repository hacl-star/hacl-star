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

let nonce = AE.nonce
let cipher = AE.cipher

let pkey = ODH.pkey
let skey = ODH.skey

let subId_t = ODH.dh_share
let plain_t = AE.ae_plain

#set-options "--z3rlimit 1900 --max_ifuel 2 --max_fuel 1"
private noeq type aux_t' (im:index_module{ID.get_subId im == subId_t}) (pm:plain_module) =
  | BP:
    am:AE.ae_module im pm ->
    km:Key.key_module im{km == AE.instantiate_km am} ->
    om:ODH.odh_module im km ->
    aux_t' im pm

let aux_t im pm = aux_t' im pm

let get_message_log pkm =
  pkm.message_log

type key (pkm:pkae_module) = AE.key pkm.im

let zero_bytes = AE.create_zero_bytes

let pkey_to_subId #pkm pk = ODH.pk_get_share pk
let pkey_to_subId_inj #pkm pk = ODH.lemma_pk_get_share_inj pk

let nonce_is_fresh (pkm:pkae_module) (i:id pkm.im) (n:nonce) (h:mem) =
  let _ = () in
  MR.m_contains pkm.message_log h
  /\ MM.fresh pkm.message_log (n,i) h

let pkey_from_skey sk = ODH.sk_get_pk sk

let gen pkm =
  ODH.keygen()

let compatible_keys sk pk = ODH.compatible_keys sk pk

#set-options "--z3rlimit 5000 --max_ifuel 1 --max_fuel 0"
//val encrypt: pkm:pkae_module -> #i:id pkm -> n:nonce -> sk:skey -> pk:pkey{ODH.compatible_keys sk pk /\ i = ID.compose_ids pkm.im (ODH.pk_get_share pk) (ODH.sk_get_share sk)} -> m:message pkm i{Plain.length #pkm.im #pkm.pm #i m / Spec.Salsa20.blocklen < pow2 32} -> ST cipher
//  (requires (fun h0 ->
//    registered pkm i
//    /\ nonce_is_fresh pkm i n h0
//    /\ Key.invariant pkm.im pkm.km h0
//  ))
//  (ensures  (fun h0 c h1 ->
//    Key.invariant pkm.im pkm.km h1
//  ))
//let encrypt pkm #i n sk pk m =
//  let h0 = get() in
//  let k = ODH.prf_odh pkm.im pkm.aux.km pkm.aux.om sk pk in
//  let h1 = get() in
//  AE.nonce_freshness_lemma #pkm.im #pkm.pm pkm.aux.am i n h0 h1;
//  let c = AE.encrypt pkm.aux.am #i n k m in
//  c
//
//val decrypt: pkm:pkae_module -> #i:id pkm -> n:nonce -> sk:skey -> pk:pkey{ODH.compatible_keys sk pk /\ i = ID.compose_ids pkm.im (ODH.pk_get_share pk) (ODH.sk_get_share sk)} -> c:cipher -> ST (option (message pkm i))
//  (requires (fun h0 ->
//    registered pkm i
//    /\ Key.invariant pkm.im pkm.km h0
//  ))
//  (ensures  (fun h0 c h1 ->
//    Key.invariant pkm.im pkm.km h1
//  ))
//let decrypt pkm #i n sk pk c =
//  let k = ODH.prf_odh pkm.im pkm.km pkm.om sk pk in
//  let m = AE.decrypt pkm.am #i n k c in
//  m
