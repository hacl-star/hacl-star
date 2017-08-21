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

#set-options "--z3rlimit 1900 --max_ifuel 1 --max_fuel 0"
private noeq type box_pkae_module =
  | BP:
    pkm:pkae_module{ID.get_subId pkm.im == ODH.dh_share /\ Plain.get_plain pkm.pm == AE.ae_plain} ->
    am:AE.ae_module pkm.im pkm.pm ->
    km:Key.key_module pkm.im{km == AE.instantiate_km am} ->
    om:ODH.odh_module pkm.im km ->
    box_pkae_module

let get_message_log pkm =
  pkm.message_log

type key (pkm:pkae_module) = AE.key pkm.im

let zero_bytes = AE.create_zero_bytes

let nonce_is_fresh (pkm:pkae_module) (i:id pkm) (n:nonce) (h:mem) =
  MR.m_contains pkm.message_log h
  /\ MM.fresh pkm.message_log (n,i) h

val gen: pkm:pkae_module -> ST (pkey*skey)
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
let gen pkm =
  ODH.keygen()

let registered pkm i = ID.registered pkm.im (ID.ID i)
let honest pkm i = ID.honest pkm.im (ID.ID i)
let dishonest pkm i = ID.dishonest pkm.im (ID.ID i)

#set-options "--z3rlimit 5000 --max_ifuel 1 --max_fuel 0"
val encrypt: pkm:pkae_module -> #i:id pkm -> n:nonce -> sk:skey -> pk:pkey{ODH.compatible_keys sk pk /\ i = ID.compose_ids pkm.im (ODH.pk_get_share pk) (ODH.sk_get_share sk)} -> m:message pkm i{Plain.length #pkm.im #pkm.pm #i m / Spec.Salsa20.blocklen < pow2 32} -> ST cipher
  (requires (fun h0 ->
    registered pkm i
    /\ nonce_is_fresh pkm i n h0
    /\ Key.invariant pkm.im pkm.km h0
  ))
  (ensures  (fun h0 c h1 ->
    Key.invariant pkm.im pkm.km h1
  ))
let encrypt pkm #i n sk pk m =
  let h0 = get() in
  let k = ODH.prf_odh pkm.im pkm.km pkm.om sk pk in
  let h1 = get() in
  AE.nonce_freshness_lemma #pkm.im #pkm.pm pkm.am i n h0 h1;
  let c = AE.encrypt pkm.am #i n k m in
  c

val decrypt: pkm:pkae_module -> #i:id pkm -> n:nonce -> sk:skey -> pk:pkey{ODH.compatible_keys sk pk /\ i = ID.compose_ids pkm.im (ODH.pk_get_share pk) (ODH.sk_get_share sk)} -> c:cipher -> ST (option (message pkm i))
  (requires (fun h0 ->
    registered pkm i
    /\ Key.invariant pkm.im pkm.km h0
  ))
  (ensures  (fun h0 c h1 ->
    Key.invariant pkm.im pkm.km h1
  ))
let decrypt pkm #i n sk pk c =
  let k = ODH.prf_odh pkm.im pkm.km pkm.om sk pk in
  let m = AE.decrypt pkm.am #i n k c in
  m
