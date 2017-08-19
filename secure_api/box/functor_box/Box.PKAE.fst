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

#set-options "--z3rlimit 1900 --max_ifuel 1 --max_fuel 0"
abstract noeq type pkae_module =
  | PKAE:
    im:ID.index_module{ID.get_subId im == ODH.dh_share} ->
    pm:Plain.plain_module{Plain.get_plain pm == AE.ae_plain} ->
    am:AE.ae_module im pm ->
    km:Key.key_module im{km == AE.instantiate_km am} ->
    om:ODH.odh_module im km ->
    pkae_module

type skey = ODH.skey
type pkey = ODH.pkey
type nonce = AE.nonce
type key (pkm:pkae_module) = AE.key pkm.im
type id (pkm:pkae_module) = ID.id pkm.im
type message (pkm:pkae_module) (i:id pkm) = AE.ae_protected_plain pkm.im pkm.pm i
type cipher = AE.cipher

val gen: pkm:pkae_module -> ST (pkey*skey)
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
let gen pkm =
  ODH.keygen()

let fresh pkm i = ID.fresh pkm.im (ID.ID i)
let registered pkm i = ID.registered pkm.im (ID.ID i)
let honest pkm i = ID.honest pkm.im (ID.ID i)
let dishonest pkm i = ID.dishonest pkm.im (ID.ID i)

#set-options "--z3rlimit 5000 --max_ifuel 2 --max_fuel 0"
val encrypt: pkm:pkae_module -> #i:id pkm -> n:nonce -> sk:skey -> pk:pkey{ODH.compatible_keys sk pk /\ i = ID.compose_ids pkm.im (ODH.pk_get_share pk) (ODH.sk_get_share sk)} -> m:message pkm i{Plain.length #pkm.im #pkm.pm #i m / Spec.Salsa20.blocklen < pow2 32} -> ST cipher
  (requires (fun h0 ->
    registered pkm i
    /\ AE.nonce_is_fresh pkm.am i n h0
    /\ Key.km_invariant pkm.im pkm.km h0
  ))
  (ensures  (fun h0 c h1 ->
    Key.km_invariant pkm.im pkm.km h1
  ))
let encrypt pkm #i n sk pk m =
  let h0 = get() in
  assert(Key.km_invariant pkm.im pkm.km h0);
  let k = ODH.prf_odh pkm.im pkm.km pkm.om sk pk in
  let h1 = get() in
  assert(Key.km_invariant pkm.im pkm.km h1);
  assert(Key.get_keytype pkm.im pkm.km == AE.key pkm.im);
  let c = AE.encrypt pkm.am #i n k m in
  c

//
//
//val decrypt: pkm:pkae_module -> #i:id pkm -> n:nonce -> k:key pkm -> c:cipher -> option (message pkm i)
