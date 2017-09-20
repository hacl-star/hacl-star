module Box.ODH

open FStar.Set
open FStar.HyperHeap
open FStar.HyperStack
open FStar.HyperStack.ST

open Crypto.Symmetric.Bytes

module ID = Box.Index
module HH = FStar.HyperHeap
module Key = Box.Key

val hash_length': nat
val dh_share_length': nat
val dh_exponent_length': nat
let dh_share' (dh_share_length:nat) = lbytes dh_share_length
let dh_exponent' (dh_exponent_length:nat) = lbytes dh_exponent_length
let hash_output' (hash_length:nat) = lbytes hash_length
val smaller' (dh_share_length:nat): i1:dh_share' dh_share_length -> i2:dh_share' dh_share_length -> b:bool{b ==> i1 <> i2}
let key_id' (dh_share_length:nat) = i:(dh_share' dh_share_length * dh_share' dh_share_length){b2t (smaller' dh_share_length (fst i) (snd i))}

abstract noeq type odh_module = // require subId type to be dh_share?
  | ODH:
    rgn:(r:HH.rid) ->
    hash_length:(n:nat{n = hash_length'}) ->
    dh_share_length:(n:nat{n = dh_share_length'}) ->
    dh_exponent_length:(n:nat{n = dh_exponent_length'}) ->
    im:ID.index_module{ID.id im == dh_share' dh_share_length} ->
    kim:ID.index_module{ID.id im == key_id' dh_share_length} ->
    km:Key.key_module kim{Key.get_keylen kim km = hash_length} ->
    odh_module

val get_hash_length: om:odh_module -> n:nat{n = om.hash_length}
val get_dh_share_length: om:odh_module -> n:nat{n = om.dh_share_length}
val get_dh_exponent_length: om:odh_module -> n:nat{n = om.dh_share_length}
val get_index_module: om:odh_module -> im:ID.index_module{im==om.im}
val get_key_index_module: om:odh_module -> kim:ID.index_module{kim==om.kim}
val get_key_module: om:odh_module -> km:Key.key_module om.kim{km==om.km}

let dh_share (om:odh_module) = dh_share' om.dh_share_length
let dh_exponent (om:odh_module) = dh_exponent' om.dh_exponent_length
let hash_output (om:odh_module) = hash_output' om.hash_length
let smaller (om:odh_module) = smaller' om.dh_share_length
let key_id (om:odh_module) = key_id' om.dh_share_length

val hash: om:odh_module -> dh_share om -> Tot (hash_output om)

val total_order_lemma: (om:odh_module -> i1:dh_share om -> i2:dh_share om -> Lemma
  (requires True)
  (ensures
    (b2t (smaller om i1 i2) ==> (forall i. i <> i1 /\ i <> i2 /\ b2t (smaller om i i1) ==> b2t (smaller om i i2)))
    /\ (~ (b2t (smaller om i1 i2)) <==> (i1 = i2 \/ b2t (smaller om i2 i1)))))

val share_from_exponent: om:odh_module -> dh_exponent om -> Tot (dh_share om)
val dh_exponentiate: om:odh_module -> dh_exponent om -> dh_share om -> Tot (dh_share om)


#set-options "--z3rlimit 300 --max_ifuel 1 --max_fuel 0"

val create: hash_len:nat{hash_len = hash_length'} -> dh_share_len:nat{dh_share_len = dh_share_length'} -> dh_exponent_len:nat{dh_exponent_len = dh_exponent_length'} -> im:ID.index_module{ID.id im == dh_share' dh_share_len} -> kim:ID.index_module{ID.id im == key_id' dh_share_len} -> km:Key.key_module kim{Key.get_keylen kim km = hash_len} -> rgn:Key.log_region im -> odh_module

(**
  A DH public key containing its raw byte representation. All ids of DH keys have to be unfresh and registered (e.g. marked as either honest
  or dishonest).
*)
val pkey: om:odh_module -> Type0


(**
  A DH secret key containing its raw byte representation. All ids of DH keys have to be unfresh and registered (e.g. marked as either honest
  or dishonest).
*)
val skey: om:odh_module -> Type0

val get_pkey: om:odh_module -> skey om -> pkey om

val compatible_keys: om:odh_module -> sk:skey om -> pk:pkey om -> t:Type0{t <==> pk =!= get_pkey om sk}

(**
  A helper function to obtain the raw bytes of a DH public key.
*)
val pk_get_share: om:odh_module -> pk:pkey om -> Tot (dh_sh:dh_share om) //{dh_sh = pk.pk_sharite numbersre})

val lemma_pk_get_share_inj: om:odh_module -> pk:pkey om -> Lemma
  (requires True)
  (ensures (forall pk' . pk_get_share om pk' == pk_get_share om pk <==> pk' == pk))
  [SMTPat (pk_get_share om pk)]

val get_skeyGT: om:odh_module -> sk:skey om -> GTot (raw:dh_exponent om) //{raw=sk.sk_exp})

#set-options "--z3rlimit 300 --max_ifuel 1 --max_fuel 0"
(**
A helper function to obtain the share that corresponds to a DH secret key.
*)
val sk_get_share: om:odh_module -> sk:skey om -> Tot (dh_sh:dh_share om{dh_sh = share_from_exponent om (get_skeyGT om sk)})

val leak_skey: om:odh_module -> sk:skey om{ID.dishonest om.im (sk_get_share om sk)} -> Tot (raw:dh_exponent om{raw=get_skeyGT om sk})

val keygen: om:odh_module -> ST (dh_pair:(pkey om * skey om){fst dh_pair == get_pkey om (snd dh_pair)})
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))

val coerce_pkey: om:odh_module -> dh_sh:dh_share om{ID.dishonest om.im dh_sh} -> Tot (pk:pkey om{pk_get_share om pk=dh_sh})

(**
  coerce_keypair allows the adversary to coerce a DH exponent into a DH private key. The corresponding DH public key
  is generated along with it. Both keys are considered dishonest and the id is considered unfresh after coercion.
*)
val coerce_keypair: om:odh_module -> dh_exp:dh_exponent om{ID.dishonest om.im (share_from_exponent om dh_exp)} -> Tot (dh_pair:(k:pkey om{pk_get_share om k = share_from_exponent om dh_exp}) * (k:skey om{get_skeyGT om k=dh_exp}))


val compose_ids: om:odh_module -> s1:dh_share om -> s2:dh_share om{s2 <> s1} -> (i:(dh_share om * dh_share om){b2t (smaller om (fst i) (snd i))})

(**
  GTot specification of the prf_odh function for use in type refinements.
*)
val prf_odhGT: om:odh_module -> sk:skey om -> pk:pkey om{compatible_keys om sk pk} -> GTot (ho:hash_output om{ho = hash om (dh_exponentiate om (get_skeyGT om sk) (pk_get_share om pk))})

val lemma_shares: om:odh_module -> sk:skey om -> Lemma
  (requires True)
  (ensures (pk_get_share om (get_pkey om sk)) == sk_get_share om sk)
  [ SMTPat (sk_get_share om sk)]

#set-options "--z3rlimit 1000 --max_ifuel 1 --max_fuel 0"
val prf_odh: om:odh_module -> sk:skey om -> pk:pkey om{compatible_keys om sk pk} -> ST (k:Key.get_keytype om.kim om.km)
  (requires (fun h0 ->
    let i = compose_ids om (pk_get_share om pk) (sk_get_share om sk) in
    ID.registered om.kim i
    /\ Key.invariant om.kim om.km h0
  ))
  (ensures (fun h0 k h1 ->
    let i = compose_ids om (pk_get_share om pk) (sk_get_share om sk) in True
    /\ Key.get_index om.kim om.km k = i
    /\ ((ID.honest om.kim i /\ Flags.prf_odh) ==>
        modifies (Set.singleton (Key.get_log_region om.kim om.km)) h0 h1)
    // We should guarantee, that the key is randomly generated. Generally, calls to prf_odh should be idempotent. How to specify that?
    // Should we have a genPost condition that we guarantee here?
    /\ ((ID.dishonest om.kim i \/ ~Flags.prf_odh) ==>
        (Key.get_rawGT om.kim om.km k = prf_odhGT om sk pk // Functional correctness.
        /\ h0 == h1))
    /\ Key.invariant om.kim om.km h1
  ))
