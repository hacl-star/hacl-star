module Box.ODH

open FStar.Set
open FStar.HyperHeap
open FStar.HyperStack
open FStar.HyperStack.ST

open Box.Key

module ID = Box.Indexing

val dh_share: eqtype
val dh_exponent: eqtype

val smaller: i1:dh_share -> i2:dh_share -> b:bool{b ==> i1 <> i2}

val total_order_lemma: (i1:dh_share -> i2:dh_share -> Lemma
  (requires True)
  (ensures
    (b2t (smaller i1 i2) ==> (forall i. i <> i1 /\ i <> i2 /\ b2t (smaller i i1) ==> b2t (smaller i i2)))
    /\ (~ (b2t (smaller i1 i2)) <==> (i1 = i2 \/ b2t (smaller i2 i1)))))

val share_from_exponent: dh_exponent -> Tot dh_share

type index_module = im:ID.index_module{ID.get_subId im == dh_share}

val odh_module: im:index_module -> key_module im -> Type0

val create: im:index_module -> km:key_module im -> rgn:log_region im -> odh_module im km

(**
  A DH public key containing its raw byte representation. All ids of DH keys have to be unfresh and registered (e.g. marked as either honest
  or dishonest).
*)
val pkey: Type0


(**
  A DH secret key containing its raw byte representation. All ids of DH keys have to be unfresh and registered (e.g. marked as either honest
  or dishonest).
*)
val skey: Type0

val get_pkey: skey -> pkey

val compatible_keys: sk:skey -> pk:pkey -> t:Type0{t <==> pk =!= get_pkey sk}

(**
  A helper function to obtain the raw bytes of a DH public key.
*)
val pk_get_share: pk:pkey -> Tot (dh_sh:dh_share) //{dh_sh = pk.pk_share})

val lemma_pk_get_share_inj: pk:pkey -> Lemma
  (requires True)
  (ensures (forall pk' . pk_get_share pk' == pk_get_share pk <==> pk' == pk))
  [SMTPat (pk_get_share pk)]

val get_skeyGT: sk:skey -> GTot (raw:dh_exponent) //{raw=sk.sk_exp})

#set-options "--z3rlimit 300 --max_ifuel 1 --max_fuel 0"
(**
A helper function to obtain the share that corresponds to a DH secret key.
*)
val sk_get_share: sk:skey -> Tot (dh_sh:dh_share{dh_sh = share_from_exponent (get_skeyGT sk)})

val leak_skey: im:index_module -> sk:skey{ID.dishonest im (ID.SUBID (sk_get_share sk))} -> Tot (raw:dh_exponent{raw=get_skeyGT sk})

val keygen: unit -> ST (dh_pair:(pkey * skey){fst dh_pair == get_pkey (snd dh_pair)})
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))

val coerce_pkey: im:index_module -> dh_sh:dh_share{ID.dishonest im (ID.SUBID dh_sh)} -> Tot (pk:pkey{pk_get_share pk=dh_sh})

(**
  coerce_keypair allows the adversary to coerce a DH exponent into a DH private key. The corresponding DH public key
  is generated along with it. Both keys are considered dishonest and the id is considered unfresh after coercion.
*)
val coerce_keypair: im:index_module -> dh_exp:dh_exponent{ID.dishonest im (ID.SUBID (share_from_exponent dh_exp))} -> Tot (dh_pair:(k:pkey{pk_get_share k = share_from_exponent dh_exp}) * (k:skey{get_skeyGT k=dh_exp}))


(**
  GTot specification of the prf_odh function for use in type refinements.
*)
val prf_odhGT: im:index_module -> skey -> pkey -> GTot aes_key

val lemma_shares: sk:skey -> Lemma
  (requires True)
  (ensures (pk_get_share (get_pkey sk)) == sk_get_share sk)
  [ SMTPat (sk_get_share sk)]

val prf_odh: im:index_module -> km:key_module im -> om:odh_module im km  -> sk:skey -> pk:pkey{compatible_keys sk pk} -> ST (k:Key.get_keytype im km{Key.get_index im km k = (ID.compose_ids im (pk_get_share pk) (sk_get_share sk))} )
  (requires (fun h0 ->
    let i = ID.compose_ids im (pk_get_share pk) (sk_get_share sk) in
    ID.registered im (ID.ID i)
  ))
  (ensures (fun h0 k h1 ->
    let i = ID.compose_ids im (pk_get_share pk) (sk_get_share sk) in
    (ID.honest im (ID.ID i) ==> modifies (Set.singleton (Key.get_log_region im km)) h0 h1)
    // We should guarantee, that the key is randomly generated. Generally, calls to prf_odh should be idempotent. How to specify that?
    // Should we have a genPost condition that we guarantee here?
    /\ (ID.dishonest im (ID.ID i) ==>
                        (Key.leak im km k = prf_odhGT im sk pk // Functional correctness. Spec should be external in Spec.Cryptobox.
                        /\ h0 == h1))
    /\ (modifies (Set.singleton (Key.get_log_region im km)) h0 h1 \/ h0 == h1)
  ))
