module Box.ODH

open FStar.Set
open FStar.HyperHeap
open FStar.HyperStack
open FStar.HyperStack.ST

open Box.Key
open Crypto.Symmetric.Bytes

module ID = Box.Index

val dh_share_length: nat
val dh_exponent_length: nat
let dh_share = lbytes dh_share_length
let dh_exponent = lbytes dh_exponent_length

val smaller: i1:dh_share -> i2:dh_share -> b:bool{b ==> i1 <> i2}

let key_id = i:(dh_share * dh_share){b2t (smaller (fst i) (snd i))}

val total_order_lemma: (i1:dh_share -> i2:dh_share -> Lemma
  (requires True)
  (ensures
    (b2t (smaller i1 i2) ==> (forall i. i <> i1 /\ i <> i2 /\ b2t (smaller i i1) ==> b2t (smaller i i2)))
    /\ (~ (b2t (smaller i1 i2)) <==> (i1 = i2 \/ b2t (smaller i2 i1)))))

val share_from_exponent: dh_exponent -> Tot dh_share

type index_module = im:ID.index_module{ID.id im == dh_share}
type key_index_module = im:ID.index_module{ID.id im == key_id}
//type key_module (im:ID.index_module) = km:key_module im{Key.get_keylen im km = dh_share_length}

#set-options "--z3rlimit 300 --max_ifuel 1 --max_fuel 0"
val odh_module: im:index_module -> kim:key_index_module -> key_module kim -> Type0

val create: im:index_module -> kim:key_index_module -> km:key_module kim -> rgn:log_region im -> odh_module im kim km

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
val pk_get_share: pk:pkey -> Tot (dh_sh:dh_share) //{dh_sh = pk.pk_sharite numbersre})

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

val leak_skey: im:index_module -> sk:skey{ID.dishonest im (sk_get_share sk)} -> Tot (raw:dh_exponent{raw=get_skeyGT sk})

val keygen: unit -> ST (dh_pair:(pkey * skey){fst dh_pair == get_pkey (snd dh_pair)})
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))

val coerce_pkey: im:index_module -> dh_sh:dh_share{ID.dishonest im dh_sh} -> Tot (pk:pkey{pk_get_share pk=dh_sh})

(**
  coerce_keypair allows the adversary to coerce a DH exponent into a DH private key. The corresponding DH public key
  is generated along with it. Both keys are considered dishonest and the id is considered unfresh after coercion.
*)
val coerce_keypair: im:index_module -> dh_exp:dh_exponent{ID.dishonest im (share_from_exponent dh_exp)} -> Tot (dh_pair:(k:pkey{pk_get_share k = share_from_exponent dh_exp}) * (k:skey{get_skeyGT k=dh_exp}))


val compose_ids: s1:dh_share -> s2:dh_share{s2 <> s1} -> (i:(dh_share * dh_share){b2t (smaller (fst i) (snd i))})

(**
  GTot specification of the prf_odh function for use in type refinements.
*)
val prf_odhGT: sk:skey -> pk:pkey{compatible_keys sk pk} -> GTot (lbytes 32)

val lemma_shares: sk:skey -> Lemma
  (requires True)
  (ensures (pk_get_share (get_pkey sk)) == sk_get_share sk)
  [ SMTPat (sk_get_share sk)]
 

