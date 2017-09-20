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
module Plain = Box.Plain
module ID = Box.Index


val nonce': t:Type0{hasEq t}
val cipher': Type0
val sub_id': t:Type0{hasEq t}
val key_id': Type0
val plain': Type0

val valid_plain_length: nat -> bool
val valid_cipher_length: nat -> bool

type index_module = im:ID.index_module{ID.id im == sub_id'}
type plain_index_module = im:ID.index_module{ID.id im == key_id'}
type plain_module = Plain.plain_module

type log_region (pim:plain_index_module) =
  r:MR.rid{disjoint r (ID.get_rgn pim)}

val aux_t: skey:Type0 -> pkey:Type0 -> (im:index_module) -> (pim:plain_index_module) -> (pm:plain_module) -> rgn:log_region pim -> Type u#1

abstract noeq type pkae_module =
  | PKAE:
    nonce: (t:Type0{t == nonce'}) ->
    cipher: (t:Type0{t == cipher'}) ->
    sub_id: (t:Type0{t == sub_id'}) ->
    key_id: (t:Type0{t == key_id'}) ->
    plain: (t:Type0{t == plain'}) ->
    skey: (t:Type0) ->
    pkey: (t:Type0) ->
    pkey_from_skey: (sk:skey -> pk:pkey) ->
    compatible_keys: (sk:skey -> pk:pkey -> t:Type0{t <==> pk =!= pkey_from_skey sk}) ->
    im:ID.index_module{ID.id im == sub_id} ->
    pim:ID.index_module{ID.id pim == key_id} ->
    pm:Plain.plain_module{Plain.get_plain pm == plain /\ Plain.valid_length #pm == valid_plain_length} ->
    rgn:log_region pim ->
    enc: (plain -> n:nonce -> pk:pkey -> sk:skey{compatible_keys sk pk} -> GTot cipher) ->
    dec: (c:cipher -> n:nonce -> pk:pkey -> sk:skey -> GTot (option plain)) ->
    aux: (aux_t skey pkey im pim pm rgn) ->
    pkae_module



val compose_ids: pkae:pkae_module ->  s1:pkae.sub_id -> s2:pkae.sub_id{s2 <> s1} -> pkae.key_id

val length: pkae:pkae_module -> p:pkae.plain -> n:nat{valid_plain_length n}



type message_log_key (im:plain_index_module) = (nonce'*(i:ID.id im))
type message_log_value (im:plain_index_module) (i:ID.id im) = (cipher'*Plain.protected_plain_t im plain' i)
type message_log_range (im:plain_index_module) (k:message_log_key im) = (v:message_log_value im (snd k))
type message_log_inv (im:plain_index_module) (f:MM.map' (message_log_key im) (message_log_range im)) = True //t:Type0{t = True}
type message_log (im:plain_index_module) (rgn:log_region im) =
  MM.t rgn (message_log_key im) (message_log_range im) (message_log_inv im)


val get_message_log_region: pkm:pkae_module -> Tot (log_region pkm.pim)
val get_message_logGT: pkm:pkae_module -> Tot (message_log pkm.pim (get_message_log_region pkm)) //TODO: MK: would prefer this to be GTot

val create: rgn:(r:MR.rid{extends r root /\ is_eternal_region r /\ is_below r root}) -> St (pkae_module)

val zero_bytes: (n:nat{valid_plain_length n}) -> plain' //b:bytes{Seq.length b = n /\ b=Seq.create n (UInt8.uint_to_t 0)}
//TODO: MK this can be modelled better

val pkey_to_subId: #pkm:pkae_module -> pk:pkm.pkey -> ID.id pkm.im
val pkey_to_subId_inj: #pkm:pkae_module -> pk:pkm.pkey -> Lemma
  (requires True)
  (ensures (forall pk' . pkey_to_subId #pkm pk == pkey_to_subId #pkm pk' <==> pk == pk'))
  [SMTPat (pkey_to_subId #pkm pk)]

#set-options "--z3rlimit 2000 --max_ifuel 1 --max_fuel 0"
val nonce_is_fresh: (pkm:pkae_module) -> (i:ID.id pkm.pim) -> (n:nonce') -> (h:mem) ->
  (t:Type0{t <==>
    (MR.m_contains #(get_message_log_region pkm) (get_message_logGT pkm) h
      /\ MM.fresh #(get_message_log_region pkm)(get_message_logGT pkm) (n,i) h)})


//val pkey_from_skey_inj: sk:skey -> pk:pkey -> Lemma
//  (requires True)
//  (ensures (forall sk1 sk2 . pkey_from_skey sk1 == pkey_from_skey sk2 <==> sk1 == sk2))

val invariant: pkae_module -> mem -> Type0

val gen: pkm:pkae_module -> ST (keypair:(pkm.pkey*pkm.skey){fst keypair == pkm.pkey_from_skey (snd keypair)})
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 ->
    modifies_none h0 h1
  ))

let registered pkm i = ID.registered pkm.pim i
let honest pkm i = ID.honest pkm.pim i
let dishonest pkm i = ID.dishonest pkm.pim i

val encrypt: pkm:pkae_module ->
             n:pkm.nonce ->
             sk:pkm.skey ->
             pk:pkm.pkey{pkm.compatible_keys sk pk} ->
             m:(Plain.protected_plain_t pkm.pim (Plain.get_plain pkm.pm) (compose_ids pkm (pkey_to_subId #pkm pk) (pkey_to_subId #pkm (pkm.pkey_from_skey sk)))) ->
             ST pkm.cipher
  (requires (fun h0 ->
    let i = compose_ids pkm (pkey_to_subId #pkm pk) (pkey_to_subId #pkm (pkm.pkey_from_skey sk)) in
    registered pkm i
    /\ nonce_is_fresh pkm i n h0
    /\ invariant pkm h0
  ))
  (ensures  (fun h0 c h1 ->
    let i = compose_ids pkm (pkey_to_subId #pkm pk) (pkey_to_subId #pkm (pkm.pkey_from_skey sk)) in
    modifies (Set.singleton pkm.rgn) h0 h1 // stateful changes even if the id is dishonest.
    /\ ((honest pkm i /\ b2t pkae) // Ideal behaviour if the id is honest and the assumption holds
               ==> eq2 #pkm.cipher c (pkm.enc (zero_bytes (Plain.length #pkm.pim #pkm.pm #i m)) n pk sk))
    /\ ((dishonest pkm i \/ ~(b2t pkae)) // Concrete behaviour otherwise.
                  ==> eq2 #pkm.cipher c (pkm.enc (Plain.repr #pkm.pim #pkm.pm #i m) n pk sk))
    // The message is added to the log. This also guarantees nonce-uniqueness.
    /\ MR.m_contains #(get_message_log_region pkm)(get_message_logGT pkm) h1
    /\ MR.witnessed (MM.contains #(get_message_log_region pkm) (get_message_logGT pkm) (n,i) (c,m))
    /\ MR.m_sel #(get_message_log_region pkm) h1 (get_message_logGT pkm)== MM.upd (MR.m_sel #(get_message_log_region pkm) h0 (get_message_logGT pkm)) (n,i) (c,m)
    /\ invariant pkm h1
  ))

val decrypt: pkm:pkae_module ->
             n:pkm.nonce ->
             sk:pkm.skey ->
             pk:pkm.pkey{pkm.compatible_keys sk pk} ->
             c:pkm.cipher ->
             ST (option (Plain.protected_plain_t pkm.pim (Plain.get_plain pkm.pm) (compose_ids pkm (pkey_to_subId #pkm pk) (pkey_to_subId #pkm (pkm.pkey_from_skey sk)))))
  (requires (fun h0 ->
    let i = compose_ids pkm (pkey_to_subId #pkm pk) (pkey_to_subId #pkm (pkm.pkey_from_skey sk)) in
    registered pkm i
    /\ invariant pkm h0
  ))
  (ensures  (fun h0 p h1 ->
    let i = compose_ids pkm (pkey_to_subId #pkm pk) (pkey_to_subId #pkm (pkm.pkey_from_skey sk)) in
    h0 == h1
    /\ invariant pkm h1
    /\ ((~(b2t pkae_int_ctxt) \/ dishonest pkm i) ==> // Concrete behaviour of the id is dishonest or if the assumption doesn't hold.
        (let option_m = pkm.dec c n pk sk in // Functional correctness: we get a result iff the ciphertext is valid.
        (Some? option_m ==>
          Some? p /\ Some?.v p == Plain.coerce #pkm.pim #pkm.pm #i (Some?.v option_m))
        /\ (None? option_m ==>
            None? p)
      ))
    /\ (let log = get_message_logGT pkm in
      (b2t pkae_int_ctxt /\ honest pkm i) ==> // Ideal behaviour otherwise: We get a result iff something is in the log.
        (Some? p ==>
          (MM.defined log (n,i) h0 /\ (fst (MM.value log (n,i) h0) == c )
          /\ Some?.v p == snd (MM.value log (n,i) h0)))
      /\ (None? p ==>
          (MM.fresh log (n,i) h0 \/ c =!= fst (MM.value log (n,i) h0)))
    )
  ))
