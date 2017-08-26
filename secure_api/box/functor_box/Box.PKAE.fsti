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
module ID = Box.Indexing


type index_module = ID.index_module
type plain_module = Plain.plain_module
let id (im:index_module) = ID.id im
val nonce: t:Type0{hasEq t}
val cipher: Type0
type log_region (im:index_module) =
  r:MR.rid{disjoint r (ID.get_rgn im)}

val subId_t: Type0
val plain_max_length: nat
val plain_t: Type0
val length: p:plain_t -> n:nat{n<plain_max_length}

type message_log_key (im:index_module) = (nonce*(i:id im))
type message_log_value (im:index_module) (i:id im) = (cipher*Plain.protected_plain_t im plain_t i)
type message_log_range (im:index_module) (k:message_log_key im) = (v:message_log_value im (snd k))
type message_log_inv (im:index_module) (f:MM.map' (message_log_key im) (message_log_range im)) = True //t:Type0{t = True}
type message_log (im:index_module) (rgn:log_region im) =
  MM.t rgn (message_log_key im) (message_log_range im) (message_log_inv im)

val pkey: Type0
val skey: Type0

val pkey_from_skey: sk:skey -> pk:pkey

val compatible_keys: sk:skey -> pk:pkey -> t:Type0{t <==> pk =!= pkey_from_skey sk}

val aux_t: (im:index_module{ID.get_subId im == subId_t}) -> (pm:plain_module{Plain.get_plain pm == plain_t}) -> rgn:log_region im -> Type u#1

abstract noeq type pkae_module =
  | PKAE:
    im:ID.index_module{ID.get_subId im == subId_t} ->
    pm:Plain.plain_module{Plain.get_plain pm == plain_t /\ Plain.plain_max_length #pm= plain_max_length} ->
    rgn:log_region im ->
    enc: (plain_t -> n:nonce -> pk:pkey -> sk:skey{compatible_keys sk pk} -> GTot cipher) ->
    dec: (c:cipher -> n:nonce -> pk:pkey -> sk:skey -> GTot (option plain_t)) ->
    aux: (aux_t im pm rgn) ->
    pkae_module

val get_message_log_region: pkm:pkae_module -> Tot (log_region pkm.im)
val get_message_logGT: pkm:pkae_module -> Tot (message_log pkm.im (get_message_log_region pkm)) //TODO: MK: would prefer this to be GTot

val create: rgn:(r:MR.rid{extends r root /\ is_eternal_region r /\ is_below r root}) -> St (pkae_module)

val zero_bytes: (n:nat{n<plain_max_length}) -> plain_t //b:bytes{Seq.length b = n /\ b=Seq.create n (UInt8.uint_to_t 0)}
//TODO: MK this can be modelled better

val pkey_to_subId: #pkm:pkae_module -> pk:pkey -> ID.get_subId pkm.im
val pkey_to_subId_inj: #pkm:pkae_module -> pk:pkey -> Lemma
  (requires True)
  (ensures (forall pk' . pkey_to_subId #pkm pk == pkey_to_subId #pkm pk' <==> pk == pk'))
  [SMTPat (pkey_to_subId #pkm pk)]

#set-options "--z3rlimit 2000 --max_ifuel 1 --max_fuel 0"
val nonce_is_fresh: (pkm:pkae_module) -> (i:id pkm.im) -> (n:nonce) -> (h:mem) ->
  (t:Type0{t <==>
    (MR.m_contains #(get_message_log_region pkm) (get_message_logGT pkm) h
      /\ MM.fresh #(get_message_log_region pkm)(get_message_logGT pkm) (n,i) h)})


//val pkey_from_skey_inj: sk:skey -> pk:pkey -> Lemma
//  (requires True)
//  (ensures (forall sk1 sk2 . pkey_from_skey sk1 == pkey_from_skey sk2 <==> sk1 == sk2))

val gen: unit -> ST (keypair:(pkey*skey){fst keypair == pkey_from_skey (snd keypair)})
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 ->
    modifies_none h0 h1
  ))

let registered pkm i = ID.registered pkm.im (ID.ID i)
let honest pkm i = ID.honest pkm.im (ID.ID i)
let dishonest pkm i = ID.dishonest pkm.im (ID.ID i)


val encrypt: pkm:pkae_module ->
             #i:id pkm.im ->
             n:nonce ->
             sk:skey ->
             pk:pkey{compatible_keys sk pk /\ i = ID.compose_ids pkm.im (pkey_to_subId #pkm pk) (pkey_to_subId #pkm (pkey_from_skey sk))} ->
             m:(Plain.protected_plain_t pkm.im (Plain.get_plain pkm.pm) i) ->
             ST cipher
  (requires (fun h0 ->
    registered pkm i
    /\ nonce_is_fresh pkm i n h0
  ))
  (ensures  (fun h0 c h1 ->
    ((honest pkm i /\ b2t ae_ind_cpa) // Ideal behaviour if the id is honest and the assumption holds
               ==> true)//(c == pkm.enc (zero_bytes (Plain.length #pkm.im #pkm.pm #i m)) n pk sk)) //TODO: MK: this cannot work as the ODH key is idealized, requires de-idealization step, maybe doable?
    /\ ((dishonest pkm i \/ ~(b2t ae_ind_cpa)) // Concrete behaviour otherwise.
                  ==> true)//(eq2 #cipher c (pkm.enc (Plain.repr #pkm.im #pkm.pm #i m) n pk sk)))
    // The message is added to the log. This also guarantees nonce-uniqueness.
      /\ MR.m_contains #(get_message_log_region pkm)(get_message_logGT pkm) h1
        /\ MR.witnessed (MM.contains #(get_message_log_region pkm) (get_message_logGT pkm) (n,i) (c,m))
        /\ MR.m_sel #(get_message_log_region pkm) h1 (get_message_logGT pkm)== MM.upd (MR.m_sel #(get_message_log_region pkm) h0 (get_message_logGT pkm)) (n,i) (c,m)
  ))

val decrypt: pkm:pkae_module -> #i:id pkm.im -> n:nonce -> sk:skey -> pk:pkey{compatible_keys sk pk /\ i = ID.compose_ids pkm.im (pkey_to_subId #pkm pk) (pkey_to_subId #pkm (pkey_from_skey sk))} -> c:cipher -> ST (option (Plain.protected_plain_t pkm.im (Plain.get_plain pkm.pm) i))
  (requires (fun h0 ->
    registered pkm i
  ))
  (ensures  (fun h0 c h1 -> true
  ))
  
