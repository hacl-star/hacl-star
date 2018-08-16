module Box.PKAE

open FStar.Set
open FStar.Seq
open FStar.HyperStack
open FStar.HyperStack.ST

open FStar.Endianness

open Box.Plain
open Box.Index
open Mem

module MM = FStar.Monotonic.Map

let n32 = n:nat{n <= 32}
let bytes32 = b:bytes{Seq.length b <= 32}

let plain_package = pp:plain_package{pp.flag == Flags.pkae}

noeq type public_key_encryption_scheme (public_key_length:n32) (secret_key_length:n32) (pp:plain_package)=
  | PKES:
    gen: (unit -> lbytes secret_key_length*lbytes public_key_length) ->
    enc: (p:plain pp -> sk:lbytes secret_key_length -> pk:lbytes public_key_length -> n:nonce pp -> c:cipher pp) ->
    enc_star: (plain_length:nat{pp.valid_plain_length plain_length} -> c:cipher pp) ->
    dec: (c:cipher pp -> sk:lbytes secret_key_length -> pk:lbytes public_key_length -> n:nonce pp -> option (p:plain pp)) ->
//    correctness: (p:bytes -> k:lbytes key_length -> n:lbytes nonce_length -> Lemma
//    (requires True)
//    (ensures (
//      let dec_result = dec (enc p k n) k n in
//      Some? dec_result
//      /\ Some?.v dec_result == p
//    ))
      //    ) ->
    public_key_encryption_scheme public_key_length secret_key_length pp

noeq type pkae_parameters (pp:plain_package) =
  | PK_Param:
  public_key_length: n32 ->
  secret_key_length: n32 ->
  pke_scheme: public_key_encryption_scheme public_key_length secret_key_length pp ->
  pkae_parameters pp

let index_package (#pp:plain_package) (pkp:pkae_parameters pp) = ip:index_package{
  Leaf_IP? ip
  /\ (match ip with
    | Leaf_IP t rgn log -> t == lbytes pkp.public_key_length)
  }

val pkey : #pp:plain_package -> pkae_parameters pp -> Type0
val get_pkey_raw: #pp:plain_package -> #pkp:pkae_parameters pp -> pkey pkp -> Tot (lbytes pkp.public_key_length)
//val get_pkey_id: (#pp:plain_package) -> (#pkp:pkae_parameters pp) -> (#ip:index_package pkp) -> pk:pkey pkp -> Tot (i:id ip)

val skey : #pp:plain_package -> pkae_parameters pp -> Type0
val get_skey_raw: #pp:plain_package -> #pkp:pkae_parameters pp -> skey pkp -> GTot (lbytes pkp.secret_key_length)
val get_pkey_raw_from_skey_raw: #pp:plain_package -> #pkp:pkae_parameters pp -> lbytes pkp.secret_key_length -> lbytes pkp.public_key_length
val get_pkey_from_skey: #pp:plain_package -> #pkp:pkae_parameters pp -> sk:skey pkp -> pk:pkey pkp{get_pkey_raw pk = get_pkey_raw_from_skey_raw (get_skey_raw sk)}
//val get_skey_id: #pp:plain_package -> #pkp:pkae_parameters pp -> ip:index_package pkp -> sk:skey pkp -> Tot (i:id ip{i = get_pkey_id (get_pkey_from_skey sk)})

let compatible_keys (#pp:plain_package) (#pkp:pkae_parameters pp) (sk:skey pkp) (pk:pkey pkp) = get_pkey_raw pk <> get_pkey_raw (get_pkey_from_skey sk)

let composed_ip (#pp:plain_package) (#pkp:pkae_parameters pp) (ip:index_package pkp) = Node_IP [ip;ip]
let composed_id (#pp:plain_package) (#pkp:pkae_parameters pp) (pk1:pkey pkp) (pk2:pkey pkp{
    get_pkey_raw pk1 <> get_pkey_raw pk2
  }) :(lbytes pkp.public_key_length * lbytes pkp.public_key_length) =
  let pk1_raw = get_pkey_raw pk1 in
  let pk2_raw = get_pkey_raw pk2 in
  let le_sh1 = little_endian pk1_raw in
  let le_sh2 = little_endian pk2_raw in
  assert(hasEq (lbytes pkp.secret_key_length * lbytes pkp.public_key_length));
  if le_sh1 < le_sh2 then
    pk1_raw,pk2_raw
  else
    pk2_raw,pk1_raw

val pkae_package: (#pp:plain_package) -> (#pkp:pkae_parameters pp) -> (ip:index_package pkp) -> Type u#1

val create_pkae_package: (#pp:plain_package) -> (pkp:pkae_parameters pp) -> (ip:index_package pkp) -> rgn:erid -> ST (pkae_package ip)
  (requires (fun h0 -> True))
  (ensures (fun h0 pkae_p h1 ->
    modifies (Set.singleton rgn) h0 h1
  ))



val gen_footprint: (#pp:plain_package) -> (#pkp:pkae_parameters pp) -> (#ip:index_package pkp) -> pkae_package ip -> h0:mem -> h1:mem -> Type0

val gen : (#pp:plain_package) -> (#pkp:pkae_parameters pp) -> (#ip:index_package pkp) -> pkae_p:pkae_package ip -> ST (keypair:(skey pkp*pkey pkp))
  (requires (fun h0 ->
    Flags.model
  ))
  (ensures (fun h0 (sk,pk) h1 ->
    get_pkey_from_skey sk == pk
    /\ honest #ip (get_pkey_raw pk)
    /\ registered #ip (get_pkey_raw pk)
    /\ gen_footprint pkae_p h0 h1
  ))

val coerce_pkey_footprint: (#pp:plain_package) -> (#pkp:pkae_parameters pp) -> (#ip:index_package pkp) -> pkae_p:pkae_package ip -> pk_raw:lbytes pkp.public_key_length -> h0:mem -> h1:mem -> Type0

val coerce_pkey : (#pp:plain_package) -> (#pkp:pkae_parameters pp) -> (#ip:index_package pkp) -> pkae_p:pkae_package ip -> pk_raw:lbytes pkp.public_key_length -> ST (pk:pkey pkp)
  (requires (fun h0 ->
    corrupt #ip pk_raw
    /\ registered #ip pk_raw
  ))
  (ensures (fun h0 pk h1 ->
    get_pkey_raw pk = pk_raw
    /\ coerce_pkey_footprint pkae_p pk_raw h0 h1
  ))

val coerce_skey_footprint: (#pp:plain_package) -> (#pkp:pkae_parameters pp) -> (#ip:index_package pkp) -> pkae_p:pkae_package ip -> sk_raw:lbytes pkp.secret_key_length -> h0:mem -> h1:mem -> Type0

val coerce_skey : (#pp:plain_package) -> (#pkp:pkae_parameters pp) -> (#ip:index_package pkp) -> pkae_p:pkae_package ip -> sk_raw:lbytes pkp.secret_key_length -> ST (sk:skey pkp)
  (requires (fun h0 ->
    let pk_raw = get_pkey_raw_from_skey_raw sk_raw in
    corrupt #ip pk_raw
    /\ registered #ip pk_raw
  ))
  (ensures (fun h0 sk h1 ->
    let pk_raw = get_pkey_raw_from_skey_raw sk_raw in
    get_skey_raw sk = sk_raw
    /\ coerce_skey_footprint pkae_p sk_raw h0 h1
  ))

val get_log_rgn: (#pp:plain_package) -> (#pkp:pkae_parameters pp) -> (#ip:index_package pkp) -> (pkae_p:pkae_package ip) -> Tot (rgn:erid)

val get_log: (#pp:plain_package) -> (#pkp:pkae_parameters pp) -> (#ip:index_package pkp) -> (pkae_p:pkae_package ip) -> GTot (Mem.message_log (composed_ip ip) pp (get_log_rgn pkae_p))

let nonce_is_unique (#pp:plain_package) (#pkp:pkae_parameters pp) (#ip:index_package pkp) (pkae_p:pkae_package ip) i n h0 =
  Flags.model ==>
    (let log: i_message_log (composed_ip ip) pp (get_log_rgn pkae_p) = get_log pkae_p in
    forall c . MM.fresh log (i,n,c) h0)

let extended_message_log (#pp:plain_package) (#pkp:pkae_parameters pp) (#ip:index_package pkp) (pkae_p:pkae_package ip) (i:id (composed_ip ip)) (n:nonce pp) (c:cipher pp) (p:protected_plain pp i) (h0:mem) (h1:mem) =
  if Flags.model then
    let log_key = i,n,c in
    let log_value = p in
    let log: i_message_log (composed_ip ip) pp (get_log_rgn pkae_p) = get_log pkae_p in
    sel h1 log == MM.upd (sel h0 log) log_key log_value
    /\ witnessed (MM.defined log log_key)
    /\ witnessed (MM.contains log log_key log_value)
  else
    True

val encrypt_footprint:
  (#pp:plain_package) ->
  (#pkp:pkae_parameters pp) ->
  (#ip:index_package pkp) ->
  (pkae_p:pkae_package ip) ->
  (pk:pkey pkp) ->
  (sk:skey pkp{compatible_keys sk pk}) ->
  (n:nonce pp) ->
  (c:cipher pp) ->
  (p:protected_plain #(composed_ip ip) pp (composed_id pk (get_pkey_from_skey sk))) ->
  (h0:mem) ->
  (h1:mem) ->
  Type0

val decrypt_footprint:
  (#pp:plain_package) ->
  (#pkp:pkae_parameters pp) ->
  (#ip:index_package pkp) ->
  (pkae_p:pkae_package ip) ->
  (pk:pkey pkp) ->
  (sk:skey pkp{compatible_keys sk pk}) ->
  (n:nonce pp) ->
  (c:cipher pp) ->
  (option (p:protected_plain #(composed_ip ip) pp (composed_id pk (get_pkey_from_skey sk)))) ->
  (h0:mem) ->
  (h1:mem) ->
  Type0

#set-options "--z3rlimit 30 --max_ifuel 2 --max_fuel 2"
val encrypt:
  #pp:plain_package ->
  #pkp:pkae_parameters pp ->
  #ip:index_package pkp ->
  pkae_p:pkae_package ip ->
  pk:pkey pkp ->
  sk:skey pkp{compatible_keys sk pk} ->
  n:nonce pp ->
  p:protected_plain #(composed_ip ip) pp (composed_id pk (get_pkey_from_skey sk)) ->
  ST (cipher pp)
  (requires (fun h0 ->
    let i = composed_id pk (get_pkey_from_skey sk) in
    nonce_is_unique pkae_p i n h0
    /\ registered #(composed_ip ip) i
  ))
  (ensures (fun h0 c h1 ->
    let i = composed_id pk (get_pkey_from_skey sk) in
    encrypt_footprint pkae_p pk sk n c p h0 h1
    /\ ((honest #(composed_ip ip) i /\ Flags.pkae) ==>
      c == pkp.pke_scheme.enc_star (Plain.length p))
    /\ ((corrupt #(composed_ip ip) i \/ ~(Flags.pkae)) ==>
      c == pkp.pke_scheme.enc (Plain.repr #(composed_ip ip) #pp  p) (get_skey_raw sk) (get_pkey_raw pk) n)
    /\ extended_message_log pkae_p i n c p h0 h1
  ))

val decrypt:
  #pp:plain_package ->
  #pkp:pkae_parameters pp ->
  #ip:index_package pkp ->
  pkae_p:pkae_package ip ->
  pk:pkey pkp ->
  sk:skey pkp{compatible_keys sk pk} ->
  n:nonce pp ->
  c:cipher pp ->
  ST (option (p:protected_plain #(composed_ip ip) pp (composed_id pk (get_pkey_from_skey sk))))
  (requires (fun h0 ->
    let i = composed_id pk (get_pkey_from_skey sk) in
    registered #(composed_ip ip) i
  ))
  (ensures (fun h0 option_p h1 ->
    let i:id (composed_ip ip) = composed_id pk (get_pkey_from_skey sk) in
    let option_spec = pkp.pke_scheme.dec c (get_skey_raw sk) (get_pkey_raw pk) n in
    decrypt_footprint pkae_p pk sk n c option_p h0 h1
    /\ ((honest i /\ Flags.pkae) ==>
      (let log: i_message_log (composed_ip ip) pp (get_log_rgn pkae_p) = get_log pkae_p in
      MM.sel (sel h0 log) (i,n,c) == option_p))
    /\ ((corrupt i \/ ~(Flags.pkae)) ==>
      (Some? option_spec ==>
      (Some? option_p
      /\ Plain.repr (Some?.v option_p) == Some?.v option_spec)))
  ))
