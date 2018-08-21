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

val pp : pp:plain_package{pp.flag == Flags.pkae}

noeq type public_key_encryption_scheme (public_key_length:n32) (secret_key_length:n32) =
  | PKES:
    gen: (unit -> lbytes secret_key_length*lbytes public_key_length) ->
    enc: (p:plain pp -> n:nonce pp -> pk:lbytes public_key_length -> sk:lbytes secret_key_length -> c:cipher pp) ->
    enc_star: (plain_length:nat{pp.valid_plain_length plain_length} -> c:cipher pp) ->
    dec: (c:cipher pp -> n:nonce pp -> pk:lbytes public_key_length -> sk:lbytes secret_key_length -> option (p:plain pp)) ->
//    correctness: (p:bytes -> k:lbytes key_length -> n:lbytes nonce_length -> Lemma
//    (requires True)
//    (ensures (
//      let dec_result = dec (enc p k n) k n in
//      Some? dec_result
//      /\ Some?.v dec_result == p
//    ))
      //    ) ->
    public_key_encryption_scheme public_key_length secret_key_length

noeq type pkae_parameters =
  | PK_Param:
  public_key_length: n32 ->
  secret_key_length: n32 ->
  pke_scheme: public_key_encryption_scheme public_key_length secret_key_length ->
  pkae_parameters

val pkp: pkae_parameters

let pkae_index_package = ip:index_package{
  Leaf_IP? ip
  /\ (match ip with
    | Leaf_IP t rgn log -> t == lbytes pkp.public_key_length)
  /\ id ip == lbytes pkp.public_key_length
  }

val pkey : Type0
val get_pkey_raw: pkey -> Tot (lbytes pkp.public_key_length)
//val get_pkey_id: (#pp:plain_package) -> (#pkp:pkae_parameters pp) -> (#ip:index_package pkp) -> pk:pkey pkp -> Tot (i:id ip)

val skey : Type0
val get_skey_raw: skey -> GTot (lbytes pkp.secret_key_length)
val get_pkey_raw_from_skey_raw: lbytes pkp.secret_key_length -> lbytes pkp.public_key_length
val get_pkey_from_skey: sk:skey -> pk:pkey{get_pkey_raw pk = get_pkey_raw_from_skey_raw (get_skey_raw sk)}
//val get_skey_id: #pp:plain_package -> #pkp:pkae_parameters pp -> ip:index_package pkp -> sk:skey pkp -> Tot (i:id ip{i = get_pkey_id (get_pkey_from_skey sk)})

let compatible_keys (sk:skey) (pk:pkey) = get_pkey_raw pk <> get_pkey_raw (get_pkey_from_skey sk)

#set-options "--z3rlimit 30 --max_ifuel 2 --max_fuel 2"
let compose_ip (ip:pkae_index_package) : ip':index_package{
  ip' == Node_IP [ip;ip]
  /\ id ip == lbytes pkp.public_key_length
  /\ id ip' == id ip * id ip
  /\ id ip' == lbytes pkp.public_key_length * lbytes pkp.public_key_length
} =
  let ip' = Node_IP [ip;ip] in
  assert(unfold_id [ip;ip] == id ip * id ip);
  assert(unfold_id [ip;ip] == id ip');
  ip'

let composed_id (ip:pkae_index_package) (pk1:pkey) (pk2:pkey{
    get_pkey_raw pk1 <> get_pkey_raw pk2
  }) : (id (compose_ip ip)) =
  let pk1_raw = get_pkey_raw pk1 in
  let pk2_raw = get_pkey_raw pk2 in
  let le_sh1 = little_endian pk1_raw in
  let le_sh2 = little_endian pk2_raw in
  assert(hasEq (lbytes pkp.secret_key_length * lbytes pkp.public_key_length));
  if le_sh1 < le_sh2 then
    pk1_raw,pk2_raw
  else
    pk2_raw,pk1_raw

val pkae_package: (ip:pkae_index_package) -> Type u#1

val create_pkae_package: (ip:pkae_index_package) -> rgn:erid -> ST (pkae_package ip)
  (requires (fun h0 -> True))
  (ensures (fun h0 pkae_p h1 ->
    modifies (Set.singleton rgn) h0 h1
  ))



val gen_footprint: (#ip:pkae_index_package) -> pkae_package ip -> h0:mem -> h1:mem -> Type0

val gen : (#ip:pkae_index_package) -> pkae_p:pkae_package ip -> ST (keypair:(skey*pkey))
  (requires (fun h0 ->
    Flags.model
  ))
  (ensures (fun h0 (sk,pk) h1 ->
    get_pkey_from_skey sk == pk
    /\ honest #ip (get_pkey_raw pk)
    /\ registered #ip (get_pkey_raw pk)
    /\ gen_footprint pkae_p h0 h1
  ))

val coerce_pkey_footprint: (#ip:pkae_index_package) -> pkae_p:pkae_package ip -> pk_raw:lbytes pkp.public_key_length -> h0:mem -> h1:mem -> Type0

val coerce_pkey : (#ip:pkae_index_package) -> pkae_p:pkae_package ip -> pk_raw:lbytes pkp.public_key_length -> ST (pk:pkey)
  (requires (fun h0 ->
    corrupt #ip pk_raw
    /\ registered #ip pk_raw
  ))
  (ensures (fun h0 pk h1 ->
    get_pkey_raw pk = pk_raw
    /\ coerce_pkey_footprint pkae_p pk_raw h0 h1
  ))

val coerce_skey_footprint: (#ip:pkae_index_package) -> pkae_p:pkae_package ip -> sk_raw:lbytes pkp.secret_key_length -> h0:mem -> h1:mem -> Type0

val coerce_skey : (#ip:pkae_index_package) -> pkae_p:pkae_package ip -> sk_raw:lbytes pkp.secret_key_length -> ST (sk:skey)
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

val get_log_rgn: (#ip:pkae_index_package) -> (pkae_p:pkae_package ip) -> Tot (rgn:erid)

val get_log: (#ip:pkae_index_package) -> (pkae_p:pkae_package ip) -> GTot (Mem.message_log (compose_ip ip) pp (get_log_rgn pkae_p))

let nonce_is_unique (#ip:pkae_index_package) (pkae_p:pkae_package ip) i n h0 =
  Flags.model ==>
    (let log: i_message_log (compose_ip ip) pp (get_log_rgn pkae_p) = get_log pkae_p in
    forall c . MM.fresh log (i,n,c) h0)

let extended_message_log
  (#ip:pkae_index_package)
  (pkae_p:pkae_package ip)
  (pk:pkey)
  (sk:skey{compatible_keys sk pk})
  (n:nonce pp)
  (c:cipher pp)
  (p:protected_plain #(compose_ip ip) pp (composed_id ip pk (get_pkey_from_skey sk)))
  (h0:mem) (h1:mem) =
  let i = composed_id ip pk (get_pkey_from_skey sk) in
  if Flags.model then
    let log_key = i,n,c in
    let log_value = p in
    let log: i_message_log (compose_ip ip) pp (get_log_rgn pkae_p) = get_log pkae_p in
    sel h1 log == MM.upd (sel h0 log) log_key log_value
    /\ witnessed (MM.defined log log_key)
    /\ witnessed (MM.contains log log_key log_value)
  else
    True

//val encrypt_footprint:
//  (#ip:pkae_index_package) ->
//  (pkae_p:pkae_package ip) ->
//  (pk:pkey) ->
//  (sk:skey{compatible_keys sk pk}) ->
//  (n:nonce pp) ->
//  (c:cipher pp) ->
//  (p:protected_plain #(compose_ip ip) pp (composed_id ip pk (get_pkey_from_skey sk))) ->
//  (h0:mem) ->
//  (h1:mem) ->
//  Type0

val decrypt_footprint:
  (#ip:pkae_index_package) ->
  (pkae_p:pkae_package ip) ->
  (pk:pkey) ->
  (sk:skey{compatible_keys sk pk}) ->
  (n:nonce pp) ->
  (c:cipher pp) ->
  (option (p:protected_plain #(compose_ip ip) pp (composed_id ip pk (get_pkey_from_skey sk)))) ->
  (h0:mem) ->
  (h1:mem) ->
  Type0

#set-options "--z3rlimit 30 --max_ifuel 2 --max_fuel 2"
val encrypt:
  #ip:pkae_index_package ->
  pkae_p:pkae_package ip ->
  pk:pkey ->
  sk:skey{compatible_keys sk pk} ->
  n:nonce pp ->
  p:protected_plain #(compose_ip ip) pp (composed_id ip pk (get_pkey_from_skey sk)) ->
  ST (cipher pp)
  (requires (fun h0 ->
    let i = composed_id ip pk (get_pkey_from_skey sk) in
    nonce_is_unique pkae_p i n h0
    /\ registered #(compose_ip ip) i
  ))
  (ensures (fun h0 c h1 ->
    let i = composed_id ip pk (get_pkey_from_skey sk) in
    encrypt_footprint pkae_p pk sk n c p h0 h1
    /\ ((honest #(compose_ip ip) i /\ Flags.pkae) ==>
      c == pkp.pke_scheme.enc_star (Plain.length p))
    /\ ((corrupt #(compose_ip ip) i \/ ~(Flags.pkae)) ==>
      c == pkp.pke_scheme.enc (Plain.repr #(compose_ip ip) #pp  p) n (get_pkey_raw pk) (get_skey_raw sk))
    /\ extended_message_log pkae_p pk sk n c p h0 h1
  ))

val decrypt:
  #ip:pkae_index_package ->
  pkae_p:pkae_package ip ->
  pk:pkey ->
  sk:skey{compatible_keys sk pk} ->
  n:nonce pp ->
  c:cipher pp ->
  ST (option (p:protected_plain #(compose_ip ip) pp (composed_id ip pk (get_pkey_from_skey sk))))
  (requires (fun h0 ->
    let i = composed_id ip pk (get_pkey_from_skey sk) in
    registered #(compose_ip ip) i
  ))
  (ensures (fun h0 option_p h1 ->
    let i:id (compose_ip ip) = composed_id ip pk (get_pkey_from_skey sk) in
    let option_spec = pkp.pke_scheme.dec c n (get_pkey_raw pk) (get_skey_raw sk) in
    decrypt_footprint pkae_p pk sk n c option_p h0 h1
    /\ ((honest i /\ Flags.pkae) ==>
      (let log: i_message_log (compose_ip ip) pp (get_log_rgn pkae_p) = get_log pkae_p in
      MM.sel (sel h0 log) (i,n,c) == option_p))
    /\ ((corrupt i \/ ~(Flags.pkae)) ==>
      (Some? option_spec ==>
      (Some? option_p
      /\ Plain.repr (Some?.v option_p) == Some?.v option_spec)))
  ))
