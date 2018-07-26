module Box.PKAE

open FStar.Set
open FStar.Seq
open FStar.HyperStack
open FStar.HyperStack.ST

open FStar.Endianness

open Box.Plain
open Box.Index

module MM = FStar.Monotonic.Map

let n32 = (n:nat{n<=32})
let bytes32 = b:bytes{Seq.length b <= 32}

#set-options "--z3rlimit 300 --max_ifuel 1 --max_fuel 1"

val pp : (pp:plain_package{pp.flag == Flags.pkae})

// Footpring function instead of rgn in the type
val pkae_package: rgn:erid -> Type u#1

//val create_pkae_package: rgn:erid -> ST (pkae_package rgn)
//  (requires (fun h0 -> True))
//  (ensures (fun h0 pkae_p h1 ->
//    modifies (Set.singleton rgn) h0 h1
//  ))
//
////val pkey_length: n32
//let pkey_length = 32
//val pkey : Type
//val get_pkey_raw: pkey -> Tot (lbytes pkey_length)
//val get_pkey_id: pk:pkey -> Tot (i:pk_id{i = PK_id (get_pkey_raw pk)})
//
////val skey_length: n32
//let skey_length = 32
//val skey : Type
//val get_skey_raw: skey -> GTot (lbytes pkey_length)
//val get_pkey_from_skey: skey -> pkey
//val get_skey_id: sk:skey -> Tot (i:pk_id{i = PK_id (get_pkey_raw (get_pkey_from_skey sk))})
//
//val gen : #rgn:erid -> ip:index_package rgn -> ST (keypair:(pkey*skey))
//  (requires (fun h0 -> True))
//  (ensures (fun h0 keypair h1 ->
//    get_pkey_from_skey (snd keypair) == fst keypair
//    /\ honest ip (PK_id (get_pkey_raw (fst keypair)))
//    /\ modifies (Set.singleton rgn) h0 h1
//  ))
//
//val coerce : #rgn:erid -> ip:index_package rgn -> pk_raw:lbytes pkey_length -> sk_raw:lbytes skey_length ->ST (keypair:(pkey*skey))
//  (requires (fun h0 ->
//    fresh ip (PK_id pk_raw) h0
//  ))
//  (ensures (fun h0 keypair h1 ->
//    get_pkey_from_skey (snd keypair) == fst keypair
//    /\ dishonest ip (get_pkey_id (fst keypair))
//    /\ get_pkey_raw (fst keypair) = pk_raw
//    /\ get_skey_raw (snd keypair) = sk_raw
//    /\ modifies (Set.singleton rgn) h0 h1
//  ))
//
//val compose_ids: pk_id -> pk_id -> inst_id
//
//val nonce_length:n32
//let nonce = lbytes nonce_length
//val valid_ciphertext_length : n32 -> bool
//let ciphertext = b:bytes32{valid_ciphertext_length (Seq.length b)}
//
//val compatible_keys: pkey -> skey -> bool
//
//type message_log_key =
//  | LOG_KEY: i:inst_id -> n:nonce -> c:ciphertext -> message_log_key
//
//let message_log_value (i:inst_id) = protected_plain pp i
//let message_log_range (k:message_log_key) = message_log_value (k.i)
//let message_log_inv (f:MM.map' (message_log_key) (message_log_range)) = True
//
//let message_log (rgn:erid) =
//  MM.t rgn (message_log_key) (message_log_range) (message_log_inv)
//
//val get_log: #rgn:erid -> pkae_package rgn -> message_log rgn
//
//let nonce_is_unique (#rgn:erid) (pkae_p:pkae_package rgn) (i:inst_id) (n:nonce) (h0:mem) =
//  forall c . MM.fresh (get_log pkae_p) (LOG_KEY i n c) h0
//
//let extended_message_log (#rgn:erid) (pkae_p:pkae_package rgn) (i:inst_id) (n:nonce) (c:ciphertext) (p:protected_plain pp i) (h0:mem) (h1:mem) =
//  let log_key = LOG_KEY i n c in
//  let log_value = p in
//  let log = get_log pkae_p in
//  sel h1 log == MM.upd (sel h0 log) log_key log_value
//  /\ witnessed (MM.defined log log_key)
//  /\ witnessed (MM.contains log log_key log_value)
//
//
//val enc_spec: p:plain pp -> pk:lbytes pkey_length -> sk:lbytes skey_length -> n:nonce -> c:ciphertext
////val enc_star: plain_length:n32 -> pk:lbytes pkey_length -> sk:lbytes skey_length -> n:nonce -> c:ciphertext
//val dec_spec: c:ciphertext -> pk:lbytes pkey_length -> sk:lbytes skey_length -> n:nonce -> option (p:plain pp)
//
//#set-options "--z3rlimit 300 --max_ifuel 0 --max_fuel 0"
//val encrypt: #rgn:erid -> pkae_p:pkae_package rgn -> ip:index_package rgn -> pk:pkey -> sk:skey{compatible_keys pk sk} -> n:nonce -> p:protected_plain pp (compose_ids (get_pkey_id pk) (get_skey_id sk)) -> ST ciphertext
//  (requires (fun h0 ->
//    let i = compose_ids (get_pkey_id pk) (get_skey_id sk) in
//    nonce_is_unique pkae_p i n h0
//  ))
//  (ensures (fun h0 c h1 ->
//    let i = compose_ids (get_pkey_id pk) (get_skey_id sk) in
//    //let both_honest = honest ip i in
//    modifies (Set.singleton rgn) h0 h1
//    /\ ((honest ip i /\ Flags.pkae) ==>
//      c == enc_star (length p) (get_pkey_raw pk) (get_skey_raw sk) n)
//    /\ ((dishonest ip i \/ ~(Flags.pkae)) ==>
//      c == enc_spec (repr #rgn #pp #ip #i p) (get_pkey_raw pk) (get_skey_raw sk) n)
//    /\ extended_message_log pkae_p i n c p h0 h1
//  ))
//
//val decrypt: #rgn:erid -> pkae_p:pkae_package rgn -> ip:index_package rgn -> pk:pkey -> sk:skey{compatible_keys pk sk} -> n:nonce -> c:ciphertext -> ST (option_p:option (protected_plain pp (compose_ids (get_pkey_id pk) (get_skey_id sk))))
//  (requires (fun h0 ->
//    True
//  ))
//  (ensures (fun h0 option_p h1 ->
//    let i = compose_ids (get_pkey_id pk) (get_skey_id sk) in
//    let option_spec = dec_spec c (get_pkey_raw pk) (get_skey_raw sk) n in
//    (modifies (Set.singleton rgn) h0 h1 \/ h0 == h1)
//    /\ ((honest ip i /\ Flags.pkae) ==>
//      (MM.sel (sel h0 (get_log pkae_p)) (LOG_KEY i n c) == option_p)
//      )
//    /\ ((dishonest ip i \/ ~(Flags.pkae)) ==>
//      (Some? option_spec ==>
//      (Some? option_p
//      /\ repr #rgn #pp #ip #i (Some?.v option_p) == Some?.v option_spec))
//      )
//  ))
