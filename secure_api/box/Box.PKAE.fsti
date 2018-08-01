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

let n32 = nat
let bytes32 = b:bytes{Seq.length b <= 32}

val pkae_package: Type u#1
// Footpring function instead of rgn in the type
//val pkae_package: rgn:erid -> Type0

val create_pkae_package: rgn:erid -> ST (pkae_package)
  (requires (fun h0 -> True))
  (ensures (fun h0 pkae_p h1 ->
    modifies (Set.singleton rgn) h0 h1
  ))

//val pkey_length: n32
let pkey_length = 32
val pkey : Type0
val get_pkey_raw: pkey -> Tot (lbytes pkey_length)
val get_pkey_id: pk:pkey -> Tot (i:pk_id{i = PK_id (get_pkey_raw pk)})

//val skey_length: n32
let skey_length = 32
val skey : Type0
val get_skey_raw: skey -> GTot (lbytes pkey_length)
val get_pkey_raw_from_skey_raw: lbytes skey_length -> lbytes pkey_length
val get_pkey_from_skey: sk:skey -> pk:pkey{get_pkey_raw pk = get_pkey_raw_from_skey_raw (get_skey_raw sk)}
val get_skey_id: sk:skey -> Tot (i:pk_id{i = PK_id (get_pkey_raw (get_pkey_from_skey sk))})


val get_index_package: pkae_p:pkae_package -> ip:index_package

let honest pkae_p i = honest (get_index_package pkae_p) i
let dishonest pkae_p i = dishonest (get_index_package pkae_p) i
let registered pkae_p i = registered (get_index_package pkae_p) i
let fresh pkae_p i h = fresh (get_index_package pkae_p) i h

val gen_footprint: pkae_package -> h0:mem -> h1:mem -> Type0

val gen : pkae_p:pkae_package -> ST (keypair:(skey*pkey))
  (requires (fun h0 -> True))
  (ensures (fun h0 keypair h1 ->
    get_pkey_from_skey (fst keypair) == snd keypair
    /\ honest pkae_p (get_pkey_id (snd keypair))
    /\ gen_footprint pkae_p h0 h1
  ))

val coerce_pkey_footprint: pkae_package -> pk_raw:lbytes pkey_length -> h0:mem -> h1:mem -> Type0

val coerce_pkey : pkae_p:pkae_package -> pk_raw:lbytes pkey_length -> ST (pk:pkey)
  (requires (fun h0 ->
    fresh pkae_p (PK_id pk_raw) h0
  ))
  (ensures (fun h0 pk h1 ->
    dishonest pkae_p (get_pkey_id pk)
    /\ get_pkey_raw pk = pk_raw
    /\ coerce_pkey_footprint pkae_p pk_raw h0 h1
  ))

val coerce_skey_footprint: pkae_package -> sk_raw:lbytes skey_length -> h0:mem -> h1:mem -> Type0

val coerce_skey : pkae_p:pkae_package -> sk_raw:lbytes skey_length -> ST (sk:skey)
  (requires (fun h0 ->
    fresh pkae_p (PK_id (get_pkey_raw_from_skey_raw sk_raw)) h0
  ))
  (ensures (fun h0 sk h1 ->
    dishonest pkae_p (get_skey_id sk)
    /\ get_skey_raw sk = sk_raw
    /\ coerce_skey_footprint pkae_p sk_raw h0 h1
  ))

val compose_ids: pk1:pk_id -> pk2:pk_id{pk1 <> pk2} -> inst_id

val nonce: eqtype
val ciphertext: eqtype
//val valid_ciphertext_length : n32 -> bool
//let ciphertext = b:bytes32{valid_ciphertext_length (Seq.length b)}


//type message_log_key = inst_id*nonce*ciphertext
//type message_log_key = inst_id*nonce*ciphertext
////  | LOG_KEY: i:inst_id -> n:nonce -> c:ciphertext -> message_log_key
//
//let fst t = Mktuple3?._1 t
//let snd t = Mktuple3?._2 t
//let thrd t = Mktuple3?._3 t
//
//let message_log_value (i:inst_id) = protected_plain pp i
//let message_log_range (k:message_log_key) = message_log_value (Mktuple3?._1 k)
//let message_log_inv (f:MM.map' (message_log_key) (message_log_range)) = True
//
//let message_log (rgn:erid) =
//  MM.t rgn (message_log_key) (message_log_range) (message_log_inv)
val compatible_keys: pkey -> skey -> bool

val get_log_rgn: pkae_p:pkae_package -> Tot (rgn:erid)

val get_pp: pkae_p:pkae_package -> plain_package

val get_log: pkae_p:pkae_package -> GTot (Mem.message_log nonce ciphertext (get_pp pkae_p) (get_log_rgn pkae_p))
//val get_log: pkae_p:pkae_package -> GTot (Mem.message_log nonce ciphertext pp (get_log_rgn pkae_p))


//val nonce_is_unique: (pkae_p:pkae_package) -> (i:inst_id) -> (n:nonce) -> (h0:mem) -> GTot (t:Type0{t <==> (forall c . MM.fresh (get_log pkae_p) (i,n,c) h0)})
let nonce_is_unique pkae_p i n h0 =
  forall c . MM.fresh (get_log pkae_p) (i,n,c) h0

let extended_message_log (pkae_p:pkae_package) (i:inst_id) (n:nonce) (c:ciphertext) (p:protected_plain (get_pp pkae_p) i) (h0:mem) (h1:mem) =
  let log_key = i,n,c in
  let log_value = p in
  let log = get_log pkae_p in
  sel h1 log == MM.upd (sel h0 log) log_key log_value
  /\ witnessed (MM.defined log log_key)
  /\ witnessed (MM.contains log log_key log_value)

val encrypt_footprint: (pkae_p:pkae_package) -> (i:inst_id) -> (n:nonce) -> (c:ciphertext) -> (p:protected_plain (get_pp pkae_p) i) -> (h0:mem) -> (h1:mem) -> Type0
val decrypt_footprint: (pkae_p:pkae_package) -> (i:inst_id) -> (n:nonce) -> (c:ciphertext) -> option (p:protected_plain (get_pp pkae_p) i) -> (h0:mem) -> (h1:mem) -> Type0

val enc_spec: pkae_p:pkae_package -> p:plain (get_pp pkae_p) -> pk:lbytes pkey_length -> sk:lbytes skey_length -> n:nonce -> c:ciphertext
val enc_star: pkae_p:pkae_package -> plain_length:n32{(get_pp pkae_p).valid_length plain_length} -> c:ciphertext
val dec_spec: pkae_p:pkae_package -> c:ciphertext -> pk:lbytes pkey_length -> sk:lbytes skey_length -> n:nonce -> option (p:plain (get_pp pkae_p))

#set-options "--z3rlimit 300 --max_ifuel 0 --max_fuel 0"
val encrypt: pkae_p:pkae_package -> pk:pkey -> sk:skey{compatible_keys pk sk} -> n:nonce -> p:protected_plain (get_pp pkae_p) (compose_ids (get_pkey_id pk) (get_skey_id sk)) -> ST ciphertext
  (requires (fun h0 ->
    let i = compose_ids (get_pkey_id pk) (get_skey_id sk) in
    nonce_is_unique pkae_p i n h0
    /\ registered pkae_p i
  ))
  (ensures (fun h0 c h1 ->
    let i = compose_ids (get_pkey_id pk) (get_skey_id sk) in
    encrypt_footprint pkae_p i n c p h0 h1
    /\ ((honest pkae_p i /\ Flags.pkae) ==>
      c == enc_star pkae_p (Plain.length p))
    /\ ((dishonest pkae_p i \/ ~(Flags.pkae)) ==>
      c == enc_spec pkae_p (repr #(get_pp pkae_p) #(get_index_package pkae_p) #i p) (get_pkey_raw pk) (get_skey_raw sk) n)
    /\ extended_message_log pkae_p i n c p h0 h1
  ))

val decrypt: pkae_p:pkae_package -> pk:pkey -> sk:skey{compatible_keys pk sk} -> n:nonce -> c:ciphertext -> ST (option_p:option (protected_plain (get_pp pkae_p) (compose_ids (get_pkey_id pk) (get_skey_id sk))))
  (requires (fun h0 ->
    True
  ))
  (ensures (fun h0 option_p h1 ->
    let i = compose_ids (get_pkey_id pk) (get_skey_id sk) in
    let option_spec = dec_spec pkae_p c (get_pkey_raw pk) (get_skey_raw sk) n in
    decrypt_footprint pkae_p i n c option_p h0 h1
    /\ ((honest pkae_p i /\ Flags.pkae) ==>
      (MM.sel (sel h0 (get_log pkae_p)) (i,n,c) == option_p)
      )
    /\ ((dishonest pkae_p i \/ ~(Flags.pkae)) ==>
      (Some? option_spec ==>
      (Some? option_p
      /\ repr #(get_pp pkae_p) #(get_index_package pkae_p) #i (Some?.v option_p) == Some?.v option_spec))
      )
  ))
