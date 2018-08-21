module Box.PKAE

open FStar.Set
open FStar.Seq
open FStar.HyperStack
open FStar.HyperStack.ST

open FStar.Endianness

open Box.Plain
open Box.Index

module AE = Box.AE
module ODH = Box.ODH
module MM = FStar.Monotonic.Map
module AE_Spec = Spec.SecretBox
module ODH_Spec = Spec.Curve25519
module PKAE_Spec = Spec.CryptoBox
module H = Spec.HSalsa20

assume val random_bytes: n:nat -> lbytes n
//
//assume val pkae_flag: bool

let n32 = n:nat{n <= 32}
let bytes32 = b:bytes{Seq.length b <= 32}

val ae_enc_star: n:(n:nat{AE_Spec.valid_plain_length n}) -> b:lbytes (n+16){AE_Spec.valid_cipher_length (n+16)}
let ae_enc_star n = Seq.append (random_bytes n) (random_bytes 16)

val pp : pp:plain_package{pp.flag == Flags.pkae}
let pp = PP Flags.pkae AE_Spec.valid_plain_length AE_Spec.valid_cipher_length (fun n -> n = AE_Spec.noncelen)

// For some reason it doesn't verify if there is an additional refinement on the output of secretbox_open_easy
#set-options "--z3rlimit 300 --max_ifuel 1 --max_fuel 0"
let secretbox_scheme =
  let ss = AE.ES #(AE_Spec.keylen) #pp (fun () -> random_bytes 32) AE_Spec.secretbox_easy (ae_enc_star) AE_Spec.secretbox_open_easy in
  ss

let ae_params =
  let aep = AE.GP AE_Spec.keylen secretbox_scheme in
  aep

//let ae_package_log_key = i:ODH.id
//let ae_package_log_value (rgn:erid) (i:ODH.id) = (ap:AE.ae_package #ODH.id #i #AE_Spec.keylen kp ae_params pp{extends (AE.get_ap_rgn ap) rgn})
//let ae_package_log_range (rgn:erid) (k:ae_package_log_key) = ae_package_log_value rgn k
//let ae_package_log_inv (rgn:erid) (f:MM.map' (ae_package_log_key) (ae_package_log_range rgn))  = True
//
//let ae_package_log (log_rgn:erid) (ap_rgn:erid) =
//  MM.t log_rgn (ae_package_log_key) (ae_package_log_range ap_rgn) (ae_package_log_inv ap_rgn)

let zero_nonce = Seq.create H.noncelen (UInt8.uint_to_t 0)
let hsalsa20_hash input = H.hsalsa20 input zero_nonce

let odh_params = ODH.OP (ODH_Spec.serialized_point_length) (ODH_Spec.scalar_length) (H.keylen) (ODH_Spec.base_point) (ODH_Spec.scalarmult) (hsalsa20_hash)


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

let cryptobox :public_key_encryption_scheme (PKAE_Spec.dh_keylen) (PKAE_Spec.dh_keylen) = PKES (fun () -> random_bytes 32,random_bytes 32) PKAE_Spec.cryptobox (ae_enc_star) PKAE_Spec.cryptobox_open

noeq type pkae_parameters =
  | PK_Param:
  public_key_length: n32 ->
  secret_key_length: n32 ->
  pke_scheme: public_key_encryption_scheme public_key_length secret_key_length ->
  pkae_parameters

val pkp: pkae_parameters
let pkp = PK_Param odh_params.ODH.share_length odh_params.ODH.exponent_length cryptobox

let pkae_index_package = ip:index_package{
  Leaf_IP? ip
  /\ (match ip with
    | Leaf_IP t rgn log -> t == lbytes pkp.public_key_length)
  /\ id ip == lbytes pkp.public_key_length
  }

val pkey : Type0
let pkey = ODH.share odh_params
//val get_pkey_id: (#pp:plain_package) -> (#pkp:pkae_parameters pp) -> (#ip:index_package pkp) -> pk:pkey pkp -> Tot (i:id ip)

#set-options "--z3rlimit 300 --max_ifuel 1 --max_fuel 0"
val get_pkey_raw: pkey -> Tot (lbytes pkp.public_key_length)
let get_pkey_raw = ODH.get_share_raw

val skey : Type0
let skey = ODH.exponent odh_params
val get_skey_raw: skey -> GTot (lbytes pkp.secret_key_length)
let get_skey_raw = ODH.get_exponent_raw
val get_pkey_raw_from_skey_raw: lbytes pkp.secret_key_length -> lbytes pkp.public_key_length
let get_pkey_raw_from_skey_raw skey_raw = odh_params.ODH.exponentiate skey_raw odh_params.ODH.generator
val get_pkey_from_skey: sk:skey -> pk:pkey{get_pkey_raw pk = get_pkey_raw_from_skey_raw (get_skey_raw sk)}
let get_pkey_from_skey = ODH.get_exp_share

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
#set-options "--z3rlimit 30 --max_ifuel 0 --max_fuel 0"
noeq abstract type pkae_package (ip:pkae_index_package) =
  | PKAE_P :
    pkae_rgn:erid ->
    kp: Key.key_package (compose_ip ip){kp.Key.key_length = odh_params.ODH.hash_length} ->
    op: ODH.odh_package #odh_params ip kp ->
    ap: AE.ae_package #pp (compose_ip ip) ae_params ->
    pkae_package ip

#set-options "--z3rlimit 90 --max_ifuel 1 --max_fuel 1"
val create_pkae_package: (ip:pkae_index_package) -> rgn:erid -> ST (pkae_package ip)
  (requires (fun h0 -> True))
  (ensures (fun h0 pkae_p h1 ->
    modifies (Set.singleton rgn) h0 h1
  ))
let create_pkae_package ip rgn =
  let pkae_rgn = new_region rgn in
  let kp = AE.create_ae_key_package (compose_ip ip) AE_Spec.keylen in
  let op = ODH.create_odh_package ip pkae_rgn kp in
  let ap = AE.create_ae_package #(compose_ip ip) #pp pkae_rgn ae_params in
  PKAE_P pkae_rgn kp op ap

#set-options "--z3rlimit 90 --max_ifuel 1 --max_fuel 1"
val gen_footprint: (#ip:pkae_index_package) -> pkae_package ip -> h0:mem -> h1:mem -> Type0
let gen_footprint #ip pkae_p h0 h1 = ODH.gen_dh_footprint #odh_params ip h0 h1

#set-options "--z3rlimit 90 --max_ifuel 1 --max_fuel 1"
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
let gen #ip pkae_p = ODH.gen_dh #odh_params ip

val coerce_pkey_footprint: (#ip:pkae_index_package) -> pkae_p:pkae_package ip -> pk_raw:lbytes pkp.public_key_length -> h0:mem -> h1:mem -> Type0
let coerce_pkey_footprint #ip pkae_p pk_raw h0 h1 = ODH.coerce_dh_sh_footprint #odh_params ip pk_raw h0 h1

val coerce_pkey : (#ip:pkae_index_package) -> pkae_p:pkae_package ip -> pk_raw:lbytes pkp.public_key_length -> ST (pk:pkey)
  (requires (fun h0 ->
    corrupt #ip pk_raw
    /\ registered #ip pk_raw
  ))
  (ensures (fun h0 pk h1 ->
    get_pkey_raw pk = pk_raw
    /\ coerce_pkey_footprint pkae_p pk_raw h0 h1
  ))
let coerce_pkey #ip pkae_p pk_raw =
  let pk = ODH.coerce_dh_sh ip  pk_raw in
  pk

val coerce_skey_footprint: (#ip:pkae_index_package) -> pkae_p:pkae_package ip -> sk_raw:lbytes pkp.secret_key_length -> h0:mem -> h1:mem -> Type0
let coerce_skey_footprint #ip pkae_p sk_raw h0 h1 = ODH.coerce_dh_exp_footprint #odh_params ip sk_raw h0 h1

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
let coerce_skey #ip pkae_p sk_raw =
  let sk = ODH.coerce_dh_exp #odh_params ip sk_raw in
  sk

val get_log_rgn: (#ip:pkae_index_package) -> (pkae_p:pkae_package ip) -> Tot (rgn:erid)
let get_log_rgn #ip pkae_p = AE.get_log_rgn pkae_p.ap

// We need an explicit ciphertext type with valid_length predicate.
//val get_pp: pkae_p:pkae_package -> pp:plain_package{pp.flag == Flags.pkae /\ pp.valid_length}
//let get_pp #pp pkae_p = AE.get_ap_pp pkae_p.ap

#set-options "--z3rlimit 150 --max_ifuel 0 --max_fuel 0"
val get_log: (#ip:pkae_index_package) -> (pkae_p:pkae_package ip) -> GTot (Mem.message_log (compose_ip ip) pp (get_log_rgn pkae_p))
let get_log #ip pkae_p =
  let ap :AE.ae_package #pp (compose_ip ip) ae_params = pkae_p.ap in
  let rgn :erid = AE.get_log_rgn pkae_p.ap in
  let rgn' :erid = get_log_rgn pkae_p in
  assert(rgn' == rgn);
  let log : Mem.message_log (compose_ip ip) pp rgn = AE.get_ap_log #(compose_ip ip) #pp #ae_params ap in
  log

let nonce_is_unique (#ip:pkae_index_package) (pkae_p:pkae_package ip) i n h0 =
  Flags.model ==>
    (let log: Mem.i_message_log (compose_ip ip) pp (get_log_rgn pkae_p) = get_log pkae_p in
    forall c . MM.fresh log (i,n,c) h0)

#set-options "--z3rlimit 30 --max_ifuel 8 --max_fuel 8"
let extended_message_log
  (#ip:pkae_index_package)
  (pkae_p:pkae_package ip)
  (pk:pkey)
  (sk:skey{compatible_keys sk pk})
  (n:nonce pp)
  (c:cipher pp)
  (p:protected_plain #(compose_ip ip) pp (composed_id ip pk (get_pkey_from_skey sk)))
  (h0:mem) (h1:mem) =
  let i : id (compose_ip ip) = composed_id ip pk (get_pkey_from_skey sk) in
  let log_value: protected_plain #(compose_ip ip) pp i = p in
  //if Flags.model then
  //  let log_key: id (compose_ip ip)*nonce pp*cipher pp  = i,n,c in
  //  let log: Mem.i_message_log (compose_ip ip) pp (get_log_rgn pkae_p) = get_log pkae_p in
  //  //sel h1 log == MM.upd (sel h0 log) log_key p
  //           True
  //  /\ witnessed (MM.defined log log_key)
  //  ///\ witnessed (MM.contains log log_key p)
  //else
    True

#set-options "--z3rlimit 30 --max_ifuel 2 --max_fuel 2"
val encrypt_footprint:
  (#ip:pkae_index_package) ->
  (pkae_p:pkae_package ip) ->
  (pk:pkey) ->
  (sk:skey{compatible_keys sk pk}) ->
  (n:nonce pp) ->
  (c:cipher pp) ->
  (p:protected_plain #(compose_ip ip) pp (composed_id ip pk (get_pkey_from_skey sk))) ->
  (h0:mem) ->
  (h1:mem) ->
  Type0

let encrypt_footprint #ip pkae_p pk sk n c p h0 h1 =
  ODH.dh_op_memory_footprint pkae_p.op pk sk h0 h1
  /\ AE.encrypt_footprint #(compose_ip ip) pkae_p.ap h0 h1

let decrypt_footprint #ip pkae_p pk sk n c p h0 h1 =
  ODH.dh_op_memory_footprint pkae_p.op pk sk h0 h1
  /\ AE.decrypt_footprint pkae_p.ap h0 h1

//let enc_spec pkae_p p pk sk n = PKAE_Spec.cryptobox p n pk sk
//
//// Maybe require function to get cipher length from plain_length
//let enc_star pkae_p plain_length = random_bytes (plain_length+16)
//
//val dec_spec: pkae_p:pkae_package -> c:ciphertext -> pk:lbytes pkey_length -> sk:lbytes skey_length -> n:nonce -> option (p:plain (get_pp pkae_p))

//#set-options "--z3rlimit 100 --max_ifuel 1 --max_fuel 0"
//let dec_spec pkae_p c pk sk n =
//  let option_p:option (plain pkae_p.pp) = PKAE_Spec.cryptobox_open c n pk sk in
//  assert(pkae_p.pp == get_pp pkae_p);
//  match option_p with
//  | Some (p:plain (pkae_p.pp)) ->
//    let (p:plain (get_pp pkae_p)) = p in
//    admit()
//    //Some p
//  | None -> None
//  //let option_pp:option (plain (get_pp pkae_p)) = option_p in
//  //admit()

#set-options "--z3rlimit 30 --max_ifuel 2 --max_fuel 2"
val encrypt:
  #ip:pkae_index_package ->
  pkae_p:pkae_package ip ->
  pk:pkey ->
  sk:skey{compatible_keys sk pk} ->
  n:nonce pp ->
  p:protected_plain #(compose_ip ip) pp (composed_id pk (get_pkey_from_skey sk)) ->
  ST (cipher pp)
  (requires (fun h0 ->
    let i = composed_id pk (get_pkey_from_skey sk) in
    nonce_is_unique pkae_p i n h0
    /\ registered #(compose_ip ip) i
  ))
  (ensures (fun h0 c h1 ->
    let i = composed_id pk (get_pkey_from_skey sk) in
    encrypt_footprint #ip pkae_p pk sk n c p h0 h1
    /\ ((honest #(compose_ip ip) i /\ Flags.pkae) ==>
      c == pkp.pke_scheme.enc_star (Plain.length p))
    /\ ((corrupt #(compose_ip ip) i \/ ~(Flags.pkae)) ==>
      c == pkp.pke_scheme.enc (Plain.repr #(compose_ip ip) #pp  p) n (get_pkey_raw pk) (get_skey_raw sk))
    /\ extended_message_log #ip pkae_p i n c p h0 h1
  ))

#set-options "--z3rlimit 30 --max_ifuel 0 --max_fuel 0"
let encrypt #ip pkae_p pk sk n p =
  admit()

val decrypt: pkae_package:pkae_package -> pk:pkey -> sk:skey{ODH.get_share_raw pk <> ODH.get_share_raw (ODH.get_exp_share sk)} -> n:nonce -> c:ciphertext -> ST (option (p:protected_plain pp (ODH.create_id pk (ODH.get_exp_share sk))))
  (requires (fun h0 ->
    let i = ODH.create_id pk (ODH.get_exp_share sk) in
    match sel h0 pkae_package.ap_log i with
    | Some ap ->
      contains h0 (AE.get_ap_log ap)
    | None -> True
  ))
  (ensures (fun h0 c h1 ->
    let i = ODH.create_id pk (ODH.get_exp_share sk) in
    let both_honest = ODH.exp_hon sk && ODH.sh_hon pk in
    let kp_log = ODH.get_op_log pkae_package.op in
    match sel h0 pkae_package.ap_log i with
    | Some ap ->
      ((both_honest /\ ODH.get_flag()) ==>
        (MM.defined kp_log i h0 ==>
          h0 == h1)
        /\ (MM.fresh kp_log i h0 ==>
          modifies (Set.singleton (ODH.get_op_rgn pkae_package.op)) h0 h1))
      /\ ((~both_honest \/ ~(ODH.get_flag())) ==>
          h0 == h1)
    | None ->
      MM.defined pkae_package.ap_log i h1
      /\ (let ap = Some?.v (sel h1 pkae_package.ap_log i) in
        sel h1 pkae_package.ap_log == MM.upd (sel h0 pkae_package.ap_log) i ap
        /\ ((both_honest /\ ODH.get_flag()) ==>
            (MM.defined kp_log i h0 ==>
              modifies (Set.union (Set.singleton pkae_package.ap_rgn) (Set.singleton pkae_package.ap_log_rgn)) h0 h1)
            /\ (MM.fresh kp_log i h0 ==>
              modifies (Set.union (Set.singleton pkae_package.ap_rgn) (Set.union (Set.singleton pkae_package.ap_log_rgn) (Set.singleton (ODH.get_op_rgn pkae_package.op)))) h0 h1))
        /\ ((~both_honest \/ ~(ODH.get_flag())) ==>
            (modifies (Set.union (Set.singleton pkae_package.ap_rgn) (Set.singleton pkae_package.ap_log_rgn)) h0 h1)))
  ))

let decrypt pkae_package pk sk n c =
  let i = ODH.create_id pk (ODH.get_exp_share sk) in
  recall pkae_package.ap_log;
  let k = ODH.dh_op pkae_package.op pk sk in
  let ap =
    match get_ap_from_log pkae_package i with
    | Some ap ->
      ap
    | None ->
      let ap = AE.create_ae_package pkae_package.ap_rgn kp ae_params pp in
      MM.extend pkae_package.ap_log i ap;
      recall pkae_package.ap_log;
      AE.recall_log ap;
      ap
  in
  AE.decrypt ap k n c
