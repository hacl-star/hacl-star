module Box.PKAE

open FStar.Set
open FStar.Seq
open FStar.HyperStack
open FStar.HyperStack.ST

open FStar.Endianness

open Box.Plain

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

val ae_enc_star: n:(n:nat{AE_Spec.valid_plain_length n}) -> b:lbytes (n+16){AE_Spec.valid_cipher_length (n+16)}
let ae_enc_star n = Seq.append (random_bytes n) (random_bytes 16)

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

#set-options "--z3rlimit 300 --max_ifuel 1 --max_fuel 0"
noeq abstract type pkae_package (#pp:plain_package) (#pkp:pkae_parameters pp) (ip:index_package pkp) =
  | PKAE_P :
    pkae_rgn:erid ->
    kp: Key.key_package ip AE_Spec.keylen (AE.key AE_Spec.keylen) ->
    op: ODH.odh_package #ip #AE_Spec.keylen #(AE.key AE_Spec.keylen) kp odh_params ->
    ap: AE.ae_package kp ae_params ->
    pkae_package

#set-options "--z3rlimit 300 --max_ifuel 1 --max_fuel 0"
let create_pkae_package rgn pp =
  let pkae_rgn = new_region rgn in
  let ip = create_index_package pkae_rgn in
  //let pp = PP Flags.pkae AE_Spec.valid_plain_length in
  let kp = AE.create_ae_key_package ip AE_Spec.keylen in
  let op = ODH.create_odh_package pkae_rgn kp odh_params in
  let ap = AE.create_ae_package pkae_rgn kp ae_params in
  PKAE_P pkae_rgn ip kp op ap

let pkey = ODH.share odh_params
let get_pkey_raw = ODH.get_share_raw
let get_pkey_id pk = PK_id (ODH.get_share_raw pk)

let skey = ODH.exponent odh_params
let get_skey_raw = ODH.get_exponent_raw
let get_pkey_raw_from_skey_raw skey_raw = odh_params.ODH.exponentiate skey_raw odh_params.ODH.generator
let get_pkey_from_skey = ODH.get_exp_share
let get_skey_id sk = get_pkey_id (ODH.get_exp_share sk)

//let nonce = AE.nonce ae_params
//let ciphertext = AE.ciphertext ae_params

let get_index_package #pp pkae_p = pkae_p.ip

let gen_footprint #pp pkae_p h0 h1 = ODH.gen_dh_footprint pkae_p.ip odh_params h0 h1

let gen #pp pkae_p = ODH.gen_dh pkae_p.ip odh_params

let coerce_pkey_footprint #pp pkae_p pk_raw h0 h1 = ODH.coerce_dh_sh_footprint pkae_p.ip odh_params pk_raw h0 h1

let coerce_pkey #pp pkae_p pk_raw =
  let pk = ODH.coerce_dh_sh pkae_p.ip odh_params pk_raw in
  pk

let coerce_skey_footprint #pp pkae_p sk_raw h0 h1 = ODH.coerce_dh_exp_footprint pkae_p.ip odh_params sk_raw h0 h1

let coerce_skey #pp pkae_p sk_raw =
  let sk = ODH.coerce_dh_exp pkae_p.ip odh_params sk_raw in
  sk

let compose_ids pk1 pk2 = compose_id (pk1) pk2

//let compatible_keys pk sk = get_pkey_from_skey sk <> pk

//#set-options "--z3rlimit 5 --max_ifuel 0 --max_fuel 0"
//val create_key : pkae_p:pkae_package -> i:inst_id -> message_log_value i
//let create_key pkae_p i =
//  //assert(protected_plain pp i == AE.message_log_value pp i);
//  //assert(protected_plain pp i == message_log_value i);
//  let (ae_value : AE.message_log_value pp i) = coerce pkae_p.ip i (AE.zero_bytes (fun n -> true) 5) in
//  admit()
//  //let pkae_value : message_log_value i = ae_value in
//  //pkae_value

let get_log_rgn #pp pkae_p = AE.get_log_rgn pkae_p.ap

// We need an explicit ciphertext type with valid_length predicate.
//val get_pp: pkae_p:pkae_package -> pp:plain_package{pp.flag == Flags.pkae /\ pp.valid_length}
//let get_pp #pp pkae_p = AE.get_ap_pp pkae_p.ap

#set-options "--z3rlimit 300 --max_ifuel 1 --max_fuel 0"
//val get_log: pkae_p:pkae_package -> GTot (AE.ae_message_log ae_params (AE.get_ap_pp pkae_p.ap) (AE.get_log_rgn pkae_p.ap))
//val get_log: pkae_p:pkae_package -> GTot (AE.ae_message_log ae_params (AE.get_ap_pp pkae_p.ap) (AE.get_log_rgn pkae_p.ap))
let get_log #pp pkae_p =
  assert(ae_params.AE.scheme.AE.pp == pp);
  admit()
  //AE.get_ap_log #pkae_p.ip #_ #_ #ae_params pkae_p.ap

let encrypt_footprint pkae_p pk sk n c p h0 h1 =
  ODH.dh_op_memory_footprint pkae_p.op pk sk h0 h1
  /\ AE.encrypt_footprint pkae_p.ap h0 h1

let decrypt_footprint pkae_p pk sk n c p h0 h1 =
  ODH.dh_op_memory_footprint pkae_p.op pk sk h0 h1
  /\ AE.decrypt_footprint pkae_p.ap h0 h1

let enc_spec pkae_p p pk sk n = PKAE_Spec.cryptobox p n pk sk

// Maybe require function to get cipher length from plain_length
let enc_star pkae_p plain_length = random_bytes (plain_length+16)

val dec_spec: pkae_p:pkae_package -> c:ciphertext -> pk:lbytes pkey_length -> sk:lbytes skey_length -> n:nonce -> option (p:plain (get_pp pkae_p))

#set-options "--z3rlimit 100 --max_ifuel 1 --max_fuel 0"
let dec_spec pkae_p c pk sk n =
  let option_p:option (plain pkae_p.pp) = PKAE_Spec.cryptobox_open c n pk sk in
  assert(pkae_p.pp == get_pp pkae_p);
  match option_p with
  | Some (p:plain (pkae_p.pp)) ->
    let (p:plain (get_pp pkae_p)) = p in
    admit()
    //Some p
  | None -> None
  //let option_pp:option (plain (get_pp pkae_p)) = option_p in
  //admit()

#set-options "--z3rlimit 300 --max_ifuel 0 --max_fuel 0"
val encrypt: pkae_package:pkae_package -> pk:pkey -> sk:skey{ODH.get_share_raw pk <> ODH.get_share_raw (ODH.get_exp_share sk)} -> n:nonce -> p:protected_plain pp (ODH.create_id pk (ODH.get_exp_share sk)) -> ST ciphertext
  (requires (fun h0 ->
    let i = ODH.create_id pk (ODH.get_exp_share sk) in
    match sel h0 pkae_package.ap_log i with
    | Some ap ->
      contains h0 (AE.get_ap_log ap)
      /\ AE.nonce_is_unique ap n h0
    | None -> True
  ))
  (ensures (fun h0 c h1 ->
    let i = ODH.create_id pk (ODH.get_exp_share sk) in
    let both_honest = ODH.exp_hon sk && ODH.sh_hon pk in
    let kp_log = ODH.get_op_log pkae_package.op in
    // Describe ap_log state
    Some? (sel h1 pkae_package.ap_log i)
    /\ (let ap = Some?.v (sel h1 pkae_package.ap_log i) in
    (if Some? (sel h0 pkae_package.ap_log i) then
      sel h1 pkae_package.ap_log == sel h0 pkae_package.ap_log
      /\ sel h1 (AE.get_ap_log ap) == MM.upd (sel h0 (AE.get_ap_log ap)) (n,c) p
    else
      sel h1 pkae_package.ap_log == MM.upd (sel h0 pkae_package.ap_log) i ap
      /\ (forall n' . n' =!= n ==> AE.nonce_is_unique ap n' h1))
    // Describe modified memory regions
    /\ (let modified_regions_ap_op = Set.union
        (AE.encrypt_modified_regions ap)
        (ODH.dh_op_modified_regions pkae_package.op pk sk h0)
      in
      let modified_regions_extend_ap_log = Set.union (Set.singleton pkae_package.ap_rgn) (Set.singleton pkae_package.ap_log_rgn) in
      let modified_regions =
        if Some? (sel h0 pkae_package.ap_log i) then
          modified_regions_ap_op
        else
          Set.union modified_regions_ap_op modified_regions_extend_ap_log
      in
      modifies modified_regions h0 h1)
    /\ ODH.dh_op_log_change pkae_package.op pk sk h0 h1
    // Describe functionality
    /\ (let k =
        if both_honest && ODH.get_flag() then
          Some?.v (MM.sel (sel h1 (ODH.get_op_log pkae_package.op)) i)
        else
          ODH.(odh_params.hash (odh_params.exponentiate (ODH.get_exponent_raw sk) (ODH.get_share_raw pk)))
      in
      ODH.dh_op_functional_spec pkae_package.op pk sk k h1
    )
    /\ ((both_honest /\ ODH.get_flag()) ==>
        (let k = Some?.v (MM.sel (sel h1 (ODH.get_op_log pkae_package.op)) i) in
        AE.encrypt_functional_spec ap k n c p)
      )
      // In case we have a dishonest key or we don't idealize, we can't guarantee anything.
    )
  ))

#set-options "--z3rlimit 300 --max_ifuel 0 --max_fuel 0"
let encrypt pkae_package pk sk n p =
  let i = ODH.create_id pk (ODH.get_exp_share sk) in
  recall pkae_package.ap_log;
  let k = ODH.dh_op pkae_package.op pk sk in
  let h1 = get() in
  ODH.recall_op_log pkae_package.op;
  let ap =
    match get_ap_from_log pkae_package i with
    | Some ap ->
      ap
    | None ->
      let ap = AE.create_ae_package pkae_package.ap_rgn kp ae_params pp in
      MM.extend pkae_package.ap_log i ap;
      ap
  in
  let c = AE.encrypt ap k n p in
  //assert(
  //    let both_honest = ODH.exp_hon sk && ODH.sh_hon pk in
  //    (both_honest /\ ODH.get_flag()) ==>
  //      (let k' = Some?.v (MM.sel (sel h1 (ODH.get_op_log pkae_package.op)) i) in
  //      AE.encrypt_functional_spec ap k n c p
  //      )
  //    );
  //    admit();
  //assert(AE.encrypt_functional_spec ap k n c p);
  c

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
