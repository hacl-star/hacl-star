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
module H = Spec.HSalsa20

assume val random_bytes: n:(n:nat{n<=32}) -> unit -> lbytes n

assume val pkae_flag: bool

#set-options "--z3rlimit 300 --max_ifuel 1 --max_fuel 1"
// For some reason it doesn't verify if there is an additional refinement on the output of secretbox_open_easy
let secretbox_scheme =
  AE.ES #(AE_Spec.keylen) #(AE_Spec.noncelen) (fun n -> n / Spec.Salsa20.blocklen < pow2 32) (fun n -> n >= 16 && (n - 16) / Spec.Salsa20.blocklen < pow2 32) (random_bytes 32) AE_Spec.secretbox_easy AE_Spec.secretbox_open_easy

let ae_params = AE.GP AE_Spec.keylen AE_Spec.noncelen secretbox_scheme

let pp = PP (AE.get_ae_flagGT ae_params) (fun n -> n / Spec.Salsa20.blocklen < pow2 32)

let kp = AE.create_ae_key_package ODH.id AE_Spec.keylen

let ae_package_log_key = i:ODH.id
let ae_package_log_value (rgn:erid) (i:ODH.id) = (ap:AE.ae_package #ODH.id #i #AE_Spec.keylen kp ae_params pp{extends (AE.get_ap_rgn ap) rgn})
let ae_package_log_range (rgn:erid) (k:ae_package_log_key) = ae_package_log_value rgn k
let ae_package_log_inv (rgn:erid) (f:MM.map' (ae_package_log_key) (ae_package_log_range rgn))  = True

let ae_package_log (log_rgn:erid) (ap_rgn:erid) =
  MM.t log_rgn (ae_package_log_key) (ae_package_log_range ap_rgn) (ae_package_log_inv ap_rgn)

let zero_nonce = Seq.create H.noncelen (UInt8.uint_to_t 0)
let hsalsa20_hash input = H.hsalsa20 input zero_nonce

let odh_params = ODH.OP (ODH_Spec.serialized_point_length) (ODH_Spec.scalar_length) (H.keylen) (ODH_Spec.base_point) (ODH_Spec.scalarmult) (hsalsa20_hash)

noeq abstract type pkae_package =
  | PKAE_P :
    op_rgn:erid ->
    op: ODH.odh_package #AE_Spec.keylen #(AE.key AE_Spec.keylen #ODH.id) kp odh_params{extends (ODH.get_op_rgn op) op_rgn} ->
    ap_log_rgn:erid{disjoint op_rgn ap_log_rgn} ->
    ap_rgn:erid{disjoint op_rgn ap_rgn /\ disjoint ap_rgn ap_log_rgn /\ disjoint (ODH.get_op_rgn op) ap_rgn} ->
    ap_log: ae_package_log ap_log_rgn ap_rgn ->
    pkae_package

val create_pkae_package: rgn:erid -> ST pkae_package
  (requires (fun h0 -> True))
  (ensures (fun h0 pkae_p h1 ->
    modifies (Set.singleton rgn) h0 h1
    /\ extends (ODH.get_op_rgn pkae_p.op) pkae_p.op_rgn
  ))
let create_pkae_package rgn =
  let pkae_rgn = new_region rgn in
  let odh_rgn = new_region pkae_rgn in
  let op = ODH.create_odh_package kp odh_params odh_rgn in
  let ap_log_rgn = new_region pkae_rgn in
  let ap_rgn = new_region pkae_rgn in
  let ap_log = MM.alloc #ap_log_rgn #ae_package_log_key #(ae_package_log_range ap_rgn) #(ae_package_log_inv ap_rgn) in
  PKAE_P odh_rgn op ap_log_rgn ap_rgn ap_log

let pkey = ODH.share odh_params
let skey = ODH.exponent odh_params
let nonce = AE.nonce ae_params
let ciphertext = AE.ciphertext ae_params
let gen = ODH.gen_dh odh_params

#set-options "--z3rlimit 300 --max_ifuel 0 --max_fuel 0"
val get_ap_from_log: pkae_p:pkae_package -> i:ODH.id -> ST (option (ap:ae_package_log_value pkae_p.ap_rgn i))
  (requires (fun h0 -> True))
  (ensures (fun h0 ap h1 ->
    (match sel h0 pkae_p.ap_log i with
      | Some ap ->
        contains h1 (AE.get_ap_log ap)
        /\ MM.defined pkae_p.ap_log i h1
        /\ MM.contains pkae_p.ap_log i ap h1
        /\ witnessed (MM.defined pkae_p.ap_log i)
        /\ witnessed (MM.contains pkae_p.ap_log i ap)
      | None -> MM.fresh pkae_p.ap_log i h1)
    /\ h0 == h1
    /\ ap == MM.sel (sel h1 pkae_p.ap_log) i
  ))

let get_ap_from_log pkae_p i =
  match MM.lookup pkae_p.ap_log i with
  | Some ap ->
    AE.recall_log ap;
    Some ap
  | None -> None


//#set-options "--z3rlimit 300 --max_ifuel 0 --max_fuel 0"
//val nonce_freshness_framing_lemma: pkae_p:pkae_package -> i:ODH.id -> n:nonce -> h0:mem -> h1:mem -> Lemma
//  (requires (
//    //((modifies (Set.singleton (ODH.get_op_rgn pkae_p.op)) h0 h1 /\ (extends (ODH.get_op_rgn pkae_p.op) pkae_p.op_rgn)) \/ h0 == h1)
//    (modifies (Set.singleton (ODH.get_op_rgn pkae_p.op)) h0 h1 \/ h0 == h1)
//    /\ extends (ODH.get_op_rgn pkae_p.op) pkae_p.op_rgn
//    /\ disjoint (ODH.get_op_rgn pkae_p.op) pkae_p.ap_log_rgn
//    /\ contains h0 pkae_p.ap_log
//    /\ (match sel h0 pkae_p.ap_log i with
//      | Some ap -> contains h0 (AE.get_ap_log ap)
//      | None -> True)
//  ))
//  (ensures (
//    contains h1 pkae_p.ap_log
//    /\ (match sel h0 pkae_p.ap_log i with
//      | Some ap_old ->
//        let ap_new = Some?.v (sel h1 pkae_p.ap_log i) in
//        AE.get_ap_log ap_old == AE.get_ap_log ap_new
//        /\ contains h1 (AE.get_ap_log ap_new)
//      | None -> True)
//    ///\ (let ap_option_new = sel h1 pkae_p.ap_log i in
//    //ap_option_new == ap_option_old
//    ///\ (Some? ap_option_new)
//    ///\ AE.get_ap_log (Some?.v ap_option_new) == AE.get_ap_log (Some?.v ap_option_old))
//  ))
//let nonce_freshness_framing_lemma pkae_p i n h0 h1 = ()

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
    match sel h0 pkae_package.ap_log i with
    | Some ap ->
      ((both_honest /\ ODH.get_flag()) ==>
        (MM.defined kp_log i h0 ==>
          modifies (Set.singleton (AE.get_ap_rgn ap)) h0 h1)
        /\ (MM.fresh kp_log i h0 ==>
          modifies (Set.union (Set.singleton (AE.get_ap_rgn ap)) (Set.singleton (ODH.get_op_rgn pkae_package.op))) h0 h1))
      /\ ((~both_honest \/ ~(ODH.get_flag())) ==>
          (modifies (Set.singleton (AE.get_ap_rgn ap)) h0 h1))
    | None ->
      MM.defined pkae_package.ap_log i h1
      /\ (let ap = Some?.v (sel h1 pkae_package.ap_log i) in
        sel h1 pkae_package.ap_log == MM.upd (sel h0 pkae_package.ap_log) i ap
        /\ ((both_honest /\ ODH.get_flag()) ==>
            (MM.defined kp_log i h0 ==>
              modifies (Set.union (Set.singleton pkae_package.ap_rgn) (Set.union (Set.singleton pkae_package.ap_log_rgn) (Set.singleton (AE.get_ap_rgn ap)))) h0 h1)
            /\ (MM.fresh kp_log i h0 ==>
              modifies (Set.union (Set.singleton pkae_package.ap_rgn) (Set.union (Set.singleton pkae_package.ap_log_rgn) (Set.union (Set.singleton (AE.get_ap_rgn ap)) (Set.singleton (ODH.get_op_rgn pkae_package.op))))) h0 h1))
        /\ ((~both_honest \/ ~(ODH.get_flag())) ==>
            (modifies (Set.union (Set.singleton pkae_package.ap_rgn) (Set.union (Set.singleton pkae_package.ap_log_rgn) (Set.singleton (AE.get_ap_rgn ap)))) h0 h1)))
  ))

#set-options "--z3rlimit 500 --max_ifuel 0 --max_fuel 0"
let encrypt pkae_package pk sk n p =
  let i = ODH.create_id pk (ODH.get_exp_share sk) in
  recall pkae_package.ap_log;
  let k = ODH.dh_op pkae_package.op pk sk in
  let ap =
    match get_ap_from_log pkae_package i with
    | Some ap ->
      ap
    | None ->
      let h0 = get() in
      let ap = AE.create_ae_package pkae_package.ap_rgn kp ae_params pp in
      let h1 = get() in
      MM.extend pkae_package.ap_log i ap;
      recall pkae_package.ap_log;
      AE.recall_log ap;
      //assert(
        //let both_honest = ODH.exp_hon sk && ODH.sh_hon pk in
        //(~both_honest \/ ~(ODH.get_flag())) ==>
          //(modifies (Set.singleton pkae_package.ap_rgn) h0 h1)
          ////(modifies (Set.singleton (AE.get_ap_rgn ap)) h0 h1)
          ////(modifies (Set.singleton pkae_package.ap_log_rgn) h0 h1)
          ////(modifies (Set.union (Set.singleton pkae_package.ap_log_rgn) (Set.singleton (AE.get_ap_rgn ap))) h0 h1)
          //);
      ap
  in
  AE.encrypt ap k n p

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
