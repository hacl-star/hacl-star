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
let ae_package_log_value (i:ODH.id) = (ap:AE.ae_package #ODH.id #i #AE_Spec.keylen kp ae_params pp)
let ae_package_log_range (k:ae_package_log_key) = ae_package_log_value k
let ae_package_log_inv (f:MM.map' (ae_package_log_key) (ae_package_log_range))  = True

let ae_package_log (rgn:erid) =
  MM.t rgn (ae_package_log_key) (ae_package_log_range) (ae_package_log_inv)

let zero_nonce = Seq.create H.noncelen (UInt8.uint_to_t 0)
let hsalsa20_hash input = H.hsalsa20 input zero_nonce

let odh_params = ODH.OP (ODH_Spec.serialized_point_length) (ODH_Spec.scalar_length) (H.keylen) (ODH_Spec.base_point) (ODH_Spec.scalarmult) (hsalsa20_hash)

noeq abstract type pkae_package =
  | PKAE_P :
    op_rgn:erid ->
    op: ODH.odh_package #AE_Spec.keylen #(AE.key AE_Spec.keylen #ODH.id) kp odh_params ->
    ap_log_rgn:erid ->
    ap_log: ae_package_log ap_log_rgn ->
    pkae_package

val create_pkae_package: rgn:erid -> ST pkae_package
  (requires (fun h0 -> True))
  (ensures (fun h0 pkae_p h1 ->
    modifies (Set.singleton rgn) h0 h1
  ))
let create_pkae_package rgn =
  let pkae_rgn = new_region rgn in
  let odh_rgn = new_region pkae_rgn in
  let ap_log_rgn = new_region pkae_rgn in
  let op = ODH.create_odh_package kp odh_params odh_rgn in
  let ap_log = MM.alloc #ap_log_rgn #ae_package_log_key #ae_package_log_range #ae_package_log_inv in
  PKAE_P odh_rgn op ap_log_rgn ap_log

let gen = ODH.gen_dh odh_params

val encrypt: #id:eqtype -> #i:id -> #key_length:(n:nat{n<=32}) -> #kp:KEY.key_package #id key_length (key key_length #id) -> #aparams:ae_parameters{key_length = aparams.keylength} -> #pp:plain_package{ valid_ae_plain_package aparams pp} ->  ap:ae_package #id #i #key_length kp aparams pp -> k:key key_length i -> n:nonce aparams.nonce_length -> p:protected_plain pp i -> ST ciphertext

let encrypt = ODH.odh_package
