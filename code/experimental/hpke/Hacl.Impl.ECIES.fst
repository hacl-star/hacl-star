module Hacl.Impl.ECIES

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.LoopCombinators

module ST = FStar.HyperStack.ST
module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators
module Spec = Spec.ECIES


val crypto_random: output:buffer uint8 -> len:size_t{v len > 0 /\ length output == v len} ->
  Stack bool
  (requires (fun h -> live h output))
  (ensures  (fun h0 _ h1 -> modifies1 output h0 h1))

let crypto_random output len =
  push_frame ();
  let tmp = create len (u8 0xAB) in
  copy output tmp;
  pop_frame ();
  true



///
/// Curve25519, AES128_GCM and HKDF_SHA2_256
///

let ciphersuite = Spec.DH.DH_Curve25519, Spec.AEAD.AEAD_AES128_GCM, Spec.Hash.SHA2_256
let id_of_ciphersuite = u8 0

///
/// Constants
///

inline_for_extraction
let size_id_of_ciphersuite = size 1

inline_for_extraction
let size_nonce = size (Spec.ECIES.size_nonce ciphersuite)

inline_for_extraction
let size_aead_key = size 32

inline_for_extraction
let size_aead_nonce = size 16

inline_for_extraction
let size_key = size (Spec.ECIES.size_key ciphersuite)

inline_for_extraction
let size_key_dh = size (Spec.ECIES.size_key_dh ciphersuite)

inline_for_extraction
let size_ecies_secret = 1ul +. size_key +. 2ul *. size_key_dh

inline_for_extraction
let size_context = size 32

inline_for_extraction
let size_info = size_id_of_ciphersuite + (size Spec.ECIES.size_label_key) + size_context



///
/// Types
///

type key_public_p = lbuffer uint8 size_key_dh
type key_private_p = lbuffer uint8 size_key_dh
type key_p = lbuffer uint8 size_key

///
/// Implementation
///

let const_label_nonce: x:ilbuffer size_t (size Spec.ECIES.size_label_nonce){witnessed x Spec.ECIES.label_nonce /\ recallable x} =
  createL_global Spec.ECIES.label_nonce_list

let const_label_key: x:ilbuffer size_t (size Spec.ECIES.size_label_key){witnessed x Spec.ECIES.label_key /\ recallable x} =
  createL_global Spec.ECIES.label_key_list



val encap:
    output: lbuffer uint8 size_ecies_secret
  -> pk: key_public_p
  -> context: lbuffer uint8 size_context ->
  Stack unit
  (requires (fun h -> live h output /\ live h pk /\ live h context
                 /\ disjoint output pk /\ disjoint output context))
  (ensures  (fun h0 _ h1 -> modifies1 output h0 h1))

let encap output pk context =
  push_frame ();
  let flag = sub output (size 0) (size 1) in
  let key = sub output (size 1) size_key in
  let epk = sub output (1ul +. size_key) size_key_dh in
  let esk = create size_key_dh (u8 0) in
  let extracted = create size_key (u8 0) in
  let secret = create size_key (u8 0) in
  let salt = create (2ul *. size_key_dh) (u8 0) in
  let info = create size_info (u8 0) in
  let res0 = crypto_random esk size_key_dh in
  (* let epk = DH.secret_to_public (curve_of_cs cs) esk in *)
  Hacl.Curve25519_64.secret_to_public epk esk;
  Hacl.Curve25519_64.ecdh secret esk pk;
  (* let salt = epk @| pk in *)
  update_sub salt (size 0) size_key_dh epk;
  update_sub salt size_key_dh size_key_dh pk;
  (* let extracted = HKDF.hkdf_extract (hash_of_cs cs) salt secret in *)
  Hacl.HKDF_SHA2_256.hkdf_extract extracted salt (2ul *. size_key_dh) secret size_key;
  (* let info = (id_of_cs cs) @| label_key @| context in *)
  info.(0ul) <- id_of_ciphersuite;
  update_sub info (size 1) (size Spec.ECIES.size_label_key) const_label_key;
  update_sub #MUT #uint8 #size_info info (1ul +. Spec.ECIES.size_label_key) size_context context;
  (* let key = HKDF.hkdf_expand (hash_of_cs cs) extracted info (size_key cs) in *)
  Hacl.HKDF_SHA2_256.hkdf_expand key extracted size_key info size_info size_key;
  if res0 then output.(0ul) <- (u8 0) else output.(0ul) <- (u8 1);
  pop_frame ()


val decap:
    output: lbuffer uint8 (size_key +. 1ul)
  -> kpriv: key_private_p
  -> eph_kpub: key_public_p
  -> context: lbuffer uint8 size_context ->
  Stack unit
  (requires (fun h -> live h output /\ live h kpriv /\ live h eph_kpub /\ live h context))
  (ensures  (fun h0 _ h1 -> modifies1 output h0 h1))

let decap output sk epk context =
  push_frame();
  let pk = create size_key_dh (u8 0) in
  let salt = create (2ul *. size_key_dh) (u8 0) in
  let info = create size_info (u8 0) in
  let extracted = create size_key (u8 0) in
  let flag = sub output (size 0) (size 1) in
  let secret = sub output (size 1) size_ecies_secret in
  (* let pk = DH.secret_to_public (curve_of_cs cs) sk in *)
  Hacl.Curve25519_64.secret_to_public pk sk;
  Hacl.Curve25519_64.ecdh secret sk epk;
  (* let salt = epk @| pk in *)
  update_sub salt (size 0) size_key_dh epk;
  update_sub salt size_key_dh size_key_dh pk;
  (* let extracted = HKDF.hkdf_extract (hash_of_cs cs) salt secret in *)
  Hacl.HKDF_SHA2_256.hkdf_extract extracted salt (2ul *. size_key_dh) secret size_ecies_secret;
  (* let info = (id_of_cs cs) @| label_key @| context in *)
  info.(0ul) <- id_of_ciphersuite;
  update_sub info (size 1) (size Spec.ECIES.size_label_key) const_label_key;
  update_sub #MUT #uint8 #size_info info (1ul +. size Spec.ECIES.size_label_key) size_context context;
  (* let key = HKDF.hkdf_expand (hash_of_cs cs) extracted info (size_key cs) in *)
  Hacl.HKDF_SHA2_256.hkdf_expand secret extracted size_key info size_info size_key;
  pop_frame()


val encrypt:
    output: buffer uint8
  -> sk: lbuffer uint8 size_key_dh
  -> input: buffer uint8
  -> len: size_t{v len == length input}
  -> aad: buffer uint8
  -> alen: size_t{v alen == length aad}
  -> counter: uint32 ->
  Stack unit
  (requires (fun h -> live h output /\ live h sk /\ live h input /\ live h aad
                 /\ disjoint output sk /\ disjoint output input /\ disjoint output aad))
  (ensures  (fun h0 _ h1 -> modifies1 output h0 h1))

let encrypt output sk input len aad alen counter =
  push_frame();
  let context = create 22ul (u128 0) in
  let ctr8 = create (numbytes U32) (u8 0) in
  let aead_nonce = create size_aead_nonce (u8 0) in
  (* let key = sub sk (size 0) size_ *)
  let key = sub sk 0ul size_aead_key in
  (* let nonce = sub sk klen (size_nonce cs - numbytes U32) in *)
  let nonce = sub sk size_aead_key (size_aead_nonce - numbytes U32) in
  let ctr = uint_to_bytes_le ctr8 counter in
  (* let aead_nonce = (nonce @| ctr) in *)
  update_sub aead_nonce 0ul (size_aead_nonce - numbytes U32) nonce;
  update_sub aead_nonce (size_aead_nonce - numbytes U32) (numbytes U32) ctr8;
  Hacl.AesGCM.NI.aes128_gcm_init context key aead_nonce;
  (* AEAD.aead_encrypt (aead_of_cs cs) key (nonce @| ctr) input aad *)
  Hacl.AesGCM.NI.aes128_gcm_encrypt context len output input alen aad;
  pop_frame ()


val decrypt:
    output: buffer uint8
  -> sk: lbuffer uint8 size_key
  -> input: buffer uint8
  -> len: uint32{length input == v len}
  -> aad: buffer uint8
  -> alen: size_t{v alen == length aad}
  -> counter:uint32 ->
  Stack bool
  (requires (fun h -> live h output /\ live h sk /\ live h input /\ live h aad
                 /\ disjoint output sk /\ disjoint output input /\ disjoint output aad))
  (ensures  (fun h0 _ h1 -> modifies1 output h0 h1))

let decrypt output sk input len aad alen counter =
  push_frame ();
  let context = create 22ul (u128 0) in
  let ctr8 = create (numbytes U32) (u8 0) in
  let aead_nonce = create size_aead_nonce (u8 0) in
  (* let key = sub sk (size 0) size_ *)
  let key = sub sk 0ul size_aead_key in
  (* let nonce = sub sk klen (size_nonce cs - numbytes U32) in *)
  let nonce = sub sk size_aead_key (size_aead_nonce - numbytes U32) in
  let ctr = uint_to_bytes_le ctr8 counter in
  (* let aead_nonce = (nonce @| ctr) in *)
  update_sub aead_nonce 0ul (size_aead_nonce - numbytes U32) nonce;
  update_sub aead_nonce (size_aead_nonce - numbytes U32) (numbytes U32) ctr8;
  Hacl.AesGCM.NI.aes128_gcm_init context key aead_nonce;
  let r = Hacl.AesGCM.NI.aes128_gcm_decrypt context len output input alen aad in
  pop_frame ();
  r
