module Hacl.Impl.HPKE

open FStar.HyperStack
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer
open FStar.Mul

module S = Spec.Agile.HPKE
module SDH = Spec.Agile.DH
module DH = Hacl.Impl.Generic.DH
module HKDF = Hacl.Impl.Generic.HKDF
module AEAD = Hacl.Impl.Generic.AEAD

#set-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
let psk (cs:S.ciphersuite) = lbuffer uint8 (size (S.size_psk cs))

inline_for_extraction noextract
let nhash_length (cs:S.ciphersuite) : (s:size_t{v s == S.size_psk cs}) =
  match S.hash_of_cs cs with
  | Spec.Agile.Hash.SHA2_256 -> 32ul
  | Spec.Agile.Hash.SHA2_512 -> 64ul

inline_for_extraction noextract
let nsize_dh_public (cs:S.ciphersuite) : (s:size_t{v s == S.size_dh_public cs}) =
  match S.curve_of_cs cs with
  | SDH.DH_Curve25519 -> 32ul
  | SDH.DH_Curve448 -> 56ul
  | SDH.DH_P256 -> 64ul

inline_for_extraction noextract
let nsize_aead_key (cs:S.ciphersuite) : (s:size_t{v s == S.size_aead_key cs}) =
  match S.aead_of_cs cs with
  | Spec.Agile.AEAD.AES128_GCM -> 16ul
  | Spec.Agile.AEAD.AES256_GCM -> 32ul
  | Spec.Agile.AEAD.CHACHA20_POLY1305 -> 32ul

inline_for_extraction noextract
let nsize_aead_nonce (cs:S.ciphersuite) : (s:size_t{v s == S.size_aead_nonce cs}) =
  match S.aead_of_cs cs with
  | Spec.Agile.AEAD.AES128_GCM -> 12ul
  | Spec.Agile.AEAD.AES256_GCM -> 12ul
  | Spec.Agile.AEAD.CHACHA20_POLY1305 -> 12ul


val encap:
     #cs:S.ciphersuite
  -> o_zz: key_dh_public cs
  -> o_pkE: key_dh_public cs
  -> skE: key_dh_secret cs
  -> pkR: key_dh_public cs
  -> ST unit
    (requires fun h0 ->
      live h0 o_zz /\ live h0 o_pkE /\
      live h0 skE /\ live h0 pkR /\
      disjoint o_zz skE /\ disjoint o_zz pkR /\
      disjoint o_zz o_pkE /\ disjoint o_pkE skE /\ disjoint o_pkE pkR)
    (ensures fun h0 _ h1 -> modifies (loc o_zz |+| loc o_pkE) h0 h1 /\
      (let zz, pkE = S.encap cs (as_seq h0 skE) (as_seq h0 pkR) in
       as_seq h1 o_zz == zz /\ as_seq h1 o_pkE == pkE))

[@ Meta.Attribute.inline_]
let encap #cs o_zz o_pkE skE pkR =
  DH.secret_to_public #cs o_pkE skE;
  DH.scalarmult #cs skE pkR o_zz

val decap:
     #cs:S.ciphersuite
  -> o_pkR: key_dh_public cs
  -> pkE: key_dh_public cs
  -> skR: key_dh_secret cs
  -> ST unit
    (requires fun h0 ->
      live h0 o_pkR /\ live h0 pkE /\ live h0 skR /\
      disjoint o_pkR pkE /\ disjoint o_pkR skR)
    (ensures fun h0 _ h1 -> modifies (loc o_pkR) h0 h1 /\
      as_seq h1 o_pkR == S.decap cs (as_seq h0 pkE) (as_seq h0 skR))

[@ Meta.Attribute.inline_ ]
let decap #cs o_pkR pkE skR = DH.scalarmult #cs skR pkE o_pkR

val build_context_default:
     #cs:S.ciphersuite
  -> pkE: key_dh_public cs
  -> pkR: key_dh_public cs
  -> pkI: key_dh_public cs
  -> infolen:size_t {v infolen <= S.max_pskID}
  -> info:lbuffer uint8 infolen
  -> output:lbuffer uint8 (size (7 + (3 * S.size_dh_public cs) + v infolen))
  -> ST unit
    (requires fun h0 ->
      live h0 pkE /\ live h0 pkR /\
      live h0 pkI /\ live h0 info)
    (ensures fun h0 _ h1 -> modifies (loc output) h0 h1 /\
      as_seq h1 output == S.build_context cs S.Base (as_seq h0 pkE) (as_seq h0 pkR) (as_seq h0 pkI) S.default_pskId (as_seq h0 info))

let build_context_default #cs pkE pkR pkI infolen info output = admit()

noextract inline_for_extraction
val ks_derive_default_aux:
     #cs:S.ciphersuite
  -> pkR:key_dh_public cs
  -> zz:key_dh_public cs
  -> pkE:key_dh_public cs
  -> infolen: size_t{v infolen <= S.max_info}
  -> info: lbuffer uint8 infolen
  -> o_key: key_aead cs
  -> o_nonce: nonce_aead cs
  -> context_len:size_t{v context_len == 7 + (3 * S.size_dh_public cs) + v infolen}
  -> context:lbuffer uint8 context_len
  -> secret:lbuffer uint8 (nhash_length cs)
  -> pkI:lbuffer uint8 (nsize_dh_public cs)
  -> psk:lbuffer uint8 (nhash_length cs)
  -> label_key:lbuffer uint8 8ul
  -> label_nonce:lbuffer uint8 10ul
  -> tmp:lbuffer uint8 (10ul +. context_len)
  -> ST unit
       (requires fun h0 ->
         live h0 pkR /\ live h0 zz /\ live h0 pkE /\
         live h0 info /\ live h0 o_key /\ live h0 o_nonce /\
         live h0 context /\ live h0 secret /\ live h0 pkI /\
         live h0 psk /\ live h0 tmp /\ live h0 label_key /\ live h0 label_nonce /\
         disjoint o_key o_nonce /\ disjoint secret psk /\ disjoint secret zz /\
         disjoint context zz /\ disjoint context psk /\ disjoint context secret /\
         disjoint tmp label_key /\ disjoint tmp label_nonce /\ disjoint tmp context /\
         disjoint label_key context /\ disjoint label_key secret /\
         disjoint label_nonce o_key /\ disjoint label_nonce context /\
         disjoint label_nonce secret /\
         disjoint secret tmp /\ disjoint o_key tmp /\
         disjoint o_key secret /\ disjoint o_nonce secret /\
         as_seq h0 label_key `Seq.equal` S.label_key /\
         as_seq h0 label_nonce `Seq.equal` S.label_nonce /\
         as_seq h0 psk `Seq.equal` S.default_psk cs /\
         as_seq h0 pkI `Seq.equal` S.default_pkI cs)
       (ensures fun h0 _ h1 -> modifies (loc o_nonce |+| loc o_key |+| loc tmp |+| loc context |+| loc secret) h0 h1 /\
         (let keyIR, nonceIR = S.ks_derive cs S.Base (as_seq h0 pkR) (as_seq h0 zz) (as_seq h0 pkE) (as_seq h0 info) None None in
         as_seq h1 o_key == keyIR /\ as_seq h1 o_nonce == nonceIR))

#set-options "--z3rlimit 100"

noextract inline_for_extraction
[@ Meta.Attribute.inline_]
let ks_derive_default_aux #cs pkR zz pkE infolen info o_key o_nonce context_len context secret pkI psk label_key label_nonce tmp =
  build_context_default pkE pkR pkI infolen info context;
  let h0 = get() in
  HKDF.hkdf_extract #cs secret psk (nhash_length cs) zz (nsize_dh_public cs);
  let info_key = sub tmp 2ul (8ul +. context_len) in
  copy (sub info_key 0ul 8ul) label_key;
  copy (sub info_key 8ul context_len) context;
  (**) let h1 = get() in
  (**) assert (as_seq h1 info_key `Seq.equal` (S.label_key `Seq.append` as_seq h0 context));
  HKDF.hkdf_expand #cs o_key secret (nhash_length cs) info_key (8ul +. context_len) (nsize_aead_key cs);
  copy (sub tmp 0ul 10ul) label_nonce;
  (**) let h2 = get() in
  (**) assert (as_seq h2 tmp `Seq.equal` (S.label_nonce `Seq.append` as_seq h0 context));
  HKDF.hkdf_expand #cs o_nonce secret (nhash_length cs) tmp (10ul +. context_len) (nsize_aead_nonce cs)

val ks_derive_default:
     #cs:S.ciphersuite
  -> pkR:key_dh_public cs
  -> zz:key_dh_public cs
  -> pkE:key_dh_public cs
  -> infolen: size_t{v infolen <= S.max_info}
  -> info: lbuffer uint8 infolen
  -> o_key: key_aead cs
  -> o_nonce: nonce_aead cs
  -> ST unit
       (requires fun h0 ->
         live h0 pkR /\ live h0 zz /\ live h0 pkE /\
         live h0 info /\ live h0 o_key /\ live h0 o_nonce /\
         disjoint o_key o_nonce)
       (ensures fun h0 _ h1 -> modifies (loc o_key |+| loc o_nonce) h0 h1 /\
         (let keyIR, nonceIR = S.ks_derive cs S.Base (as_seq h0 pkR) (as_seq h0 zz) (as_seq h0 pkE) (as_seq h0 info) None None in
         as_seq h1 o_key == keyIR /\ as_seq h1 o_nonce == nonceIR))

#push-options "--z3rlimit 400"

let ks_derive_default #cs pkR zz pkE infolen info o_key o_nonce =
  (**) let hinit = get() in
  push_frame();
  (**) let h0 = get() in
  let default_psk:buffer uint8 = create (nhash_length cs) (u8 0) in
  let default_pkI = create (nsize_dh_public cs) (u8 0) in
  let context_len = 7ul +. (3ul *. nsize_dh_public cs) +. infolen in
  let context = create context_len (u8 0) in
  let label_key:lbuffer uint8 8ul = createL S.label_key_list in
  let label_nonce = createL S.label_nonce_list in
  let tmp = create (10ul +. context_len) (u8 0) in
  let secret:buffer uint8 = create (nhash_length cs) (u8 0) in
  ks_derive_default_aux #cs pkR zz pkE infolen info o_key o_nonce
    context_len context secret default_pkI default_psk label_key label_nonce tmp;
  (**) let h1 = get() in
  pop_frame();
  (**) let hf = get() in
  (**) LowStar.Monotonic.Buffer.modifies_fresh_frame_popped hinit h0 (loc o_key |+| loc o_nonce) h1 hf

#pop-options

#set-options "--z3rlimit 100"

[@ Meta.Attribute.specialize]
let setupBaseI #cs o_pkE o_k o_n skE pkR infolen info =
  push_frame();
  let zz = create (nsize_dh_public cs) (u8 0) in
  encap zz o_pkE skE pkR;
  ks_derive_default pkR zz o_pkE infolen info o_k o_n;
  pop_frame()

[@ Meta.Attribute.specialize]
let setupBaseR #cs o_key_aead o_nonce_aead pkE skR infolen info =
  push_frame();
  let pkR = create (nsize_dh_public cs) (u8 0) in
  let zz = create (nsize_dh_public cs) (u8 0) in
  DH.secret_to_public pkR skR;
  decap zz pkE skR;
  ks_derive_default pkR zz pkE infolen info o_key_aead o_nonce_aead;
  pop_frame()

noextract inline_for_extraction
val encryptBase_aux
     (#cs:S.ciphersuite)
     (skE: key_dh_secret cs)
     (pkR: key_dh_public cs)
     (mlen: size_t{v mlen <= S.max_length cs})
     (m:lbuffer uint8 mlen)
     (infolen: size_t {v infolen <= S.max_info /\ v infolen + S.size_dh_public cs + 16 <= max_size_t})
     (info: lbuffer uint8 infolen)
     (output: lbuffer uint8 (size (v infolen + S.size_dh_public cs + 16)))
     (zz:key_dh_public cs)
     (pkR': key_dh_public cs)
     (k:key_aead cs)
     (n:nonce_aead cs) :
     ST unit
       (requires fun h0 ->
         live h0 output /\ live h0 skE /\ live h0 pkR /\
         live h0 m /\ live h0 info /\
         live h0 zz /\ live h0 pkR' /\ live h0 k /\ live h0 n /\
         disjoint output info /\ disjoint output m /\ disjoint output skE /\
         disjoint zz skE /\ disjoint zz pkR /\ disjoint pkR' skE /\ disjoint pkR' pkR /\ disjoint zz pkR' /\
         disjoint info zz /\ disjoint info pkR' /\ disjoint m zz /\ disjoint m pkR' /\
         disjoint info k /\ disjoint info n /\ disjoint m n /\ disjoint k m /\
         disjoint output pkR' /\ disjoint output k /\ disjoint output n /\ disjoint k n)
       (ensures fun h0 _ h1 ->
         modifies (loc zz |+| loc pkR' |+| loc k |+| loc n |+| loc output) h0 h1 /\
         as_seq h1 output `Seq.equal` S.encryptBase cs (as_seq h0 skE) (as_seq h0 pkR) (as_seq h0 m) (as_seq h0 info))

noextract inline_for_extraction
[@ Meta.Attribute.inline_]
let encryptBase_aux #cs skE pkR mlen m infolen info output zz pkR' k n =
  assert (v (infolen +. 16ul) == v infolen + 16);
  assert (S.size_dh_public cs + v (infolen +. 16ul) == length output);
  encap zz pkR' skE pkR;
  let pkE:key_dh_public cs = sub output 0ul (nsize_dh_public cs) in
  setupBaseI pkE k n skE pkR' infolen info;
  let dec = sub output (nsize_dh_public cs) (infolen +. 16ul) in
  AEAD.aead_encrypt #cs k n mlen m infolen info dec;
  let h2 = get() in
  assert (as_seq h2 output `Seq.equal` (as_seq h2 pkE `Seq.append` as_seq h2 dec))

#push-options "--z3rlimit 400"

[@ Meta.Attribute.specialize]
let encryptBase #cs skE pkR mlen m infolen info output =
  (**) let hinit = get() in
  push_frame();
  (**) let h0 = get() in
  let zz = create (nsize_dh_public cs) (u8 0) in
  let pkR' = create (nsize_dh_public cs) (u8 0) in
  let k = create (nsize_aead_key cs) (u8 0) in
  let n = create (nsize_aead_nonce cs) (u8 0) in
  encryptBase_aux #cs skE pkR mlen m infolen info output zz pkR' k n;
  (**) let h1 = get() in
  pop_frame();
  (**) let hf = get() in
  (**) LowStar.Monotonic.Buffer.modifies_fresh_frame_popped hinit h0 (loc output) h1 hf

#pop-options

[@ Meta.Attribute.specialize]
let decryptBase #cs pkE skR mlen m infolen info output = admit()
