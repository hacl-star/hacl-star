module Hacl.Impl.HPKE

open FStar.HyperStack
open FStar.HyperStack.All

module MB = LowStar.Monotonic.Buffer

open Lib.IntTypes
open Lib.Buffer
open FStar.Mul

module S = Spec.Agile.HPKE
module SDH = Spec.Agile.DH
module DH = Hacl.Impl.Generic.DH
module HKDF = Hacl.Impl.Generic.HKDF
module AEAD = Hacl.Impl.Generic.AEAD
module Hash = Hacl.Impl.Generic.Hash

friend Spec.Agile.HPKE

#set-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
let psk (cs:S.ciphersuite) = lbuffer uint8 (size (S.size_psk cs))

inline_for_extraction noextract
let nhash_length_u8 (cs:S.ciphersuite) : (s:uint8{v s == S.size_psk cs}) =
  match cs with
  | _, _, Spec.Agile.Hash.SHA2_256 -> u8 32
  | _, _, Spec.Agile.Hash.SHA2_512 -> u8 64


inline_for_extraction noextract
let nhash_length (cs:S.ciphersuite) : (s:size_t{v s == S.size_psk cs}) =
  match cs with
  | _, _, Spec.Agile.Hash.SHA2_256 -> 32ul
  | _, _, Spec.Agile.Hash.SHA2_512 -> 64ul

inline_for_extraction noextract
let nsize_dh_public (cs:S.ciphersuite) : (s:size_t{v s == S.size_dh_public cs}) =
  match cs with
  | SDH.DH_Curve25519, _, _ -> 32ul
  | SDH.DH_Curve448, _, _ -> 56ul
  | SDH.DH_P256, _, _ -> 64ul

inline_for_extraction noextract
let nsize_dh_key (cs:S.ciphersuite) : (s:size_t{v s == S.size_dh_key cs}) =
  match cs with
  | SDH.DH_Curve25519, _, _ -> 32ul
  | SDH.DH_Curve448, _, _ -> 56ul
  | SDH.DH_P256, _, _ -> 32ul

inline_for_extraction noextract
let nsize_aead_key (cs:S.ciphersuite) : (s:size_t{v s == S.size_aead_key cs}) =
  match cs with
  | _, Spec.Agile.AEAD.AES128_GCM, _ -> 16ul
  | _, Spec.Agile.AEAD.AES256_GCM, _ -> 32ul
  | _, Spec.Agile.AEAD.CHACHA20_POLY1305, _ -> 32ul

inline_for_extraction noextract
let nsize_aead_nonce (cs:S.ciphersuite) : (s:size_t{v s == S.size_aead_nonce cs}) =
  match cs with
  | _, Spec.Agile.AEAD.AES128_GCM, _ -> 12ul
  | _, Spec.Agile.AEAD.AES256_GCM, _ -> 12ul
  | _, Spec.Agile.AEAD.CHACHA20_POLY1305, _ -> 12ul

noextract
val encap:
     #cs:S.ciphersuite
  -> o_zz: key_dh_public cs
  -> o_pkE: key_dh_public cs
  -> skE: key_dh_secret cs
  -> pkR: key_dh_public cs
  -> ST unit
    (requires fun h0 ->
      (S.curve_of_cs cs = Spec.Agile.DH.DH_Curve25519 ==>
        Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled)) /\
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
  DH.scalarmult #cs o_zz skE pkR

noextract
val decap:
     #cs:S.ciphersuite
  -> o_pkR: key_dh_public cs
  -> pkE: key_dh_public cs
  -> skR: key_dh_secret cs
  -> ST unit
    (requires fun h0 ->
      (S.curve_of_cs cs = Spec.Agile.DH.DH_Curve25519 ==>
        Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled)) /\
      live h0 o_pkR /\ live h0 pkE /\ live h0 skR /\
      disjoint o_pkR pkE /\ disjoint o_pkR skR)
    (ensures fun h0 _ h1 -> modifies (loc o_pkR) h0 h1 /\
      as_seq h1 o_pkR == S.decap cs (as_seq h0 pkE) (as_seq h0 skR))

[@ Meta.Attribute.inline_ ]
let decap #cs o_pkR pkE skR = DH.scalarmult #cs o_pkR skR pkE

noextract inline_for_extraction
val id_of_cs (cs:S.ciphersuite) (output:lbuffer uint8 6ul):
  ST unit
  (requires fun h -> live h output)
  (ensures fun h0 _ h1 -> modifies (loc output) h0 h1 /\ as_seq h1 output `Seq.equal` S.id_of_cs cs)

let id_of_cs cs output =
  let open Spec.Agile.DH in
  let open Spec.Agile.AEAD in
  let open Spec.Agile.Hash in
  match cs with
  | DH_Curve25519, AES128_GCM,        SHA2_256 ->
      upd output 0ul (u8 1); upd output 1ul (u8 1); upd output 2ul (u8 1);
      upd output 3ul (u8 1); upd output 4ul (u8 1); upd output 5ul (u8 1)
  | DH_Curve25519, CHACHA20_POLY1305, SHA2_256 ->
      upd output 0ul (u8 2); upd output 1ul (u8 2); upd output 2ul (u8 2);
      upd output 3ul (u8 2); upd output 4ul (u8 2); upd output 5ul (u8 2)
  | DH_Curve448,   AES256_GCM,        SHA2_512 ->
      upd output 0ul (u8 3); upd output 1ul (u8 3); upd output 2ul (u8 3);
      upd output 3ul (u8 3); upd output 4ul (u8 3); upd output 5ul (u8 3)
  | DH_Curve448,   CHACHA20_POLY1305, SHA2_512 ->
      upd output 0ul (u8 4); upd output 1ul (u8 4); upd output 2ul (u8 4);
      upd output 3ul (u8 4); upd output 4ul (u8 4); upd output 5ul (u8 4)
  | DH_P256,       AES128_GCM,        SHA2_256 ->
      upd output 0ul (u8 5); upd output 1ul (u8 5); upd output 2ul (u8 5);
      upd output 3ul (u8 5); upd output 4ul (u8 5); upd output 5ul (u8 5)
  | DH_P256,       CHACHA20_POLY1305, SHA2_256 ->
      upd output 0ul (u8 6); upd output 1ul (u8 6); upd output 2ul (u8 6);
      upd output 3ul (u8 6); upd output 4ul (u8 6); upd output 5ul (u8 6)
  | DH_Curve25519, CHACHA20_POLY1305, SHA2_512 ->
      upd output 0ul (u8 7); upd output 1ul (u8 7); upd output 2ul (u8 7);
      upd output 3ul (u8 7); upd output 4ul (u8 7); upd output 5ul (u8 7)

inline_for_extraction noextract
val build_context_default:
     #cs:S.ciphersuite
  -> pkE: key_dh_public cs
  -> pkR: key_dh_public cs
  -> pkI: key_dh_public cs
  -> pskID_hash:lbuffer uint8 (nhash_length cs)
  -> info_hash:lbuffer uint8 (nhash_length cs)
  -> output:lbuffer uint8 (size (9 + (3 * S.size_dh_public cs) + (2 * Spec.Agile.Hash.size_hash (S.hash_of_cs cs))))
  -> ST unit
    (requires fun h0 ->
      live h0 pkE /\ live h0 pkR /\ live h0 pkI /\
      live h0 pskID_hash /\ live h0 info_hash /\ live h0 output /\
      disjoint output pkE /\ disjoint output pkR /\ disjoint output pkI /\
      disjoint output pskID_hash /\ disjoint output info_hash)
    (ensures fun h0 _ h1 -> modifies (loc output) h0 h1 /\
      as_seq h1 output `Seq.equal` S.build_context S.Base cs (as_seq h0 pkE) (as_seq h0 pkR) (as_seq h0 pkI) (as_seq h0 pskID_hash) (as_seq h0 info_hash))

#set-options "--z3rlimit 300"

let build_context_default #cs pkE pkR pkI pskID_hash info_hash output =
  (**) let h0 = get() in
  upd output 0ul (u8 0);
  id_of_cs cs (sub output 1ul 6ul);
  (**) let h1 = get() in
  (**) assert (as_seq h1 (gsub output 1ul 6ul) == S.id_of_cs cs);
  (**) assert (as_seq h1 (gsub output 0ul 1ul) `Seq.equal` S.id_of_mode S.Base);
  (**) assert (as_seq h1 (gsub output 0ul 7ul) `Seq.equal` (S.id_of_mode S.Base `Seq.append` S.id_of_cs cs));
  copy (sub output 7ul (nsize_dh_public cs)) pkE;
  (**) let h2 = get() in
  copy (sub output (7ul +. nsize_dh_public cs) (nsize_dh_public cs)) pkR;
  (**) let h3 = get() in
  copy (sub output (7ul +. nsize_dh_public cs +. nsize_dh_public cs) (nsize_dh_public cs)) pkI;
  (**) let h4 = get() in
  (**) assert (as_seq h4 (gsub output 0ul (7ul +. nsize_dh_public cs +. nsize_dh_public cs +. nsize_dh_public cs)) `Seq.equal`
    (S.id_of_mode S.Base `Seq.append`
    S.id_of_cs cs `Seq.append`
    as_seq h0 pkE `Seq.append`
    as_seq h0 pkR `Seq.append`
    as_seq h0 pkI));
  let psklen_b = sub output (7ul +. nsize_dh_public cs +. nsize_dh_public cs +. nsize_dh_public cs) 1ul in
  Lib.ByteBuffer.uint_to_bytes_be (psklen_b) (nhash_length_u8 cs);
  (**) [@inline_let]
  (**) let hlength = Spec.Agile.Hash.size_hash (S.hash_of_cs cs) in
  (**) let h5 = get() in
  (**) Lib.ByteSequence.lemma_uint_to_bytes_be_preserves_value (nhash_length_u8 cs);
  (**) Lib.ByteSequence.nat_from_intseq_be_inj (as_seq h5 psklen_b) (Lib.ByteSequence.nat_to_bytes_be #SEC 1 hlength);
  (**) assert (as_seq h5 psklen_b `Seq.equal` Lib.ByteSequence.nat_to_bytes_be #SEC 1 hlength);
  (**) assert (as_seq h5 (gsub output 0ul (7ul +. nsize_dh_public cs +. nsize_dh_public cs +. nsize_dh_public cs +. 1ul)) `Seq.equal`
    (S.id_of_mode S.Base `Seq.append`
     S.id_of_cs cs `Seq.append`
     as_seq h0 pkE `Seq.append`
     as_seq h0 pkR `Seq.append`
     as_seq h0 pkI `Seq.append`
     Lib.ByteSequence.nat_to_bytes_be 1 hlength));
  let pskhash_b = sub output (7ul +. nsize_dh_public cs +. nsize_dh_public cs +. nsize_dh_public cs +. 1ul) (nhash_length cs) in
  copy pskhash_b pskID_hash;
  (**) let h6 = get() in
  (**) assert (as_seq h6 (gsub output 0ul (7ul +. nsize_dh_public cs +. nsize_dh_public cs +. nsize_dh_public cs +. 1ul +. nhash_length cs)) `Seq.equal`
    (S.id_of_mode S.Base `Seq.append`
     S.id_of_cs cs `Seq.append`
     as_seq h0 pkE `Seq.append`
     as_seq h0 pkR `Seq.append`
     as_seq h0 pkI `Seq.append`
     Lib.ByteSequence.nat_to_bytes_be 1 hlength `Seq.append`
     as_seq h0 pskID_hash));
  let infolen_b = sub output (7ul +. nsize_dh_public cs +. nsize_dh_public cs +. nsize_dh_public cs +. 1ul +. nhash_length cs) 1ul in
  Lib.ByteBuffer.uint_to_bytes_be infolen_b (nhash_length_u8 cs);
  (**) let h7 = get() in
  (**) Lib.ByteSequence.lemma_uint_to_bytes_be_preserves_value (nhash_length_u8 cs);
  (**) Lib.ByteSequence.nat_from_intseq_be_inj (as_seq h7 infolen_b) (Lib.ByteSequence.nat_to_bytes_be #SEC 1 hlength);
  (**) assert (as_seq h7 infolen_b `Seq.equal` Lib.ByteSequence.nat_to_bytes_be #SEC 1 hlength);
  (**) assert (as_seq h7 (gsub output 0ul (7ul +. nsize_dh_public cs +. nsize_dh_public cs +. nsize_dh_public cs +. 2ul +. nhash_length cs)) `Seq.equal`
    (S.id_of_mode S.Base `Seq.append`
    S.id_of_cs cs `Seq.append`
    as_seq h0 pkE `Seq.append`
    as_seq h0 pkR `Seq.append`
    as_seq h0 pkI `Seq.append`
    Lib.ByteSequence.nat_to_bytes_be 1 hlength `Seq.append`
    as_seq h0 pskID_hash `Seq.append`
    Lib.ByteSequence.nat_to_bytes_be 1 hlength));
  let output_info = sub output (7ul +. nsize_dh_public cs +. nsize_dh_public cs +. nsize_dh_public cs +. 2ul +. nhash_length cs) (nhash_length cs) in
  (**) assert(disjoint output_info info_hash);
  copy output_info info_hash;
  (**) let h8 = get() in
  (**) assert (as_seq h8 (gsub output 0ul (7ul +. nsize_dh_public cs +. nsize_dh_public cs +. nsize_dh_public cs +. 2ul +. nhash_length cs +. nhash_length cs)) `Seq.equal`
    (S.id_of_mode S.Base `Seq.append`
    S.id_of_cs cs `Seq.append`
    as_seq h0 pkE `Seq.append`
    as_seq h0 pkR `Seq.append`
    as_seq h0 pkI `Seq.append`
    Lib.ByteSequence.nat_to_bytes_be 1 hlength `Seq.append`
    as_seq h0 pskID_hash `Seq.append`
    Lib.ByteSequence.nat_to_bytes_be 1 hlength `Seq.append`
    as_seq h0 info_hash))

noextract
val ks_derive_default_aux:
     #cs:S.ciphersuite
  -> pkR:key_dh_public cs
  -> zz:key_dh_public cs
  -> pkE:key_dh_public cs
  -> infolen: size_t{v infolen <= S.max_info}
  -> info: lbuffer uint8 infolen
  -> o_key: key_aead cs
  -> o_nonce: nonce_aead cs
  -> context_len:size_t{v context_len == 9 + (3 * S.size_dh_public cs) + 2 *
                                     Spec.Agile.Hash.size_hash (S.hash_of_cs cs)}
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

         MB.all_disjoint [loc o_key; loc o_nonce; loc context; loc secret; loc pkI; loc psk; loc label_key; loc label_nonce; loc tmp] /\
         disjoint secret zz /\ disjoint context zz /\
         disjoint context pkE /\ disjoint context pkR /\ disjoint context info /\
         disjoint tmp zz /\ disjoint tmp pkE /\ disjoint tmp pkR /\ disjoint tmp info /\

         as_seq h0 label_key `Seq.equal` S.label_key /\
         as_seq h0 label_nonce `Seq.equal` S.label_nonce /\
         as_seq h0 psk `Seq.equal` S.default_psk cs /\
         as_seq h0 pkI `Seq.equal` S.default_pkI cs)
       (ensures fun h0 _ h1 -> modifies (loc o_nonce |+| loc o_key |+| loc tmp |+| loc context |+| loc secret) h0 h1 /\
         (let keyIR, nonceIR = S.ks_derive cs S.Base (as_seq h0 pkR) (as_seq h0 zz) (as_seq h0 pkE) (as_seq h0 info) None None in
         as_seq h1 o_key == keyIR /\ as_seq h1 o_nonce == nonceIR))

#set-options "--z3rlimit 100"

noextract
[@ Meta.Attribute.inline_]
let ks_derive_default_aux #cs pkR zz pkE infolen info o_key o_nonce context_len context secret pkI psk label_key label_nonce tmp =
  let info_hash:lbuffer uint8 (nhash_length cs) = sub tmp 0ul (nhash_length cs) in
  let pskID_hash:lbuffer uint8 (nhash_length cs) = sub tmp (nhash_length cs) (nhash_length cs) in
  Hash.hash #cs info infolen info_hash;
  let empty_b:lbuffer uint8 0ul = sub info 0ul 0ul in
  (**) let h0 = get() in
  Hash.hash #cs empty_b 0ul pskID_hash;
  (**) assert (as_seq h0 empty_b `Seq.equal` S.default_pskId);
  build_context_default pkE pkR pkI pskID_hash info_hash context;
  let h0 = get() in
  HKDF.hkdf_extract #cs secret psk (nhash_length cs) zz (nsize_dh_public cs);
  let info_key = sub tmp 2ul (8ul +. context_len) in
  let h' = get() in
  copy (sub info_key 0ul 8ul) label_key;
  copy (sub info_key 8ul context_len) context;
  (**) let h1 = get() in
  (**) assert (as_seq h1 info_key `Seq.equal` (S.label_key `Seq.append` as_seq h0 context));
  HKDF.hkdf_expand #cs o_key secret (nhash_length cs) info_key (8ul +. context_len) (nsize_aead_key cs);
  copy (sub tmp 0ul 10ul) label_nonce;
  (**) let h2 = get() in
  (**) assert (as_seq h2 tmp `Seq.equal` (S.label_nonce `Seq.append` as_seq h0 context));
  HKDF.hkdf_expand #cs o_nonce secret (nhash_length cs) tmp (10ul +. context_len) (nsize_aead_nonce cs)

noextract
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

noextract
[@ Meta.Attribute.inline_]
let ks_derive_default #cs pkR zz pkE infolen info o_key o_nonce =
  [@inline_let]
  let label_nonce_list:list uint8 = [u8 0x68; u8 0x70; u8 0x6b; u8 0x65; u8 0x20; u8 0x6e; u8 0x6f; u8 0x6e; u8 0x63; u8 0x65] in
  assert_norm(label_nonce_list == S.label_nonce_list);
  [@inline_let]
  let label_key_list:list uint8 = [u8 0x68; u8 0x70; u8 0x6b; u8 0x65; u8 0x20; u8 0x6b; u8 0x65; u8 0x79] in
  assert_norm(label_key_list == S.label_key_list);
  (**) let hinit = get() in
  push_frame();
  (**) let h0 = get() in
  let default_psk:buffer uint8 = create (nhash_length cs) (u8 0) in
  let default_pkI = create (nsize_dh_public cs) (u8 0) in
  let context_len = 9ul +. (3ul *. nsize_dh_public cs) +. (2ul *. nhash_length cs) in
  let context = create context_len (u8 0) in
  let label_key:lbuffer uint8 8ul = createL label_key_list in
  let label_nonce = createL label_nonce_list in
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
  DH.secret_to_public #cs pkR skR;
  decap zz pkE skR;
  ks_derive_default pkR zz pkE infolen info o_key_aead o_nonce_aead;
  pop_frame()

noextract
val sealBase_aux
     (#cs:S.ciphersuite)
     (skE: key_dh_secret cs)
     (pkR: key_dh_public cs)
     (mlen: size_t{v mlen <= S.max_length cs /\  v mlen + S.size_dh_public cs + 16 <= max_size_t})
     (m:lbuffer uint8 mlen)
     (infolen: size_t {v infolen <= S.max_info})
     (info: lbuffer uint8 infolen)
     (output: lbuffer uint8 (size (v mlen + S.size_dh_public cs + 16)))
     (zz:key_dh_public cs)
     (k:key_aead cs)
     (n:nonce_aead cs) :
     ST unit
       (requires fun h0 ->
        (S.curve_of_cs cs = Spec.Agile.DH.DH_Curve25519 ==>
          Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled)) /\
         live h0 output /\ live h0 skE /\ live h0 pkR /\
         live h0 m /\ live h0 info /\
         live h0 zz /\ live h0 k /\ live h0 n /\
         disjoint output info /\ disjoint output m /\ disjoint output skE /\
         disjoint zz skE /\ disjoint zz pkR /\
         disjoint info zz /\ disjoint m zz /\
         disjoint info k /\ disjoint info n /\ disjoint m n /\ disjoint k m /\
         disjoint output pkR /\ disjoint output k /\ disjoint output n /\ disjoint k n)
       (ensures fun h0 _ h1 ->
         modifies (loc zz |+| loc k |+| loc n |+| loc output) h0 h1 /\
         as_seq h1 output `Seq.equal` S.sealBase cs (as_seq h0 skE) (as_seq h0 pkR) (as_seq h0 m) (as_seq h0 info))

#push-options "--z3rlimit 400"

noextract
[@ Meta.Attribute.inline_]
let sealBase_aux #cs skE pkR mlen m infolen info output zz k n =
  assert (v (mlen +. 16ul) == v mlen + 16);
  assert (S.size_dh_public cs + v (mlen +. 16ul) == length output);
  let pkE:key_dh_public cs = sub output 0ul (nsize_dh_public cs) in
  setupBaseI pkE k n skE pkR infolen info;
  let dec = sub output (nsize_dh_public cs) (mlen +. 16ul) in
  AEAD.aead_encrypt #cs k n infolen info mlen m dec;
  let h2 = get() in
  assert (as_seq h2 output `Seq.equal` (as_seq h2 pkE `Seq.append` as_seq h2 dec))

[@ Meta.Attribute.specialize]
let sealBase #cs skE pkR mlen m infolen info output =
  (**) let hinit = get() in
  push_frame();
  (**) let h0 = get() in
  let zz = create (nsize_dh_public cs) (u8 0) in
  let k = create (nsize_aead_key cs) (u8 0) in
  let n = create (nsize_aead_nonce cs) (u8 0) in
  sealBase_aux #cs skE pkR mlen m infolen info output zz k n;
  (**) let h1 = get() in
  pop_frame();
  (**) let hf = get() in
  (**) LowStar.Monotonic.Buffer.modifies_fresh_frame_popped hinit h0 (loc output) h1 hf

#pop-options

noextract
val openBase_aux
     (#cs:S.ciphersuite)
     (skR: key_dh_secret cs)
     (inputlen: size_t{S.size_dh_public cs + S.size_aead_tag cs <= v inputlen /\ v inputlen <= max_size_t})
     (input:lbuffer uint8 inputlen)
     (infolen: size_t {v infolen <= S.max_info})
     (info: lbuffer uint8 infolen)
     (output: lbuffer uint8 (size (v inputlen - S.size_dh_public cs - S.size_aead_tag cs)))
     (zz:key_dh_public cs)
     (k:key_aead cs)
     (n:nonce_aead cs) :
     ST UInt32.t
       (requires fun h0 ->
        (S.curve_of_cs cs = Spec.Agile.DH.DH_Curve25519 ==>
         Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled)) /\
         live h0 output /\ live h0 skR /\
         live h0 input /\ live h0 info /\
         live h0 zz /\ live h0 k /\ live h0 n /\
         disjoint output info /\ disjoint output input /\
         disjoint zz skR /\
         disjoint info zz /\ disjoint input zz /\
         disjoint info k /\ disjoint info n /\ disjoint input n /\ disjoint k input /\
         disjoint output k /\ disjoint output n /\ disjoint k n)
       (ensures fun h0 z h1 ->
         modifies (loc zz |+| loc k |+| loc n |+| loc output) h0 h1 /\
         (let plain = S.openBase cs (as_seq h0 skR) (as_seq h0 input) (as_seq h0 info) in
         match z with
         | 0ul -> Some? plain /\ as_seq h1 output `Seq.equal` Some?.v plain
         | 1ul -> None? plain
         | _ -> False))

noextract
[@ Meta.Attribute.inline_]
let openBase_aux #cs skR inputlen input infolen info output zz k n =
  let pkE = sub input 0ul (nsize_dh_public cs) in
  let clen = inputlen -. nsize_dh_public cs in
  assert (v (clen -. 16ul) <= S.max_length cs);
  assert (v (clen -. 16ul) + 16 <= max_size_t);
  assert (length output == v (clen -. 16ul));
  let c = sub input (nsize_dh_public cs) clen in
  setupBaseR k n pkE skR infolen info;
  AEAD.aead_decrypt #cs k n infolen info (clen -. 16ul) output c

[@ Meta.Attribute.specialize]
let openBase #cs pkE skR mlen m infolen info output =
  push_frame();
  let zz = create (nsize_dh_public cs) (u8 0) in
  let k = create (nsize_aead_key cs) (u8 0) in
  let n = create (nsize_aead_nonce cs) (u8 0) in
  let z = openBase_aux #cs skR mlen m infolen info output zz k n in
  pop_frame();
  z
