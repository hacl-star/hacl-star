module Hacl.Impl.HPKE

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All

module MB = LowStar.Monotonic.Buffer

open Lib.IntTypes
open Lib.Buffer
open FStar.Mul

module S = Spec.Agile.HPKE
module SHa = Spec.Agile.Hash
module SDH = Spec.Agile.DH
module SAEAD = Spec.Agile.AEAD
module DH = Hacl.HPKE.Interface.DH
module HKDF = Hacl.HPKE.Interface.HKDF
module AEAD = Hacl.HPKE.Interface.AEAD
module Hash = Hacl.HPKE.Interface.Hash

friend Spec.Agile.HPKE

#set-options "--z3rlimit 20 --fuel 0 --ifuel 0"

(* Defining basic types for the different arguments of HPKE functions *)

inline_for_extraction noextract
let seq_aead (cs:S.ciphersuite) = n:UInt64.t{UInt64.v n <= S.max_seq cs}
inline_for_extraction noextract
let exporter_secret (cs:S.ciphersuite) = lbuffer uint8 (size (S.size_kdf cs))
inline_for_extraction noextract
let key_kem (cs:S.ciphersuite) = lbuffer uint8 (size (S.size_kem_key cs))

inline_for_extraction noextract
let nsize_aead_key (cs:S.ciphersuite) : (s:size_t{v s == S.size_aead_key cs}) =
  match S.aead_of_cs cs with
  | S.ExportOnly -> 0ul
  | S.Seal SAEAD.AES128_GCM -> 16ul
  | S.Seal SAEAD.AES256_GCM -> 32ul
  | S.Seal SAEAD.CHACHA20_POLY1305 -> 32ul

inline_for_extraction noextract
let nsize_aead_nonce (cs:S.ciphersuite) : (s:size_t{v s == S.size_aead_nonce cs}) =
  match S.aead_of_cs cs with
  | S.ExportOnly -> 0ul
  | S.Seal _ -> 12ul

inline_for_extraction noextract
let nsize_kem_key (cs:S.ciphersuite) : (s:size_t{v s == S.size_kem_key cs}) =
  match S.kem_hash_of_cs cs with
  | SHa.SHA2_256 -> 32ul

inline_for_extraction noextract
let nsize_serialized_dh (cs:S.ciphersuite) : (s:size_t{v s == S.size_dh_serialized cs}) =
  match S.kem_dh_of_cs cs with
  | SDH.DH_Curve25519 -> 32ul
  | SDH.DH_P256 -> 64ul

inline_for_extraction noextract
let nsize_public_dh (cs:S.ciphersuite) : (s:size_t{v s == S.size_dh_public cs}) =
  match S.kem_dh_of_cs cs with
  | SDH.DH_Curve25519 -> 32ul
  | SDH.DH_P256 -> 65ul

inline_for_extraction noextract
let nsize_two_public_dh (cs:S.ciphersuite) : (s:size_t{v s == S.size_dh_public cs + S.size_dh_public cs}) =
  match S.kem_dh_of_cs cs with
  | SDH.DH_Curve25519 -> 64ul
  | SDH.DH_P256 -> 130ul

inline_for_extraction noextract
let nsize_ks_ctx (cs:S.ciphersuite) : (s:size_t{v s == S.size_ks_ctx cs}) =
  match S.hash_of_cs cs with
  | SHa.SHA2_256 -> 65ul
  | SHa.SHA2_384 -> 97ul
  | SHa.SHA2_512 -> 129ul

inline_for_extraction noextract
let nsize_hash_length (cs:S.ciphersuite) : (s:size_t{v s == S.size_kdf cs}) =
  match S.hash_of_cs cs with
  | SHa.SHA2_256 -> 32ul
  | SHa.SHA2_384 -> 48ul
  | SHa.SHA2_512 -> 64ul

inline_for_extraction noextract
let nsize_kem_hash_length (cs:S.ciphersuite) : (s:size_t{v s == S.size_kem_kdf cs}) =
  match S.kem_hash_of_cs cs with
  | SHa.SHA2_256 -> 32ul

inline_for_extraction noextract
let nsize_hash_length_plus_one (cs:S.ciphersuite) : size_t =
  match S.hash_of_cs cs with
  | SHa.SHA2_256 -> 33ul
  | SHa.SHA2_384 -> 49ul
  | SHa.SHA2_512 -> 65ul

noeq
type context_s (cs:S.ciphersuite) =
  { ctx_key : key_aead cs;
    ctx_nonce : nonce_aead cs;
    ctx_seq : lbuffer (seq_aead cs) 1ul;
    ctx_exporter : exporter_secret cs
  }

let ctx_loc #cs ctx =
  loc ctx.ctx_key |+| loc ctx.ctx_nonce |+| loc ctx.ctx_seq |+| loc ctx.ctx_exporter

let ctx_invariant #cs h ctx =
  live h ctx.ctx_key /\ live h ctx.ctx_nonce /\ live h ctx.ctx_seq /\ live h ctx.ctx_exporter /\
  disjoint ctx.ctx_key ctx.ctx_nonce /\ disjoint ctx.ctx_key ctx.ctx_exporter /\
  disjoint ctx.ctx_key ctx.ctx_seq /\ disjoint ctx.ctx_nonce ctx.ctx_seq /\
  disjoint ctx.ctx_nonce ctx.ctx_exporter /\ disjoint ctx.ctx_seq ctx.ctx_exporter

let as_ctx #cs h ctx =
  (as_seq h ctx.ctx_key,
   as_seq h ctx.ctx_nonce,
   UInt64.v (Seq.index (as_seq h ctx.ctx_seq) 0),
   as_seq h ctx.ctx_exporter)

let frame_ctx #cs ctx l h0 h1 = ()

let lemma_includes_ctx_loc (#cs:S.ciphersuite) (ctx:context_s cs) : Lemma
  (B.loc_includes (ctx_loc ctx) (loc ctx.ctx_key) /\
   B.loc_includes (ctx_loc ctx) (loc ctx.ctx_nonce) /\
   B.loc_includes (ctx_loc ctx) (loc ctx.ctx_seq) /\
   B.loc_includes (ctx_loc ctx) (loc ctx.ctx_exporter))
  = ()

inline_for_extraction noextract
val deserialize_public_key:
     #cs:S.ciphersuite
  -> pk: key_dh_public cs
  -> Stack (lbuffer uint8 (DH.nsize_public (S.kem_dh_of_cs cs)))
    (requires fun h -> live h pk)
    (ensures fun h0 b h1 -> live h1 b /\ h0 == h1 /\
      (match S.kem_dh_of_cs cs with
      | SDH.DH_Curve25519 -> b == pk
      | SDH.DH_P256 -> b == gsub pk 1ul 64ul))

let deserialize_public_key #cs pk =
  match cs with
  | SDH.DH_Curve25519, _, _, _ -> pk
  | SDH.DH_P256, _, _, _ -> sub pk 1ul 64ul

inline_for_extraction noextract
val serialize_public_key:
     #cs:S.ciphersuite
  -> pk: key_dh_public cs
  -> b: (lbuffer uint8 (DH.nsize_public (S.kem_dh_of_cs cs)))
  -> Stack unit
    (requires fun h -> live h pk /\ live h b /\
      (match S.kem_dh_of_cs cs with
      | SDH.DH_Curve25519 -> b == pk
      | SDH.DH_P256 -> b == gsub pk 1ul 64ul))
    (ensures fun h0 _ h1 -> modifies (loc pk) h0 h1 /\
      as_seq h1 pk `Seq.equal` S.serialize_public_key cs (as_seq h0 b))

let serialize_public_key #cs pk b =
  match cs with
  | SDH.DH_Curve25519, _, _, _ -> ()
  | SDH.DH_P256, _, _, _ -> upd pk 0ul (u8 4)

inline_for_extraction noextract
val prepare_dh:
     #cs:S.ciphersuite
  -> pk: serialized_point_dh cs
  -> Stack (lbuffer uint8 32ul)
    (requires fun h -> live h pk)
    (ensures fun h0 b h1 -> live h1 b /\ h0 == h1 /\
      (match S.kem_dh_of_cs cs with
      | SDH.DH_Curve25519 -> b == pk
      | SDH.DH_P256 -> b == gsub pk 0ul 32ul))

let prepare_dh #cs pk =
  match cs with
  | SDH.DH_Curve25519, _, _, _ -> pk
  | SDH.DH_P256, _, _, _ -> sub pk 0ul 32ul

inline_for_extraction noextract
val init_id_mode:
 m:S.mode ->
 b:lbuffer uint8 1ul ->
 Stack unit
   (requires fun h -> live h b)
   (ensures fun h0 _ h1 -> modifies (loc b) h0 h1 /\
     as_seq h1 b `Seq.equal` S.id_of_mode m)

#push-options "--ifuel 1"

inline_for_extraction noextract
let init_id_mode m b =
  match m with
  | S.Base -> upd b 0ul (u8 0)
  | S.PSK -> upd b 0ul (u8 1)
  | S.Auth -> upd b 0ul (u8 2)
  | S.AuthPSK -> upd b 0ul (u8 3)

#pop-options

inline_for_extraction noextract
val init_label_hpke:
 b:lbuffer uint8 4ul ->
 Stack unit
   (requires fun h -> live h b)
   (ensures fun h0 _ h1 -> modifies (loc b) h0 h1 /\
     as_seq h1 b `Seq.equal` S.label_HPKE)

#push-options "--z3rlimit 40 --fuel 4"

inline_for_extraction noextract
let init_label_hpke b =
  upd b 0ul (u8 0x48);
  upd b 1ul (u8 0x50);
  upd b 2ul (u8 0x4b);
  upd b 3ul (u8 0x45);
  Lib.Sequence.of_list_index S.label_HPKE_list 0;
  Lib.Sequence.of_list_index S.label_HPKE_list 1;
  Lib.Sequence.of_list_index S.label_HPKE_list 2;
  Lib.Sequence.of_list_index S.label_HPKE_list 3

#pop-options

inline_for_extraction noextract
val init_label_kem:
 b:lbuffer uint8 3ul ->
 Stack unit
   (requires fun h -> live h b)
   (ensures fun h0 _ h1 -> modifies (loc b) h0 h1 /\
     as_seq h1 b `Seq.equal` S.label_KEM)

#push-options "--z3rlimit 40 --fuel 3"

inline_for_extraction noextract
let init_label_kem b =
  upd b 0ul (u8 0x4b);
  upd b 1ul (u8 0x45);
  upd b 2ul (u8 0x4d);
  Lib.Sequence.of_list_index S.label_KEM_list 0;
  Lib.Sequence.of_list_index S.label_KEM_list 1;
  Lib.Sequence.of_list_index S.label_KEM_list 2

#pop-options

inline_for_extraction noextract
val init_label_version:
 b:lbuffer uint8 7ul ->
 Stack unit
   (requires fun h -> live h b)
   (ensures fun h0 _ h1 -> modifies (loc b) h0 h1 /\
     as_seq h1 b `Seq.equal` S.label_version)

#push-options "--z3rlimit 40 --fuel 7"

inline_for_extraction noextract
let init_label_version b =
  upd b 0ul (u8 0x48);
  upd b 1ul (u8 0x50);
  upd b 2ul (u8 0x4b);
  upd b 3ul (u8 0x45);
  upd b 4ul (u8 0x2d);
  upd b 5ul (u8 0x76);
  upd b 6ul (u8 0x31);
  Lib.Sequence.of_list_index S.label_version_list 0;
  Lib.Sequence.of_list_index S.label_version_list 1;
  Lib.Sequence.of_list_index S.label_version_list 2;
  Lib.Sequence.of_list_index S.label_version_list 3;
  Lib.Sequence.of_list_index S.label_version_list 4;
  Lib.Sequence.of_list_index S.label_version_list 5;
  Lib.Sequence.of_list_index S.label_version_list 6

#pop-options

inline_for_extraction noextract
val init_id_kem:
   #cs:S.ciphersuite
 -> b:lbuffer uint8 2ul ->
 Stack unit
   (requires fun h -> live h b)
   (ensures fun h0 _ h1 -> modifies (loc b) h0 h1 /\
     as_seq h1 b `Seq.equal` S.id_kem cs)

inline_for_extraction noextract
let init_id_kem #cs b =
  match cs with
  | SDH.DH_P256, SHa.SHA2_256, _, _ ->
    upd b 0ul (u8 0); upd b 1ul (u8 16)
  | SDH.DH_Curve25519, SHa.SHA2_256, _, _ ->
    upd b 0ul (u8 0); upd b 1ul (u8 32)

inline_for_extraction noextract
val init_id_kdf:
   #cs:S.ciphersuite
 -> b:lbuffer uint8 2ul ->
 Stack unit
   (requires fun h -> live h b)
   (ensures fun h0 _ h1 -> modifies (loc b) h0 h1 /\
     as_seq h1 b `Seq.equal` S.id_kdf cs)

inline_for_extraction noextract
let init_id_kdf #cs b =
  match cs with
  | _, _, _, SHa.SHA2_256 ->
    upd b 0ul (u8 0); upd b 1ul (u8 1)
  | _, _, _, SHa.SHA2_384 ->
    upd b 0ul (u8 0); upd b 1ul (u8 2)
  | _, _, _, SHa.SHA2_512 ->
    upd b 0ul (u8 0); upd b 1ul (u8 3)

inline_for_extraction noextract
val init_id_aead:
   #cs:S.ciphersuite
 -> b:lbuffer uint8 2ul ->
 Stack unit
   (requires fun h -> live h b)
   (ensures fun h0 _ h1 -> modifies (loc b) h0 h1 /\
     as_seq h1 b `Seq.equal` S.id_aead cs)

inline_for_extraction noextract
let init_id_aead #cs b =
  match cs with
  | _, _, S.Seal SAEAD.AES128_GCM, _  ->
    upd b 0ul (u8 0); upd b 1ul (u8 1)
  | _, _, S.Seal SAEAD.AES256_GCM, _  ->
    upd b 0ul (u8 0); upd b 1ul (u8 2)
  | _, _, S.Seal SAEAD.CHACHA20_POLY1305, _  ->
    upd b 0ul (u8 0); upd b 1ul (u8 3)
  | _, _, S.ExportOnly, _  ->
    upd b 0ul (u8 255); upd b 1ul (u8 255)

inline_for_extraction noextract
val init_suite_id:
     #cs:S.ciphersuite
  -> suite_id:lbuffer uint8 10ul ->
  Stack unit
    (requires fun h -> live h suite_id)
    (ensures fun h0 _ h1 -> modifies (loc suite_id) h0 h1 /\
      as_seq h1 suite_id == S.suite_id_hpke cs)

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let init_suite_id #cs suite_id =
  init_label_hpke (sub suite_id 0ul 4ul);
  init_id_kem #cs (sub suite_id 4ul 2ul);
  init_id_kdf #cs (sub suite_id 6ul 2ul);
  init_id_aead #cs (sub suite_id 8ul 2ul);
  let h1 = ST.get () in
  assert (as_seq h1 suite_id `Seq.equal` S.suite_id_hpke cs)

#pop-options

inline_for_extraction noextract
val init_suite_kem:
     #cs:S.ciphersuite
  -> suite_id:lbuffer uint8 5ul ->
  Stack unit
    (requires fun h -> live h suite_id)
    (ensures fun h0 _ h1 -> modifies (loc suite_id) h0 h1 /\
      as_seq h1 suite_id == S.suite_id_kem cs)

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let init_suite_kem #cs suite_id =
  init_label_kem (sub suite_id 0ul 3ul);
  init_id_kem #cs (sub suite_id 3ul 2ul);
  let h1 = ST.get () in
  assert (as_seq h1 suite_id `Seq.equal` S.suite_id_kem cs)

#pop-options


inline_for_extraction noextract
val labeled_extract_hash:
    #cs:S.ciphersuite
  -> o_hash: lbuffer uint8 (nsize_hash_length cs)
  -> suite_id_len:size_t
  -> suite_id:lbuffer uint8 suite_id_len
  -> saltlen:size_t
  -> salt:lbuffer uint8 saltlen
  -> labellen:size_t
  -> label:lbuffer uint8 labellen
  -> ikmlen:size_t
  -> ikm:lbuffer uint8 ikmlen ->
  Stack unit
    (requires fun h ->
      live h o_hash /\ live h suite_id /\ live h salt /\ live h label /\ live h ikm /\
      disjoint salt o_hash /\
      Spec.Agile.HMAC.keysized (S.hash_of_cs cs) (v saltlen) /\
      7 + v suite_id_len + v labellen + v ikmlen + SHa.block_length (S.hash_of_cs cs) <= max_size_t /\
      S.labeled_extract_ikm_length_pred (S.hash_of_cs cs) (v suite_id_len + v labellen + v ikmlen)
      )
    (ensures fun h0 _ h1 -> modifies (loc o_hash) h0 h1 /\
      as_seq h1 o_hash `Seq.equal` S.labeled_extract (S.hash_of_cs cs) (as_seq h0 suite_id) (as_seq h0 salt) (as_seq h0 label) (as_seq h0 ikm))


#push-options "--z3rlimit 200"

inline_for_extraction noextract
let labeled_extract_hash #cs o_hash suite_id_len suite_id saltlen salt labellen label ikmlen ikm =
  push_frame ();
  let h0 = ST.get () in
  let len = 7ul +. suite_id_len +. labellen +. ikmlen in
  let tmp = create len (u8 0) in

  init_label_version (sub tmp 0ul 7ul);
  copy (sub tmp 7ul suite_id_len) suite_id;
  copy (sub tmp (7ul +. suite_id_len) labellen) label;
  copy (sub tmp (7ul +. suite_id_len +. labellen) ikmlen) ikm;

  assert_norm (pow2 32 == max_size_t + 1);

  let h1 = ST.get () in
  assert (as_seq h1 tmp `Seq.equal`
    (((S.label_version `Seq.append` as_seq h0 suite_id) `Seq.append` (as_seq h0 label)) `Seq.append` (as_seq h0 ikm)));

  HKDF.hkdf_extract #cs o_hash salt saltlen tmp len;

  pop_frame ()

#pop-options


inline_for_extraction noextract
val labeled_extract_kem:
    #cs:S.ciphersuite
  -> o_hash: lbuffer uint8 (nsize_kem_hash_length cs)
  -> suite_id_len:size_t
  -> suite_id:lbuffer uint8 suite_id_len
  -> saltlen:size_t
  -> salt:lbuffer uint8 saltlen
  -> labellen:size_t
  -> label:lbuffer uint8 labellen
  -> ikmlen:size_t
  -> ikm:lbuffer uint8 ikmlen ->
  Stack unit
    (requires fun h ->
      live h o_hash /\ live h suite_id /\ live h salt /\ live h label /\ live h ikm /\
      disjoint salt o_hash /\
      Spec.Agile.HMAC.keysized (S.kem_hash_of_cs cs) (v saltlen) /\
      7 + v suite_id_len + v labellen + v ikmlen + SHa.block_length (S.kem_hash_of_cs cs) <= max_size_t /\
      S.labeled_extract_ikm_length_pred (S.kem_hash_of_cs cs) (v suite_id_len + v labellen + v ikmlen)
      )
    (ensures fun h0 _ h1 -> modifies (loc o_hash) h0 h1 /\
      as_seq h1 o_hash `Seq.equal` S.labeled_extract (S.kem_hash_of_cs cs) (as_seq h0 suite_id) (as_seq h0 salt) (as_seq h0 label) (as_seq h0 ikm))

#push-options "--z3rlimit 300"

inline_for_extraction noextract
let labeled_extract_kem #cs o_hash suite_id_len suite_id saltlen salt labellen label ikmlen ikm =
  push_frame ();
  let h0 = ST.get () in
  let len = 7ul +. suite_id_len +. labellen +. ikmlen in
  let tmp = create len (u8 0) in

  init_label_version (sub tmp 0ul 7ul);
  copy (sub tmp 7ul suite_id_len) suite_id;
  copy (sub tmp (7ul +. suite_id_len) labellen) label;
  copy (sub tmp (7ul +. suite_id_len +. labellen) ikmlen) ikm;

  assert_norm (pow2 32 == max_size_t + 1);

  let h1 = ST.get () in
  assert (as_seq h1 tmp `Seq.equal`
    (((S.label_version `Seq.append` as_seq h0 suite_id) `Seq.append` (as_seq h0 label)) `Seq.append` (as_seq h0 ikm)));

  HKDF.hkdf_extract_kem #cs o_hash salt saltlen tmp len;

  pop_frame ()

#pop-options

inline_for_extraction noextract
val nat_to_bytes_2 (l:size_t) (b:lbuffer uint8 4ul)
  : Stack unit
     (requires fun h -> live h b /\ v l <= 255 * 128)
     (ensures fun h0 _ h1 -> modifies (loc b) h0 h1 /\
       as_seq h1 (gsub b 0ul 2ul) `Seq.equal` Lib.ByteSequence.nat_to_bytes_be 2 (v l)
     )

inline_for_extraction noextract
let nat_to_bytes_2 l tmp =
  Lib.ByteBuffer.uint_to_bytes_be (sub tmp 0ul 4ul) (secret l);
  let h1 = ST.get () in
  assert (as_seq h1 (gsub tmp 0ul 4ul) `Seq.equal` Lib.ByteSequence.uint_to_bytes_be (secret l));

  Lib.ByteSequence.lemma_uint_to_bytes_be_preserves_value (secret l);
  assert (Lib.ByteSequence.nat_from_bytes_be (as_seq h1 (gsub tmp 0ul 4ul)) == v l);

  Lib.ByteSequence.lemma_nat_from_to_bytes_be_preserves_value (as_seq h1 (gsub tmp 0ul 4ul)) 4;
  assert (as_seq h1 (gsub tmp 0ul 4ul) == Lib.ByteSequence.nat_to_bytes_be 4 (v l));

  Lib.ByteSequence.index_nat_to_intseq_be #U8 #SEC 2 (v l) 0;
  Lib.ByteSequence.index_nat_to_intseq_be #U8 #SEC 2 (v l) 1;
  Lib.ByteSequence.index_nat_to_intseq_be #U8 #SEC 4 (v l) 0;
  Lib.ByteSequence.index_nat_to_intseq_be #U8 #SEC 4 (v l) 1;
  copy (sub tmp 0ul 2ul) (sub tmp 2ul 2ul)

inline_for_extraction noextract
val labeled_expand_hash:
    #cs:S.ciphersuite
  -> suite_id_len:size_t
  -> suite_id:lbuffer uint8 suite_id_len
  -> prklen:size_t
  -> prk:lbuffer uint8 prklen
  -> labellen:size_t
  -> label:lbuffer uint8 labellen
  -> infolen:size_t
  -> info:lbuffer uint8 infolen
  -> l:size_t
  -> o_hash: lbuffer uint8 l ->
  Stack unit
    (requires fun h ->
      live h o_hash /\ live h suite_id /\ live h prk /\ live h label /\ live h info /\
      disjoint o_hash prk /\
      Spec.Hash.Definitions.hash_length (S.hash_of_cs cs) <= v prklen /\
      Spec.Agile.HMAC.keysized (S.hash_of_cs cs) (v prklen) /\

      SHa.hash_length (S.hash_of_cs cs) + 9 + v suite_id_len + v labellen + v infolen + SHa.block_length (S.hash_of_cs cs) + 1 <= max_size_t /\
      Spec.Agile.HKDF.expand_output_length_pred (S.hash_of_cs cs) (v l))
    (ensures fun h0 _ h1 -> modifies (loc o_hash) h0 h1 /\
      as_seq h1 o_hash `Seq.equal` S.labeled_expand (S.hash_of_cs cs) (as_seq h0 suite_id) (as_seq h0 prk) (as_seq h0 label) (as_seq h0 info) (v l)
    )

#push-options "--z3rlimit 400"

inline_for_extraction noextract
let labeled_expand_hash #cs suite_id_len suite_id prklen prk labellen label infolen info l o_hash =
  push_frame ();
  let h0 = ST.get () in
  let len = 9ul +. suite_id_len +. labellen +. infolen in
  let tmp = create len (u8 0) in

  nat_to_bytes_2 l (sub tmp 0ul 4ul);
  init_label_version (sub tmp 2ul 7ul);
  copy (sub tmp 9ul suite_id_len) suite_id;
  copy (sub tmp (9ul +. suite_id_len) labellen) label;
  copy (sub tmp (9ul +. suite_id_len +. labellen) infolen) info;

  let h1 = ST.get () in
  assert (as_seq h1 tmp `Seq.equal` (
    (((Lib.ByteSequence.nat_to_bytes_be 2 (v l)
      `Seq.append` S.label_version)
      `Seq.append` (as_seq h0 suite_id))
      `Seq.append` (as_seq h0 label))
      `Seq.append` (as_seq h0 info)
      ));

  HKDF.hkdf_expand #cs o_hash prk prklen tmp len l;

  pop_frame ()

#pop-options

inline_for_extraction noextract
val labeled_expand_kem:
    #cs:S.ciphersuite
  -> suite_id_len:size_t
  -> suite_id:lbuffer uint8 suite_id_len
  -> prklen:size_t
  -> prk:lbuffer uint8 prklen
  -> labellen:size_t
  -> label:lbuffer uint8 labellen
  -> infolen:size_t
  -> info:lbuffer uint8 infolen
  -> l:size_t
  -> o_hash: lbuffer uint8 l ->
  Stack unit
    (requires fun h ->
      live h o_hash /\ live h suite_id /\ live h prk /\ live h label /\ live h info /\
      disjoint o_hash prk /\
      Spec.Hash.Definitions.hash_length (S.kem_hash_of_cs cs) <= v prklen /\
      Spec.Agile.HMAC.keysized (S.kem_hash_of_cs cs) (v prklen) /\
      SHa.hash_length (S.kem_hash_of_cs cs) + 9 + v suite_id_len + v labellen + v infolen + SHa.block_length (S.kem_hash_of_cs cs) + 1 <= max_size_t /\
      S.labeled_expand_info_length_pred (S.kem_hash_of_cs cs) (v suite_id_len + v labellen + v infolen) /\
      Spec.Agile.HKDF.expand_output_length_pred (S.kem_hash_of_cs cs) (v l))
    (ensures fun h0 _ h1 -> modifies (loc o_hash) h0 h1 /\
      as_seq h1 o_hash `Seq.equal` S.labeled_expand (S.kem_hash_of_cs cs) (as_seq h0 suite_id) (as_seq h0 prk) (as_seq h0 label) (as_seq h0 info) (v l)
    )

#push-options "--z3rlimit 400"

inline_for_extraction noextract
let labeled_expand_kem #cs suite_id_len suite_id prklen prk labellen label infolen info l o_hash =
  push_frame ();
  let h0 = ST.get () in
  let len = 9ul +. suite_id_len +. labellen +. infolen in
  let tmp = create len (u8 0) in

  nat_to_bytes_2 l (sub tmp 0ul 4ul);
  init_label_version (sub tmp 2ul 7ul);
  copy (sub tmp 9ul suite_id_len) suite_id;
  copy (sub tmp (9ul +. suite_id_len) labellen) label;
  copy (sub tmp (9ul +. suite_id_len +. labellen) infolen) info;

  let h1 = ST.get () in
  assert (as_seq h1 tmp `Seq.equal` (
    (((Lib.ByteSequence.nat_to_bytes_be 2 (v l)
      `Seq.append` S.label_version)
      `Seq.append` (as_seq h0 suite_id))
      `Seq.append` (as_seq h0 label))
      `Seq.append` (as_seq h0 info)
      ));

  HKDF.hkdf_expand_kem #cs o_hash prk prklen tmp len l;

  pop_frame ()

#pop-options

inline_for_extraction noextract
val extract_and_expand:
     #cs: S.ciphersuite
  -> o_shared: key_kem cs
  -> dh: lbuffer uint8 32ul
  -> ctxlen : size_t
  -> kemcontext: lbuffer uint8 ctxlen
  -> Stack unit
     (requires fun h ->
       live h o_shared /\ live h dh /\ live h kemcontext /\
       disjoint o_shared dh /\ disjoint o_shared kemcontext /\
       SHa.hash_length (S.kem_hash_of_cs cs) + v ctxlen + 28 + SHa.block_length (S.kem_hash_of_cs cs) <= max_size_t
     )
     (ensures fun h0 _ h1 -> modifies (loc o_shared) h0 h1 /\
       as_seq h1 o_shared `Seq.equal` S.extract_and_expand cs (as_seq h0 dh) (as_seq h0 kemcontext))

inline_for_extraction noextract
let extract_and_expand #cs o_shared dh ctxlen kemcontext =
  push_frame ();

  let o_eae_prk = create (nsize_kem_hash_length cs) (u8 0) in

  let suite_id_kem = create 5ul (u8 0) in
  init_suite_kem #cs suite_id_kem;

  let empty = sub suite_id_kem 0ul 0ul in
  let h0 = ST.get() in
  assert (as_seq h0 empty `Seq.equal` Lib.ByteSequence.lbytes_empty);

  [@inline_let]
  let l_label_eae_prk:list uint8 = [u8 0x65; u8 0x61; u8 0x65; u8 0x5f; u8 0x70; u8 0x72; u8 0x6b] in
  assert_norm (l_label_eae_prk == S.label_eae_prk_list);
  let label_eae_prk = createL l_label_eae_prk in

  labeled_extract_kem #cs o_eae_prk 5ul suite_id_kem 0ul empty 7ul label_eae_prk 32ul dh;

  [@inline_let]
  let l_label_shared_secret:list uint8 = [u8 0x73; u8 0x68; u8 0x61; u8 0x72; u8 0x65; u8 0x64; u8 0x5f; u8 0x73; u8 0x65; u8 0x63; u8 0x72; u8 0x65; u8 0x74] in
  assert_norm (l_label_shared_secret == S.label_shared_secret_list);
  let label_shared_secret = createL l_label_shared_secret in

  labeled_expand_kem #cs 5ul suite_id_kem (nsize_kem_hash_length cs) o_eae_prk 13ul label_shared_secret ctxlen kemcontext (nsize_kem_key cs) o_shared;

  pop_frame ()

val encap:
     #cs:S.ciphersuite
  -> o_shared: key_kem cs
  -> o_enc: key_dh_public cs
  -> skE: key_dh_secret cs
  -> pkR: serialized_point_dh cs
  -> Stack UInt32.t
    (requires fun h0 ->
      live h0 o_shared /\ live h0 o_enc /\
      live h0 skE /\ live h0 pkR /\
      disjoint o_shared skE /\ disjoint o_shared pkR /\
      disjoint o_shared o_enc /\ disjoint o_enc skE /\ disjoint o_enc pkR)
    (ensures fun h0 result h1 -> modifies (loc o_shared |+| loc o_enc) h0 h1 /\
      (let output = S.encap cs (as_seq h0 skE) (as_seq h0 pkR) in
       match result with
       | 0ul -> Some? output /\ (let shared, enc = Some?.v output in
         as_seq h1 o_shared `Seq.equal` shared /\ as_seq h1 o_enc `Seq.equal` enc)
       | 1ul -> None? output
       | _ -> False)
     )

#push-options "--z3rlimit 300"

[@ Meta.Attribute.inline_]
let encap #cs o_shared o_enc skE pkR =
  let h0 = ST.get () in
  let o_pkE = deserialize_public_key #cs o_enc in
  let res1 = DH.secret_to_public #cs o_pkE skE in
  if res1 = 0ul then (
    push_frame ();
    let h1 = ST.get () in
    assert (Some?.v (SDH.secret_to_public (S.kem_dh_of_cs cs) (as_seq h0 skE)) == as_seq h1 o_pkE);
    serialize_public_key o_enc o_pkE;
    let h2 = ST.get () in
    assert (as_seq h2 o_enc == S.serialize_public_key cs (as_seq h1 o_pkE));
    let o_dh = create (nsize_serialized_dh cs) (u8 0) in
    let res2 = DH.dh #cs o_dh skE pkR in
    if res2 = 0ul then (
      let h3 = ST.get () in
      assert (as_seq h3 o_dh == Some?.v (SDH.dh (S.kem_dh_of_cs cs) (as_seq h0 skE) (as_seq h0 pkR)));
      let o_kemcontext = create (nsize_two_public_dh cs) (u8 0) in
      copy (sub o_kemcontext 0ul (nsize_public_dh cs)) o_enc;
      let o_pkRm = sub o_kemcontext (nsize_public_dh cs) (nsize_public_dh cs) in
      let o_pkR = deserialize_public_key #cs o_pkRm in
      copy o_pkR pkR;
      serialize_public_key o_pkRm o_pkR;
      let h4 = ST.get () in
      assert (as_seq h4 o_pkRm == S.serialize_public_key cs (as_seq h0 pkR));


      let o_dhm = prepare_dh #cs o_dh in
      let h5 = ST.get () in
      assert (as_seq h5 o_kemcontext `Seq.equal` (as_seq h2 o_enc `Seq.append` as_seq h4 o_pkRm));
      extract_and_expand o_shared o_dhm (nsize_two_public_dh cs) o_kemcontext;
      let h6 = ST.get () in
      assert (as_seq h6 o_enc `Seq.equal` as_seq h2 o_enc);
      assert (as_seq h6 o_shared `Seq.equal` S.extract_and_expand cs (as_seq h5 o_dhm) (as_seq h5 o_kemcontext));
      pop_frame();
      0ul
    ) else (
      pop_frame ();
      1ul
    )

  ) else (
    assert (None? (S.encap cs (as_seq h0 skE) (as_seq h0 pkR)));
    1ul
  )

#pop-options

val decap:
     #cs:S.ciphersuite
  -> o_shared: key_kem cs
  -> enc: key_dh_public cs
  -> skR: key_dh_secret cs
  -> Stack UInt32.t
    (requires fun h0 ->
      live h0 o_shared /\ live h0 enc /\ live h0 skR /\
      disjoint o_shared enc /\ disjoint o_shared skR
    )
    (ensures fun h0 result h1 -> modifies (loc o_shared) h0 h1 /\
      (let output = S.decap cs (as_seq h0 enc) (as_seq h0 skR) in
       match result with
       | 0ul -> Some? output /\ as_seq h1 o_shared `Seq.equal` Some?.v output
       | 1ul -> None? output
       | _ -> False)
     )

#push-options "--z3rlimit 200"

[@ Meta.Attribute.inline_ ]
let decap #cs o_shared enc skR =
  push_frame ();
  let h0 = ST.get () in
  let pkE = deserialize_public_key #cs enc in
  let dh = create (nsize_serialized_dh cs) (u8 0) in
  let res1 = DH.dh #cs dh skR pkE in
  if res1 = 0ul then (
    let kemcontext = create (nsize_two_public_dh cs) (u8 0) in
    let pkRm = sub kemcontext (nsize_public_dh cs) (nsize_public_dh cs) in
    let pkR = deserialize_public_key #cs pkRm in

    let res2 = DH.secret_to_public #cs pkR skR in
    let h1 = ST.get () in

    if res2 = 0ul then (
      let h_m = ST.get () in
      assert (as_seq h_m enc `Seq.equal` as_seq h0 enc);
      copy (sub kemcontext 0ul (nsize_public_dh cs)) enc;

      serialize_public_key #cs pkRm pkR;

      let h2 = ST.get () in
      assert (as_seq h2 kemcontext `Seq.equal` (as_seq h0 enc `Seq.append` S.serialize_public_key cs (as_seq h1 pkR)));

      let dhm = prepare_dh #cs dh in

      extract_and_expand #cs o_shared dhm (nsize_two_public_dh cs) kemcontext;
      pop_frame ();
      0ul
    ) else (
      pop_frame ();
      1ul
    )
  ) else (
    pop_frame ();
    1ul
  )

#pop-options

inline_for_extraction noextract
val build_context_default:
     #cs:S.ciphersuite
  -> o_context: lbuffer uint8 (nsize_ks_ctx cs)
  -> psk_id_hash:lbuffer uint8 (nsize_hash_length cs)
  -> info_hash:lbuffer uint8 (nsize_hash_length cs)
  -> Stack unit
    (requires fun h0 ->
      live h0 o_context /\ live h0 psk_id_hash /\ live h0 info_hash /\
      disjoint o_context psk_id_hash /\ disjoint o_context info_hash)
    (ensures fun h0 _ h1 -> modifies (loc o_context) h0 h1 /\
      as_seq h1 o_context `Seq.equal` S.build_context cs S.Base (as_seq h0 psk_id_hash) (as_seq h0 info_hash))

inline_for_extraction noextract
let build_context_default #cs o_context psk_id_hash info_hash =
  init_id_mode S.Base (sub o_context 0ul 1ul);
  copy (sub o_context 1ul (nsize_hash_length cs)) psk_id_hash;
  copy (sub o_context (nsize_hash_length_plus_one cs) (nsize_hash_length cs)) info_hash

inline_for_extraction noextract
val key_schedule_core_base:
     #cs:S.ciphersuite
  -> o_ctx: context_s cs
  -> o_context : lbuffer uint8 (nsize_ks_ctx cs)
  -> o_secret : lbuffer uint8 (nsize_hash_length cs)
  -> suite_id : lbuffer uint8 10ul
  -> shared: key_kem cs
  -> infolen: size_t{v infolen <= max_length_info (S.hash_of_cs cs)}
  -> info: lbuffer uint8 infolen
  -> Stack unit
       (requires fun h0 ->
         ctx_invariant h0 o_ctx /\ live h0 o_context /\ live h0 o_secret /\
         live h0 shared /\ live h0 info /\ live h0 suite_id /\
         as_seq h0 suite_id == S.suite_id_hpke cs /\
         MB.all_disjoint [ctx_loc o_ctx; loc o_context; loc o_secret; loc shared; loc info; loc suite_id]
       )
       (ensures fun h0 _ h1 -> modifies (loc o_ctx.ctx_exporter |+| loc o_context |+| loc o_secret) h0 h1 /\
         (let context, exp_secret, secret = S.key_schedule_core cs S.Base (as_seq h0 shared) (as_seq h0 info) None in
          as_seq h1 o_context `Seq.equal` context /\
          as_seq h1 (o_ctx.ctx_exporter) `Seq.equal` exp_secret /\
          as_seq h1 o_secret `Seq.equal` secret)
       )

#push-options "--z3rlimit 300"

inline_for_extraction noextract
let key_schedule_core_base #cs o_ctx o_context o_secret suite_id shared infolen info =
  let h0' = ST.get () in
  lemma_includes_ctx_loc o_ctx;
  push_frame();
  let hi = ST.get () in
  [@inline_let]
  let l_psk_id_hash:list uint8 = [u8 0x70; u8 0x73; u8 0x6b; u8 0x5f; u8 0x69; u8 0x64; u8 0x5f; u8 0x68; u8 0x61; u8 0x73; u8 0x68] in
  assert_norm(l_psk_id_hash == S.label_psk_id_hash_list);
  let label_psk_id_hash = createL l_psk_id_hash in

  let hi1 = ST.get () in
  assert (modifies (loc suite_id) hi hi1);

  let o_psk_id_hash = create (nsize_hash_length cs) (u8 0) in
  let empty = sub suite_id 0ul 0ul in
  let h0 = ST.get() in
  assert (as_seq h0 empty `Seq.equal` Lib.ByteSequence.lbytes_empty);

  labeled_extract_hash #cs o_psk_id_hash 10ul suite_id 0ul empty 11ul label_psk_id_hash 0ul empty;
  let h1 = ST.get() in
  assert (as_seq h1 o_psk_id_hash `Seq.equal` S.labeled_extract (S.hash_of_cs cs) (S.suite_id_hpke cs) Lib.ByteSequence.lbytes_empty S.label_psk_id_hash S.default_psk_id);

  assert (modifies (loc o_psk_id_hash) hi1 h1);
  assert (modifies (loc suite_id |+| loc o_psk_id_hash) hi h1);

  [@inline_let]
  let l_label_info_hash:list uint8 = [u8 0x69; u8 0x6e; u8 0x66; u8 0x6f; u8 0x5f; u8 0x68; u8 0x61; u8 0x73; u8 0x68] in
  assert_norm (l_label_info_hash == S.label_info_hash_list);
  let label_info_hash = createL l_label_info_hash in

  let o_info_hash = create (nsize_hash_length cs) (u8 0) in

  labeled_extract_hash #cs o_info_hash 10ul suite_id 0ul empty 9ul label_info_hash infolen info;

  let h2 = ST.get () in
  assert (modifies (loc o_info_hash) h1 h2);
  assert (modifies (loc suite_id |+| loc o_psk_id_hash |+| loc o_info_hash) hi h2);

  build_context_default #cs o_context o_psk_id_hash o_info_hash;

  let h3 = ST.get () in
  assert (modifies (loc o_context) h2 h3);
  assert (modifies (loc suite_id |+| loc o_psk_id_hash |+| loc o_info_hash |+| loc o_context) hi h3);

  [@inline_let]
  let l_label_secret:list uint8 = [u8 0x73; u8 0x65; u8 0x63; u8 0x72; u8 0x65; u8 0x74] in
  assert_norm (l_label_secret == S.label_secret_list);
  let label_secret = createL l_label_secret in

  labeled_extract_hash #cs o_secret 10ul suite_id (nsize_kem_key cs) shared 6ul label_secret 0ul empty;

  let h4 = ST.get () in
  assert (modifies (loc o_secret) h3 h4);
  assert (modifies (loc suite_id |+| loc o_psk_id_hash |+| loc o_info_hash |+| loc o_context |+| loc o_secret) hi h4);

  [@inline_let]
  let l_label_exp:list uint8 = [u8 0x65; u8 0x78; u8 0x70] in
  assert_norm (l_label_exp == S.label_exp_list);
  let label_exp = createL l_label_exp in

  labeled_expand_hash #cs 10ul suite_id (nsize_hash_length cs) o_secret 3ul label_exp (nsize_ks_ctx cs) o_context (nsize_hash_length cs) o_ctx.ctx_exporter;

  let hf = ST.get () in
  assert (modifies (loc o_ctx.ctx_exporter) h4 hf);
  assert (modifies (loc suite_id |+| loc o_psk_id_hash |+| loc o_info_hash |+| loc o_context |+| loc o_secret |+| loc o_ctx.ctx_exporter) hi hf);

  pop_frame()

#pop-options

inline_for_extraction noextract
val key_schedule_end_base:
     #cs:S.ciphersuite
  -> o_ctx: context_s cs
  -> suite_id:lbuffer uint8 10ul
  -> context: lbuffer uint8 (nsize_ks_ctx cs)
  -> secret: lbuffer uint8 (nsize_hash_length cs) ->
  Stack unit
    (requires fun h -> ctx_invariant h o_ctx /\ live h context /\ live h secret /\ live h suite_id /\
      B.loc_disjoint (ctx_loc o_ctx) (loc context) /\
      B.loc_disjoint (ctx_loc o_ctx) (loc secret) /\
      B.loc_disjoint (ctx_loc o_ctx) (loc suite_id) /\
      disjoint context secret /\
      as_seq h suite_id == S.suite_id_hpke cs
    )
    (ensures fun h0 _ h1 -> modifies (ctx_loc o_ctx) h0 h1 /\
      as_ctx h1 o_ctx == S.key_schedule_end cs S.Base (as_seq h0 context) (as_seq h0 o_ctx.ctx_exporter) (as_seq h0 secret)
    )

inline_for_extraction noextract
let key_schedule_end_base #cs o_ctx suite_id context secret =
  match S.aead_of_cs cs with
  | S.ExportOnly ->
    upd o_ctx.ctx_seq 0ul 0uL;
    let h1 = ST.get () in
    assert (as_seq h1 o_ctx.ctx_key `Seq.equal` Lib.ByteSequence.lbytes_empty);
    assert (as_seq h1 o_ctx.ctx_nonce `Seq.equal` Lib.ByteSequence.lbytes_empty)

  | _ ->
    push_frame ();
    [@inline_let]
    let l_label_key:list uint8 = [u8 0x6b; u8 0x65; u8 0x79] in
    assert_norm (l_label_key == S.label_key_list);
    let label_key = createL l_label_key in

    labeled_expand_hash #cs 10ul suite_id (nsize_hash_length cs) secret 3ul label_key (nsize_ks_ctx cs) context (nsize_aead_key cs) o_ctx.ctx_key;

    [@inline_let]
    let l_label_base_nonce:list uint8 = [u8 0x62; u8 0x61; u8 0x73; u8 0x65; u8 0x5f; u8 0x6e; u8 0x6f; u8 0x6e; u8 0x63; u8 0x65] in
    assert_norm (l_label_base_nonce == S.label_base_nonce_list);
    let label_base_nonce = createL l_label_base_nonce in

    labeled_expand_hash #cs 10ul suite_id (nsize_hash_length cs) secret 10ul label_base_nonce (nsize_ks_ctx cs) context (nsize_aead_nonce cs) o_ctx.ctx_nonce;

    upd o_ctx.ctx_seq 0ul 0uL;
    pop_frame ()


val key_schedule_base:
     #cs:S.ciphersuite
  -> o_ctx: context_s cs
  -> shared: key_kem cs
  -> infolen: size_t{v infolen <= max_length_info (S.hash_of_cs cs)}
  -> info: lbuffer uint8 infolen
  -> Stack unit
       (requires fun h0 ->
         ctx_invariant h0 o_ctx /\ live h0 shared /\ live h0 info /\
         B.loc_disjoint (ctx_loc o_ctx) (loc shared) /\
         B.loc_disjoint (ctx_loc o_ctx) (loc info) /\
         disjoint shared info
       )
       (ensures fun h0 _ h1 -> modifies (ctx_loc o_ctx) h0 h1 /\
         (let ctx = S.key_schedule cs S.Base (as_seq h0 shared) (as_seq h0 info) None in
         as_ctx h1 o_ctx == ctx))

#push-options "--z3rlimit 100"

[@ Meta.Attribute.inline_ ]
let key_schedule_base #cs o_ctx shared infolen info =
  push_frame();
  let o_context = create (nsize_ks_ctx cs) (u8 0) in
  let o_secret = create (nsize_hash_length cs) (u8 0) in

  let suite_id = create 10ul (u8 0) in
  init_suite_id #cs suite_id;

  key_schedule_core_base #cs o_ctx o_context o_secret suite_id shared infolen info;
  key_schedule_end_base #cs o_ctx suite_id o_context o_secret;
  pop_frame()

#pop-options

#push-options "--z3rlimit 200"

[@ Meta.Attribute.specialize]
let setupBaseS #cs o_pkE o_ctx skE pkR infolen info =
  push_frame();
  let o_shared = create (nsize_kem_key cs) (u8 0) in
  let res = encap o_shared o_pkE skE pkR in
  if res = 0ul then (
    key_schedule_base o_ctx o_shared infolen info;
    pop_frame();
    res
  ) else (pop_frame (); res)

#pop-options

#push-options "--z3rlimit 200"

[@ Meta.Attribute.specialize]
let setupBaseR #cs o_ctx enc skR infolen info =
  push_frame();
  let pkR = create (nsize_serialized_dh cs) (u8 0) in
  let res1 = DH.secret_to_public #cs pkR skR in
  if res1 = 0ul then (
    let shared = create (nsize_kem_key cs) (u8 0) in
    let res2 = decap #cs shared enc skR in
    if res2 = 0ul then (
      key_schedule_base #cs o_ctx shared infolen info;
      pop_frame ();
      0ul
    ) else (
      pop_frame ();
      1ul
    )
  ) else (
    pop_frame ();
    1ul
  )

#pop-options

inline_for_extraction noextract
val nat_to_bytes_be_12:
  o:lbuffer uint8 12ul ->
  l:uint64 ->
  Stack unit
    (requires fun h -> live h o /\ as_seq h o `Seq.equal` Lib.Sequence.create 12 (u8 0))
    (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\
      (assert_norm (pow2 (8 * 12) == 79228162514264337593543950336);
      as_seq h1 o `Seq.equal` Lib.ByteSequence.nat_to_bytes_be 12 (v l)))

let lemma_nat_to_bytes_12 (n:nat{n < pow2 64 /\ n < pow2 96})
  : Lemma (Lib.ByteSequence.nat_to_bytes_be 12 n `Seq.equal`
    (Lib.Sequence.create 4 (u8 0) `Seq.append` Lib.ByteSequence.nat_to_bytes_be 8 n))
  =
  Lib.ByteSequence.index_nat_to_intseq_be #U8 #SEC 8 n 0;
  Lib.ByteSequence.index_nat_to_intseq_be #U8 #SEC 8 n 1;
  Lib.ByteSequence.index_nat_to_intseq_be #U8 #SEC 8 n 2;
  Lib.ByteSequence.index_nat_to_intseq_be #U8 #SEC 8 n 3;
  Lib.ByteSequence.index_nat_to_intseq_be #U8 #SEC 8 n 4;
  Lib.ByteSequence.index_nat_to_intseq_be #U8 #SEC 8 n 5;
  Lib.ByteSequence.index_nat_to_intseq_be #U8 #SEC 8 n 6;
  Lib.ByteSequence.index_nat_to_intseq_be #U8 #SEC 8 n 7;

  Lib.ByteSequence.index_nat_to_intseq_be #U8 #SEC 12 n 0;
  Lib.ByteSequence.index_nat_to_intseq_be #U8 #SEC 12 n 1;
  Lib.ByteSequence.index_nat_to_intseq_be #U8 #SEC 12 n 2;
  Lib.ByteSequence.index_nat_to_intseq_be #U8 #SEC 12 n 3;
  Lib.ByteSequence.index_nat_to_intseq_be #U8 #SEC 12 n 4;
  Lib.ByteSequence.index_nat_to_intseq_be #U8 #SEC 12 n 5;
  Lib.ByteSequence.index_nat_to_intseq_be #U8 #SEC 12 n 6;
  Lib.ByteSequence.index_nat_to_intseq_be #U8 #SEC 12 n 7;
  Lib.ByteSequence.index_nat_to_intseq_be #U8 #SEC 12 n 8;
  Lib.ByteSequence.index_nat_to_intseq_be #U8 #SEC 12 n 9;
  Lib.ByteSequence.index_nat_to_intseq_be #U8 #SEC 12 n 10;
  Lib.ByteSequence.index_nat_to_intseq_be #U8 #SEC 12 n 11;

  assert_norm (pow2 (8 * 11) == 309485009821345068724781056);
  FStar.Math.Lemmas.lemma_div_lt_nat n (8 * 11) 64;
  assert_norm (pow2 (8 * 10) == 1208925819614629174706176);
  FStar.Math.Lemmas.lemma_div_lt_nat n (8 * 10) 64;
  assert_norm (pow2 (8 * 9) == 4722366482869645213696);
  FStar.Math.Lemmas.lemma_div_lt_nat n (8 * 9) 64;
  assert_norm (pow2 (8 * 8) == 18446744073709551616);
  FStar.Math.Lemmas.lemma_div_lt_nat n (8 * 8) 64

inline_for_extraction noextract
let nat_to_bytes_be_12 o l =
  Lib.ByteBuffer.uint_to_bytes_be (sub o 4ul 8ul) l;
  let h1 = ST.get () in
  assert (as_seq h1 (gsub o 4ul 8ul) `Seq.equal` Lib.ByteSequence.uint_to_bytes_be l);

  Lib.ByteSequence.lemma_uint_to_bytes_be_preserves_value l;
  assert (Lib.ByteSequence.nat_from_bytes_be (as_seq h1 (gsub o 4ul 8ul)) == v l);

  Lib.ByteSequence.lemma_nat_from_to_bytes_be_preserves_value (as_seq h1 (gsub o 4ul 8ul)) 8;
  assert (as_seq h1 (gsub o 4ul 8ul) == Lib.ByteSequence.nat_to_bytes_be 8 (v l));

  assert_norm (pow2 (8 * 12) == 79228162514264337593543950336);
  lemma_nat_to_bytes_12 (v l);

  assert (as_seq h1 (gsub o 0ul 4ul) `Seq.equal` Lib.Sequence.create 4 (u8 0))

inline_for_extraction noextract
val context_compute_nonce:
     #cs:S.ciphersuite
  -> ctx:context_s cs
  -> seq:seq_aead cs
  -> o_nonce: nonce_aead cs
  -> Stack unit
    (requires fun h ->
      S.is_valid_not_export_only_ciphersuite cs /\
      ctx_invariant h ctx /\ live h o_nonce /\ B.loc_disjoint (ctx_loc ctx) (loc o_nonce))
    (ensures fun h0 _ h1 -> modifies (loc o_nonce) h0 h1 /\
      as_seq h1 o_nonce `Seq.equal` S.context_compute_nonce cs (as_ctx h0 ctx) (UInt64.v seq)
    )

inline_for_extraction noextract
let context_compute_nonce #cs ctx seq o_nonce =
  push_frame ();
  let enc = create (nsize_aead_nonce cs) (u8 0) in
  nat_to_bytes_be_12 enc (secret seq);
  C.Loops.map2 o_nonce enc ctx.ctx_nonce 12ul (logxor #U8 #SEC);
  pop_frame ()


val context_increment_seq:
     #cs:S.ciphersuite
  -> ctx:context_s cs
  -> Stack UInt32.t
     (requires fun h -> S.is_valid_not_export_only_ciphersuite cs /\ ctx_invariant h ctx)
     (ensures fun h0 res h1 -> modifies (ctx_loc ctx) h0 h1 /\
       (let new_ctx = S.context_increment_seq cs (as_ctx h0 ctx) in
       match res with
       | 0ul -> Some? new_ctx /\ as_ctx h1 ctx == Some?.v new_ctx
       | 1ul -> True
       | _ -> False)
     )

let context_increment_seq #cs ctx =
  let s = index ctx.ctx_seq 0ul in
  assert_norm (maxint U64 == 18446744073709551615);
  if s = 18446744073709551615uL then
    1ul
  else (
    let s' = s +. 1uL in
    assert (v s' == v s + 1);
    (* Need to trigger that s' is smaller than max_seq *)
    assert_norm (pow2 96 == 79228162514264337593543950336);
    upd ctx.ctx_seq 0ul s';
    0ul
  )

val context_seal:
     #cs:S.ciphersuite
  -> _:squash (S.is_valid_not_export_only_ciphersuite cs)
  -> ctx:context_s cs
  -> aadlen: size_t {v aadlen <= SAEAD.max_length (S.aead_alg_of cs)}
  -> aad: lbuffer uint8 aadlen
  -> plainlen: size_t {v plainlen <= SAEAD.max_length (S.aead_alg_of cs) /\ v plainlen + 16 <= max_size_t}
  -> plain: lbuffer uint8 plainlen
  -> o_ct: lbuffer uint8 (size (v plainlen +  16))
  -> Stack UInt32.t
     (requires fun h ->
       ctx_invariant h ctx /\ live h aad /\ live h plain /\ live h o_ct /\
       disjoint o_ct aad /\ disjoint o_ct plain /\
       B.loc_disjoint (ctx_loc ctx) (loc aad) /\
       B.loc_disjoint (ctx_loc ctx) (loc plain) /\
       B.loc_disjoint (ctx_loc ctx) (loc o_ct)
     )
     (ensures fun h0 result h1 -> modifies (ctx_loc ctx |+| loc o_ct) h0 h1 /\
       (let sealed = S.context_seal cs (as_ctx h0 ctx) (as_seq h0 aad) (as_seq h0 plain) in
         match result with
         | 0ul -> Some? sealed /\
           (let new_ctx, ct = Some?.v sealed in
           as_ctx h1 ctx == new_ctx /\ as_seq h1 o_ct `Seq.equal` ct)
         | 1ul -> True
         | _ -> False)
       )

#push-options "--z3rlimit 100"

[@ Meta.Attribute.inline_ ]
let context_seal #cs _ ctx aadlen aad plainlen plain o_ct =
  push_frame ();
  let nonce = create (nsize_aead_nonce cs) (u8 0) in
  let s = index ctx.ctx_seq 0ul in
  context_compute_nonce #cs ctx s nonce;
  AEAD.aead_encrypt #cs () ctx.ctx_key nonce aadlen aad plainlen plain o_ct;
  let res = context_increment_seq #cs ctx in
  pop_frame();
  res

#pop-options

#push-options "--z3rlimit 300"

[@ Meta.Attribute.specialize]
let sealBase #cs skE pkR infolen info aadlen aad plainlen plain o_enc o_ct =
  push_frame ();
  let ctx_key = create (nsize_aead_key cs) (u8 0) in
  let ctx_nonce = create (nsize_aead_nonce cs) (u8 0) in
  let ctx_seq = create 1ul 0uL in
  let ctx_exporter = create (nsize_hash_length cs) (u8 0) in
  let o_ctx:context_s cs = {ctx_key; ctx_nonce; ctx_seq; ctx_exporter} in
  let h = ST.get () in
  assert (ctx_invariant h o_ctx);
  let res = setupBaseS #cs o_enc o_ctx skE pkR infolen info in
  if res = 0ul then (
    let res = context_seal #cs () o_ctx aadlen aad plainlen plain o_ct in
    pop_frame ();
    res
  ) else (
    pop_frame ();
    1ul
  )

#pop-options

val context_open:
     #cs:S.ciphersuite
  -> _:squash (S.is_valid_not_export_only_ciphersuite cs)
  -> ctx:context_s cs
  -> aadlen: size_t {v aadlen <= SAEAD.max_length (S.aead_alg_of cs)}
  -> aad: lbuffer uint8 aadlen
  -> ctlen: size_t {16 < v ctlen /\ v ctlen <= SAEAD.max_length (S.aead_alg_of cs) }
  -> ct: lbuffer uint8 ctlen
  -> o_pt: lbuffer uint8 (size (v ctlen - 16))
  -> Stack UInt32.t
     (requires fun h ->
       ctx_invariant h ctx /\ live h aad /\ live h ct /\ live h o_pt /\
       disjoint o_pt aad /\ disjoint o_pt ct /\
       B.loc_disjoint (ctx_loc ctx) (loc aad) /\
       B.loc_disjoint (ctx_loc ctx) (loc ct) /\
       B.loc_disjoint (ctx_loc ctx) (loc o_pt)
     )
     (ensures fun h0 result h1 -> modifies (ctx_loc ctx |+| loc o_pt) h0 h1 /\
       (let sealed = S.context_open cs (as_ctx h0 ctx) (as_seq h0 aad) (as_seq h0 ct) in
         match result with
         | 0ul -> Some? sealed /\
           (let new_ctx, pt = Some?.v sealed in
           as_ctx h1 ctx == new_ctx /\ as_seq h1 o_pt `Seq.equal` pt)
         | 1ul -> True
         | _ -> False)
       )

[@ Meta.Attribute.inline_ ]
let context_open #cs _ ctx aadlen aad ctlen ct o_pt =
  push_frame ();
  let nonce = create (nsize_aead_nonce cs) (u8 0) in
  let s = index ctx.ctx_seq 0ul in
  context_compute_nonce #cs ctx s nonce;
  let res = AEAD.aead_decrypt #cs () ctx.ctx_key nonce aadlen aad (ctlen -. 16ul) o_pt ct in
  if res = 0ul then (
    let res = context_increment_seq #cs ctx in
    pop_frame();
    res
  ) else (
    pop_frame();
    1ul
  )

#push-options "--z3rlimit 400"

[@ Meta.Attribute.specialize]
let openBase #cs pkE skR infolen info aadlen aad ctlen ct o_pt =
  push_frame ();
  let ctx_key = create (nsize_aead_key cs) (u8 0) in
  let ctx_nonce = create (nsize_aead_nonce cs) (u8 0) in
  let ctx_seq = create 1ul 0uL in
  let ctx_exporter = create (nsize_hash_length cs) (u8 0) in
  let o_ctx:context_s cs = {ctx_key; ctx_nonce; ctx_seq; ctx_exporter} in
  let h = ST.get () in
  let res = setupBaseR #cs o_ctx pkE skR infolen info in
  if res = 0ul then (
    let res = context_open #cs () o_ctx aadlen aad ctlen ct o_pt in
    pop_frame();
    res
  ) else (
    pop_frame ();
    1ul
  )

#pop-options
