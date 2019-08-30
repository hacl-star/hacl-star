module Spec.QUIC


module S = FStar.Seq
module H = Spec.Hash
module HD = Spec.Hash.Definitions
module AEAD = Spec.AEAD

type byte = FStar.UInt8.t

let supported_hash = function
  | HD.SHA1 | HD.SHA2_256 | HD.SHA2_384 | HD.SHA2_512 -> true
  | _ -> false

let supported_aead = function
  | AEAD.AES128_GCM | AEAD.AES256_GCM | AEAD.CHACHA20_POLY1305 -> true
  | _ -> false

type ha = a:HD.hash_alg{supported_hash a}
type ea = a:AEAD.alg{supported_aead a}

type bytes = s:S.seq byte
type lbytes (n:nat) = b:bytes{S.length b = n}

// Move from Hashing.Spec to Spec.Hash?
let keysized (a:ha) (l:nat) =
  l < HD.max_input_length a /\ l + HD.block_length a < pow2 32
let hashable (a:ha) (l:nat) = l < HD.max_input_length a

// AEAD plain and ciphertext. We want to guarantee that regardless
// of the header size (max is 54), the neader + ciphertext + tag fits in a buffer
let max_plain_length : n:nat{forall a. n <= AEAD.max_length a} = pow2 32 - 70
let max_cipher_length : n:nat{forall a. n <= AEAD.max_length a + AEAD.tag_length a} = pow2 32 - 54

type pbytes = b:bytes{let l = S.length b in 3 <= l /\ l < max_plain_length}
type cbytes = b:bytes{let l = S.length b in 19 <= l /\ l < max_cipher_length}
type packet = b:bytes{let l = S.length b in 21 <= l /\ l < pow2 32}

let ae_keysize (a:ea) =
  match a with
  | AEAD.AES128_GCM -> 16
  | _ -> 32

val derive_secret:
  a: ha ->
  prk: bytes ->
  label: bytes ->
  len: nat ->
  Ghost (lbytes len)
  (requires len <= 255 /\
    S.length label <= 244 /\
    keysized a (S.length prk))
  (ensures fun out -> True)

type nat2 = n:nat{n < 4}
type nat4 = n:nat{n < 16}
type nat32 = n:nat{n < pow2 32}
type nat62 = n:nat{n < pow2 62}

let add3 (n:nat4) : n:nat{n=0 \/ (n >= 4 /\ n <= 18)} = if n = 0 then 0 else 3+n
let sub3 (n:nat{n = 0 \/ (n >= 4 /\ n <= 18)}) : nat4 = if n = 0 then 0 else n-3
type qbytes (n:nat4) = lbytes (add3 n)
type vlsize = n:nat{n == 1 \/ n == 2 \/ n == 4 \/ n == 8}

let vlen (n:nat62) : vlsize =
  if n < pow2 6 then 1
  else if n < pow2 14 then 2
  else if n < pow2 30 then 4
  else 8

val encode_varint: n:nat62 -> lbytes (vlen n)
val parse_varint: b:bytes{S.length b > 0} -> option (n:nat{n < pow2 62} * bytes)

val lemma_varint: (n:nat62) -> (suff:bytes) -> Lemma (parse_varint S.(encode_varint n @| suff) == Some (n,suff))


type header =
  | Short:
    spin: bool ->
    phase: bool ->
    cid:bytes{let l = S.length cid in l == 0 \/ (4 <= l /\ l <= 18)} ->
    header
  | Long:
    typ: nat2 ->
    version: nat32 ->
    dcil: nat4 ->
    scil: nat4 ->
    dcid: qbytes dcil ->
    scid: qbytes scil ->
    len: nat{len < max_cipher_length} ->
    header

type h_result =
| H_Success:
  pn_len: nat2 ->
  npn: lbytes (1 + pn_len) ->
  h: header ->
  c: cbytes ->
  h_result
| H_Failure

let header_len (h:header) (pn_len:nat2) : n:nat{2 <= n /\ n <= 54} =
  match h with
  | Short spin phase cid ->
    1 + S.length cid + 1 + pn_len
  | Long is_hs version dcil scil dcid scid plen ->
    let _ = assert_norm(max_cipher_length < pow2 62) in
    6 + add3 dcil + add3 scil + vlen plen + 1 + pn_len

let cid_len : header -> nat4 = function
  | Short _ _ cid -> sub3 (S.length cid)
  | Long _ _ dcil _ _ _ _ -> dcil

val format_header: h:header -> pn_len:nat2 -> npn: lbytes (1+pn_len) ->
  lbytes (header_len h pn_len)

val parse_header: b:packet -> cid_len: nat4 -> h_result

val lemma_header_parsing_correct:
  h: header ->
  pn_len: nat2 ->
  npn: lbytes (1+pn_len) ->
  c: cbytes{Long? h ==> S.length c = Long?.len h} ->
  Lemma (parse_header S.(format_header h pn_len npn @| c) (cid_len h)
    == H_Success pn_len npn h c)

// N.B. this is only true for a given DCID len
val lemma_header_parsing_safe: b1:packet -> b2:packet -> cl:nat4 -> Lemma
  (requires
    H_Success? (parse_header b1 cl) /\
    H_Success? (parse_header b2 cl) /\
    parse_header b1 cl == parse_header b2 cl)
  (ensures b1 == b2)

// Header protection only
val header_encrypt: a:ea ->
  hpk: lbytes (ae_keysize a) ->
  h: header ->
  pn_len: nat2 ->
  npn: lbytes (1+pn_len) ->
  c: cbytes ->
  packet

// Note that cid_len cannot be parsed from short headers
val header_decrypt: a:ea ->
  hpk: lbytes (ae_keysize a) ->
  cid_len: nat4 ->
  p: packet ->
  h_result

// This is just functional correctness, but does not guarantee security:
// decryption can succeed on an input that is not the encryption
// of the same arguments (see next lemma)
val lemma_header_encryption_correct:
  a:ea ->
  k:lbytes (ae_keysize a) ->
  h: header ->
  pn_len: nat2 ->
  npn: lbytes (1+pn_len) ->
  c: cbytes ->
  Lemma (header_decrypt a k (cid_len h)
    (header_encrypt a k h pn_len npn c)
    == H_Success pn_len npn h c)

// Even though parse_header is a secure parser, decryption is malleable:
// it is possible to successfully decrypt with a different npn
val lemma_header_encryption_malleable:
  a:ea ->
  k:lbytes (ae_keysize a) ->
  c:cbytes ->
  spin:bool -> phase:bool ->
  cid:bytes{let l = S.length cid in 4 <= l /\ l <= 17} ->
  x: lbytes 1 -> // Arbitrary byte
  npn:lbytes 1 ->
  Lemma (exists (npn':lbytes 2).
    header_decrypt a k (S.length cid - 3) (header_encrypt a k
      (Short spin phase S.(cid @| x)) 0 npn c)
    == H_Success 1 npn' (Short spin phase cid) c)

type result =
| Success: pn_len:nat2 ->
  pn: nat62 ->
  h: header ->
  plain: pbytes ->
  result
| Failure

val encrypt:
  a: ea ->
  k: lbytes (AEAD.key_length a) ->
  static_iv: lbytes 12 ->
  hpk: lbytes (ae_keysize a) ->
  pn_len: nat2 ->
  pn: nat62 ->
  h: header ->
  plain: pbytes{Long? h ==> Long?.len h == S.length plain + AEAD.tag_length a} ->
  packet

val decrypt:
  a: ea ->
  k: lbytes (AEAD.key_length a) ->
  static_iv: lbytes 12 ->
  hpk: lbytes (ae_keysize a) ->
  last: nat62 ->
  cid_len: nat4 ->
  packet: packet ->
  result

val lemma_encrypt_correct:
  a: ea ->
  k: lbytes (AEAD.key_length a) ->
  siv: lbytes 12 ->
  hpk: lbytes (ae_keysize a) ->
  pn_len: nat2 ->
  pn: nat62 ->
  h: header ->
  p: pbytes{Long? h ==> Long?.len h == S.length p + AEAD.tag_length a} ->
  Lemma (decrypt a k siv hpk (if pn=0 then 0 else pn-1) (cid_len h)
    (encrypt a k siv hpk pn_len pn h p)
    == Success pn_len pn h p)
