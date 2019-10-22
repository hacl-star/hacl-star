module Spec.QUIC

module S = FStar.Seq
module HD = Spec.Hash.Definitions
module AEAD = Spec.Agile.AEAD

type byte = FStar.UInt8.t

// JP: should we allow inversion on either hash algorithm or AEAD algorithm?
#set-options "--max_fuel 0 --max_ifuel 0"

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
  l <= HD.max_input_length a /\ l + HD.block_length a < pow2 32
let hashable (a:ha) (l:nat) = l <= HD.max_input_length a

// AEAD plain and ciphertext. We want to guarantee that regardless
// of the header size (max is 54), the neader + ciphertext + tag fits in a buffer
// JP: perhaps cleaner with a separate lemma; any reason for putting this in a refinement?
let max_plain_length: n:nat {
  forall a. {:pattern AEAD.max_length a} n <= AEAD.max_length a
} =
  pow2 32 - 70

let max_cipher_length : n:nat {
  forall a. {:pattern AEAD.max_length a \/ AEAD.tag_length a }
    n <= AEAD.max_length a + AEAD.tag_length a
} =
  pow2 32 - 54

type pbytes = b:bytes{let l = S.length b in 3 <= l /\ l < max_plain_length}
type cbytes = b:bytes{let l = S.length b in 19 <= l /\ l < max_cipher_length}
type packet = b:bytes{let l = S.length b in 21 <= l /\ l < pow2 32}

// JP: this is Spec.Agile.Cipher.key_length
let ae_keysize (a:ea) =
  match a with
  | AEAD.AES128_GCM -> 16
  | _ -> 32

// Static byte sequences to be fed into secret derivation. Marked as inline, so
// that they can be used as arguments to gcmalloc_of_list for top-level arrays.
inline_for_extraction
val label_key: lbytes 3
inline_for_extraction
val label_iv: lbytes 2
inline_for_extraction
val label_hp: lbytes 2

val derive_secret:
  a: ha ->
  prk:Spec.Hash.Definitions.bytes_hash a ->
  label: bytes ->
  len: nat ->
  Pure (lbytes len)
  (requires len <= 255 /\
    S.length label <= 244 /\
    keysized a (S.length prk)
    )
  (ensures fun out -> True)

type nat2 = n:nat{n < 4}
type nat4 = n:nat{n < 16}
type nat32 = n:nat{n < pow2 32}
type nat62 = n:nat{n < pow2 62}

let add3 (n:nat4) : n:nat{n=0 \/ (n >= 4 /\ n <= 18)} = if n = 0 then 0 else 3+n
let sub3 (n:nat{n = 0 \/ (n >= 4 /\ n <= 18)}) : nat4 = if n = 0 then 0 else n-3
type qbytes (n:nat4) = lbytes (add3 n)
type vlsize = n:nat{n == 1 \/ n == 2 \/ n == 4 \/ n == 8}
type npn = b:bytes{1 <= S.length b /\ S.length b <= 4}

let vlen (n:nat62) : vlsize =
  if n < pow2 6 then 1
  else if n < pow2 14 then 2
  else if n < pow2 30 then 4
  else 8

val encode_varint: n:nat62 -> lbytes (vlen n)
val parse_varint: b:bytes -> option (n:nat62 * bytes)

val lemma_varint: (n:nat62) -> (suff:bytes) ->
  Lemma (parse_varint S.(encode_varint n @| suff) == Some (n,suff))


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
  npn: npn ->
  h: header ->
  c: cbytes ->
  h_result
| H_Failure

// JP: seems appropriate for this module...?
let _: squash (inversion header) = allow_inversion header

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

val format_header: h:header -> npn:npn ->
  lbytes (header_len h (S.length npn-1))

val parse_header: b:packet -> cid_len: nat4 -> h_result

val lemma_header_parsing_correct:
  h: header ->
  npn: npn ->
  c: cbytes{Long? h ==> S.length c = Long?.len h} ->
  Lemma (
    parse_header S.(format_header h npn @| c) (cid_len h)
    == H_Success npn h c)

// N.B. this is only true for a given DCID len
val lemma_header_parsing_safe: b1:packet -> b2:packet -> cl:nat4 -> Lemma
  (requires parse_header b1 cl = parse_header b2 cl)
  (ensures parse_header b1 cl = H_Failure \/ b1 = b2)

// Header protection only
val header_encrypt: a:ea ->
  hpk: lbytes (ae_keysize a) ->
  h: header ->
  npn: npn ->
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
  h:header ->
  npn:npn ->
  c: cbytes{Long? h ==> S.length c = Long?.len h} ->
  Lemma (
    header_decrypt a k (cid_len h) (header_encrypt a k h npn c)
    == H_Success npn h c)


// insert bytes x in b at position i
val insert : x:bytes -> b:bytes -> i:nat -> Pure bytes
  (requires i < S.length b)
  (ensures fun res ->
    S.length res = S.length b + S.length x /\ (
    forall j.
      (j < i ==> S.index res j = S.index b j) /\
      ((i <= j /\ j < i + S.length x) ==> S.index res j = S.index x (j-i)) /\
      (i + S.length x <= j ==> S.index res j = S.index b (j-S.length x))))


// Even though parse_header is a secure parser, decryption is malleable:
// it is possible to successfully decrypt while parsing part of the
// encrypted npn into the cid
val lemma_header_encryption_malleable:
  a:ea ->
  k:lbytes (ae_keysize a) ->
  c:cbytes ->
  spin:bool -> phase:bool ->
  cid:lbytes 4 -> // Arbitrary cid (minimal size to simplify the proof)
  x: byte -> // Arbitrary part of the npn, transferred to the cid (after xor)
  npn:byte -> // Rest of the npn
  y: byte -> // Arbitrary byte, inserted by the adversay in the encrypted header
  Lemma (
    let p = header_encrypt a k (Short spin phase cid) S.(create 1 x @| create 1 npn) c in
    let p' = insert (S.create 1 y) p 7 in
    S.length p' < pow2 32 /\
    (exists h' npn'. header_decrypt a k 2 p' = H_Success npn' h' c))



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



/// compression of the packet number


let bound_npn (pn_len:nat2) = pow2 (8 `op_Multiply` (pn_len+1))

let in_window (pn_len:nat2) (last pn:nat) =
  let h = bound_npn pn_len in
  (last+1 < h/2 /\ pn < h) \/
  (last+1 >= pow2 62 - h/2 /\ pn >= pow2 62 - h) \/
  (last+1 - h/2 < pn /\ pn <= last+1 + h/2)

val reduce_pn :
  pn_len:nat2 ->
  pn:nat62 ->
  npn:nat{npn < bound_npn pn_len}

val expand_pn :
  pn_len:nat2 ->
  last:nat{last+1 < pow2 62} ->
  npn:nat{npn < bound_npn pn_len} ->
  pn:nat62{in_window pn_len last pn /\ pn % bound_npn pn_len = npn}

val lemma_parse_pn_correct : pn_len:nat2 -> last:nat{last+1 < pow2 62} -> pn:nat62 -> Lemma
  (requires in_window pn_len last pn)
  (ensures expand_pn pn_len last (reduce_pn pn_len pn) = pn)



/// decryption and correctness

val decrypt:
  a: ea ->
  k: lbytes (AEAD.key_length a) ->
  static_iv: lbytes 12 ->
  hpk: lbytes (ae_keysize a) ->
  last: nat{last+1 < pow2 62} ->
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
  last: nat{last+1 < pow2 62} ->
  h: header ->
  p: pbytes{Long? h ==> Long?.len h == S.length p + AEAD.tag_length a} -> Lemma
  (requires in_window pn_len last pn)
  (ensures
    decrypt a k siv hpk last (cid_len h)
      (encrypt a k siv hpk pn_len pn h p)
    == Success pn_len pn h p)
