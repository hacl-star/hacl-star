open Unsigned


module type Buffer = sig
  type t
  type buf
  val empty: bytes
  val size_uint32 : bytes -> uint32
  val ctypes_buf : bytes -> buf
  val size : bytes -> int
  val equal : bytes -> bytes -> bool
  val disjoint : bytes -> bytes -> bool
  val sub : bytes -> int -> int -> bytes
  val z_compare : bytes -> Z.t -> int
end
(** Abstract representation of buffers *)

module CBytes : Buffer with type t = Bytes.t and type buf = Bytes.t Ctypes.ocaml = struct
  type t = Bytes.t
  type buf = Bytes.t Ctypes.ocaml
  let empty = Bytes.empty
  let size_uint32 b = Unsigned.UInt32.of_int (Bytes.length b)
  let ctypes_buf = Ctypes.ocaml_bytes_start
  let size = Bytes.length
  let equal = Bytes.equal
  let disjoint b1 b2 = b1 != b2
  let sub = Bytes.sub
  let z_compare b z = Z.compare (Z.of_bits (Bytes.to_string b)) z
end
(** Representation of [Bytes.t] buffers *)

(* VD: temporarily disable, eliminate dependency on bigstring *)
(* module CBigstring : Buffer with type t = Bigstring.t and type buf = uint8 Ctypes_static.ptr = struct
 *   open Ctypes
 *   type t = Bigstring.t
 *   type buf = uint8 Ctypes_static.ptr
 *   let empty = Bigstring.empty
 *   let size_uint32 b = Unsigned.UInt32.of_int (Bigstring.size b)
 *   let ctypes_buf b = from_voidp uint8_t (to_voidp (bigarray_start array1 b))
 *   let size = Bigstring.size
 *   let equal = Bigstring.equal
 *   let disjoint _ _ = true (\* TODO: use https://github.com/ocaml/ocaml/pull/8618 once merged *\)
 * end *)


module Hacl_Hash = Hacl_Hash_bindings.Bindings(Hacl_Hash_stubs)
module Hacl_Spec = Hacl_Spec_bindings.Bindings(Hacl_Spec_stubs)

let pow2 n = Z.(pow ~$2) n

module AEADDefs = struct
  open Hacl_Spec
  type alg =
    | AES128_GCM
    | AES256_GCM
    | CHACHA20_POLY1305
  let alg_definition = function
    | AES128_GCM -> spec_Agile_AEAD_alg_Spec_Agile_AEAD_AES128_GCM
    | AES256_GCM -> spec_Agile_AEAD_alg_Spec_Agile_AEAD_AES256_GCM
    | CHACHA20_POLY1305 -> spec_Agile_AEAD_alg_Spec_Agile_AEAD_CHACHA20_POLY1305
  let key_length = function
    (* specs/Spec.Agile.AEAD.key_length *)
    | AES128_GCM -> 16
    | AES256_GCM -> 32
    | CHACHA20_POLY1305 -> 32
  let tag_length = function
    (* specs/Spec.Agile.AEAD.tag_length *)
    | AES128_GCM
    | AES256_GCM
    | CHACHA20_POLY1305 -> 16
  let check_iv_length len = function
    (* specs/Spec.Agile.AEAD.iv_length *)
    | AES128_GCM
    | AES256_GCM -> len > 0 && Z.((of_int 8) * (of_int len) < pow2 64)
    | CHACHA20_POLY1305 -> len = 12
  let check_max_pt_length len = function
    (* specs/Spec.Agile.AEAD.max_length *)
    | AES128_GCM
    | AES256_GCM -> Z.(of_int len < pow2 32)
    | CHACHA20_POLY1305 -> Z.(of_int len < pow2 32 - of_int 16)
  let check_sizes ~alg ~iv_len ~tag_len ~ad_len ~pt_len ~ct_len =
    (* providers/EverCrypt.AEAD.encrypt_st *)
    assert (check_iv_length iv_len alg);
    assert (tag_len = tag_length alg);
    assert (check_max_pt_length pt_len alg);
    assert Z.(of_int ad_len <= pow2 31);
    assert (pt_len = ct_len)
end

module HashDefs = struct
  open Hacl_Spec
  type deprecated_alg =
    | SHA1
    | MD5 [@@deprecated]
  type alg =
    | SHA2_224
    | SHA2_256
    | SHA2_384
    | SHA2_512
    | BLAKE2b
    | BLAKE2s
    | Legacy of deprecated_alg
  let alg_definition = function
    | SHA2_224 -> spec_Hash_Definitions_hash_alg_Spec_Hash_Definitions_SHA2_224
    | SHA2_256 -> spec_Hash_Definitions_hash_alg_Spec_Hash_Definitions_SHA2_256
    | SHA2_384 -> spec_Hash_Definitions_hash_alg_Spec_Hash_Definitions_SHA2_384
    | SHA2_512 -> spec_Hash_Definitions_hash_alg_Spec_Hash_Definitions_SHA2_512
    | BLAKE2b -> spec_Hash_Definitions_hash_alg_Spec_Hash_Definitions_Blake2B
    | BLAKE2s -> spec_Hash_Definitions_hash_alg_Spec_Hash_Definitions_Blake2S
    | Legacy SHA1 -> spec_Hash_Definitions_hash_alg_Spec_Hash_Definitions_SHA1
    | Legacy MD5 -> spec_Hash_Definitions_hash_alg_Spec_Hash_Definitions_MD5
  let digest_len alg =
    UInt32.to_int (Hacl_Hash.hacl_Hash_Definitions_hash_len (alg_definition alg))
  let check_digest_len alg len =
    assert (len = digest_len alg)
  let max_input_len = function
    (* specs/Spec.Hash.Definitions.max_input_length *)
    | Legacy SHA1
    | Legacy MD5
    | SHA2_224
    | SHA2_256 -> pow2 61
    | SHA2_384
    | SHA2_512 -> pow2 125
    | BLAKE2b -> pow2 128
    | BLAKE2s -> pow2 64
  let check_max_input_len alg len =
    assert Z.(of_int len < max_input_len alg)
  let block_len alg =
    UInt32.to_int (Hacl_Hash.hacl_Hash_Definitions_block_len (alg_definition alg))
  let check_key_len alg len =
    assert Z.(of_int len + of_int (block_len alg) < max_input_len alg)
end

module type Chacha20_Poly1305_generic = sig
  type bytes

  val encrypt: key:bytes -> iv:bytes -> ad:bytes -> pt:bytes -> ct:bytes -> tag:bytes -> unit
  (** [encrypt key iv ad pt ct tag] takes a [key], an initial value [iv], additional data
      [ad], and plaintext [pt], as well as output buffers [ct], which, if successful, will
      contain the encrypted [pt], and [tag], which will contain the authentication tag for
      the plaintext and the associated data. *)

  val decrypt: key:bytes -> iv:bytes -> ad:bytes -> ct:bytes -> tag:bytes -> pt:bytes -> bool
  (** [decrypt key iv ad ct tag pt] takes a [key], the initial value [iv], additional
      data [ad], ciphertext [ct], and authentication tag [tag], as well as output buffer [pt],
      which, if successful, will contain the decrypted [ct]. *)

end

module type Curve25519_generic = sig
(** See {{:https://hacl-star.github.io/HaclECDH.html#hacl-curve25519} here} for detailed
    usage instructions.
*)

  type bytes
  val secret_to_public : sk:bytes -> pk:bytes -> unit
  (** [secret_to_public sk pk] takes a 32-byte secret key [sk] and writes the corresponding
      32-byte ECDH public key in [pk]. Buffers [pk] and [sk] must be distinct. *)

  val ecdh : sk:bytes -> pk:bytes -> shared:bytes -> bool
  (** [ecdh sk pk shared] takes a 32-byte secret key [sk] and another party's 32-byte public
      key and writes the 32-byte ECDH shared key in [shared]. Buffer [shared] must be distinct from
      [pk] and [sk]. *)

  val scalarmult : scalar:bytes -> input:bytes -> result:bytes -> unit
  (** [scalarmult scalar input result] performs X25519 scalar multiplication. All buffers
      are 32-byte long and must be distinct. *)

end

module type EdDSA_generic = sig
(** See {{:https://hacl-star.github.io/HaclSig.html} here} for detailed
    usage instructions.

    Buffers have the following size constraints:
    - [sk], [pk]: 32 bytes
    - [signature]: 64 bytes
*)

  type bytes

  (** {1 EdDSA} *)

  val secret_to_public : sk:bytes -> pk:bytes -> unit
  (** [secret_to_public sk pk] takes a secret key [sk] and writes the corresponding
      public key in [pk]. Buffers [pk] and [sk] must be distinct. *)

  val sign : sk:bytes -> pt:bytes -> signature:bytes -> unit
  (** [sign sk pt signature] takes secret key [sk] and message [pt] and writes
      the Ed25519 signature in [signature]. *)

  val verify : pk:bytes -> pt:bytes -> signature:bytes -> bool
  (** [verify pk pt signature] takes public key [pk], message [pt] and verifies the
      Ed25519 signature, returning true if valid. *)

  (** {1 EdDSA Expanded Signing}

      The buffer [ks] containing the expanded secret key must be 96 bytes long.
*)

  val expand_keys : sk:bytes -> ks:bytes -> unit
  (** [expand_keys sk ks] takes secret key [sk] and writes the expanded secret key in [ks]. *)

  val sign_expanded : ks:bytes -> pt:bytes -> signature:bytes -> unit
  (** [sign_expanded ks pt signature] takes expanded secret key [ks] and message [pt] and writes
      the Ed25519 signature in [signature]. *)

end

module type HashFunction_generic = sig

  type bytes
  val hash : pt:bytes -> digest:bytes -> unit
  (** [hash pt digest] hashes [pt] and outputs the result in [digest]. *)
end

module type MAC_generic = sig
  (** For Poly1305, buffers have the following size constraints:
      - [key]: 32 bytes
      - [tag]: 16 bytes

      For HMAC with SHA2, [tag] needs to be the same size as the digest size of
      the corresponding hash function (see {{!EverCrypt.Hash} here}).

      For HMAC with BLAKE2, [tag] needs to be exactly 64 bytes for BLAKE2b
      and 32 bytes for BLAKE2s.
*)

  type bytes
  val mac : key:bytes -> msg:bytes -> tag:bytes -> unit
  (** [mac key msg tag] computes the MAC of [msg] using key [key] and writes the result in [tag] *)
end

module type HKDF_generic = sig
  (** Buffers have the following size constraints with respect to the digest size of the underlying
      hash function, [digest_len]:
      - [prk]: = [digest_len]
      - [okm]: <= 255 * [digest_len]
*)

  type bytes

  val extract: salt:bytes -> ikm:bytes -> prk:bytes -> unit
  (** [extract salt ikm prk] computes a pseudorandom key [prk] using input key material [ikm] and
      salt [salt]. *)

  val expand: prk:bytes -> info:bytes -> okm:bytes -> unit
  (** [expand prk info okm] expands the pseudorandom key [prk], taking the info string [info] into
      account, and writes the output key material in [okm]. *)
end

module type ECDSA_generic = sig
  (** Buffers have the following size constraints:
      - [pk]: 64 bytes, corresponding to the "raw" representation of an elliptic curve point (see {!section:points})
      - [sk], [k]: 32 bytes
      - [signature]: 64 bytes
      - [pt]: no size requirement for variants using SHA-2 hashing (see {!section:ecdsa})
  *)

  type bytes

  val sign : sk:bytes -> pt:bytes -> k:bytes -> signature:bytes -> bool
  (** [sign sk pt k signature] attempts to sign the message [pt] with secret key [sk] and
      signing secret [k]. If successful, the signature is written in [signature] and the
      function returns true. *)

  val verify : pk:bytes -> pt:bytes -> signature:bytes -> bool
  (** [verify pk pt signature] checks the [signature] of [pt] using public key [pk] and returns
  true if it is valid. *)

end

module type Blake2_generic = sig
(** Buffers have the following size constraints:
    - [key]: <= 64 bytes for BLAKE2b, <= 32 bytes for BLAKE2s
    - [digest]: non-zero, <= 64 bytes for BLAKE2b, <= 32 bytes for BLAKE2s *)
  (* TODO: review checks and write documentation for large  maximum buffer sizes *)

  type bytes
  val hash : ?key:bytes -> pt:bytes -> digest:bytes -> unit
  (** [hash ?key ~pt ~digest] hashes [pt] and outputs the result in [digest].
      An optional [key] argument can passed for keyed hashing. *)
end

module type Chacha20_Poly1305 = Chacha20_Poly1305_generic with type bytes = CBytes.t
module type Curve25519 = Curve25519_generic with type bytes = CBytes.t
module type EdDSA = EdDSA_generic with type bytes = CBytes.t
module type HashFunction = HashFunction_generic with type bytes = CBytes.t
module type MAC = MAC_generic with type bytes = CBytes.t
module type HKDF = HKDF_generic with type bytes = CBytes.t
module type ECDSA = ECDSA_generic with type bytes = CBytes.t
module type Blake2 = Blake2_generic with type bytes = CBytes.t
