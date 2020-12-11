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

(* VD: temporarely disable, eliminate dependency on bigstring *)
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

let max_size_t = Z.of_string "4294967296"

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
    | Legacy of deprecated_alg
  let alg_definition = function
    | SHA2_224 -> spec_Hash_Definitions_hash_alg_Spec_Hash_Definitions_SHA2_224
    | SHA2_256 -> spec_Hash_Definitions_hash_alg_Spec_Hash_Definitions_SHA2_256
    | SHA2_384 -> spec_Hash_Definitions_hash_alg_Spec_Hash_Definitions_SHA2_384
    | SHA2_512 -> spec_Hash_Definitions_hash_alg_Spec_Hash_Definitions_SHA2_512
    | Legacy SHA1 -> spec_Hash_Definitions_hash_alg_Spec_Hash_Definitions_SHA1
    | Legacy MD5 -> spec_Hash_Definitions_hash_alg_Spec_Hash_Definitions_MD5
  let digest_len alg =
    UInt32.to_int (Hacl_Hash.hacl_Hash_Definitions_hash_len (alg_definition alg))
  let check_digest_len alg len =
    match alg with
    | Some alg -> assert (len = digest_len alg)
    | None -> ()
  let max_input_len = max_size_t
  let check_max_input_len len =
    assert Z.(of_int len < max_input_len)
  let incremental_input_len = function
    | Legacy SHA1
    | Legacy MD5
    | SHA2_224
    | SHA2_256 -> Z.pow (Z.of_int 2) 61
    | SHA2_384
    | SHA2_512 -> Z.pow (Z.of_int 2) 125
  let block_len alg =
    UInt32.to_int (Hacl_Hash.hacl_Hash_Definitions_block_len (alg_definition alg))
  let check_key_len alg len =
    assert Z.(of_int len + of_int (block_len alg) < max_input_len)
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
      which, if sucessful, will contain the decrypted [ct]. *)

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
    - [pt]: <= {!max_size_t} - 64 bytes
*)

  type bytes

  (** {3 EdDSA} *)

  val secret_to_public : sk:bytes -> pk:bytes -> unit
  (** [secret_to_public sk pk] takes a secret key [sk] and writes the corresponding
      public key in [pk]. Buffers [pk] and [sk] must be distinct. *)

  val sign : sk:bytes -> pt:bytes -> signature:bytes -> unit
  (** [sign sk pt signature] takes secret key [sk] and message [pt] and writes
      the Ed25519 signature in [signature]. *)

  val verify : pk:bytes -> pt:bytes -> signature:bytes -> bool
  (** [verify pk pt signature] takes public key [pk], message [pt] and verifies the
      Ed25519 signature, returning true if valid. *)

  (** {3 EdDSA Expanded Signing}

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
  val hash : bytes -> bytes -> unit
end

module type MAC_generic = sig
  type bytes
  val mac : bytes -> bytes -> bytes -> unit
end

module type HKDF_generic = sig
  type bytes
  val expand: bytes -> bytes -> bytes -> unit
  val extract: bytes -> bytes -> bytes -> unit
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
  type bytes
  val hash : ?key:bytes -> pt:bytes -> digest:bytes -> unit
  (* TODO: clarify size constraints for pt, I think I might have gotten this wrong *)
  (** [hash ?key ~pt ~digest] takes an optional [key] and writes the digest of [pt] in [digest].
      Buffers have the following size constraints:
      - [key]: <= 64 bytes for BLAKE2b, <= 32 bytes for BLAKE2s
      - [pt]: <= {!max_size_t} if key is empty, otherwise <= [max_size_t] + 128 for BLAKE2b, <= [max_size_t] + 64 for BLAKE2s
      - [digest]: non-zero, <= 64 bytes for BLAKE2b, <= 32 bytes for BLAKE2s
  *)
end

module type Chacha20_Poly1305 = Chacha20_Poly1305_generic with type bytes = CBytes.t
module type Curve25519 = Curve25519_generic with type bytes = CBytes.t
module type EdDSA = EdDSA_generic with type bytes = CBytes.t
module type HashFunction = HashFunction_generic with type bytes = CBytes.t
module type MAC = MAC_generic with type bytes = CBytes.t
module type HKDF = HKDF_generic with type bytes = CBytes.t
module type ECDSA = ECDSA_generic with type bytes = CBytes.t
module type Blake2 = Blake2_generic with type bytes = CBytes.t
