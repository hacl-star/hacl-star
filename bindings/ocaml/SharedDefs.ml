open Unsigned


module type Buffer = sig
  type t
  type buf
  val size_uint32 : t -> uint32
  val ctypes_buf : t -> buf
  val size : t -> int
  val equal : t -> t -> bool
  val disjoint : t -> t -> bool
  val sub : t -> int -> int -> t
  val z_compare : t -> Z.t -> int
end

module CBytes : Buffer with type t = Bytes.t and type buf = Bytes.t Ctypes.ocaml = struct
  type t = Bytes.t
  type buf = Bytes.t Ctypes.ocaml
  let size_uint32 b = Unsigned.UInt32.of_int (Bytes.length b)
  let ctypes_buf = Ctypes.ocaml_bytes_start
  let size = Bytes.length
  let equal = Bytes.equal
  let disjoint b1 b2 = b1 != b2
  let sub = Bytes.sub
  let z_compare b z = Z.compare (Z.of_bits (Bytes.to_string b)) z
end

(* VD: temporarely disable, eliminate dependency on bigstring *)
(* module CBigstring : Buffer with type t = Bigstring.t and type buf = uint8 Ctypes_static.ptr = struct
 *   open Ctypes
 *   type t = Bigstring.t
 *   type buf = uint8 Ctypes_static.ptr
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
  type t
  val encrypt: t -> t -> t -> t -> t -> t -> unit
  val decrypt: t -> t -> t -> t -> t -> t -> bool
end

module type Curve25519_generic = sig
  type t
  val secret_to_public : t -> t -> unit
  val scalarmult : t -> t -> t -> unit
  val ecdh : t -> t -> t -> bool
end

module type EdDSA_generic = sig
  type t
  val secret_to_public : t -> t -> unit
  val sign : t -> t -> t -> unit
  val verify : t -> t -> t -> bool
  val expand_keys : t -> t -> unit
  val sign_expanded : t -> t -> t -> unit
end

module type HashFunction_generic = sig
  type t
  val hash : t -> t -> unit
end

module type MAC_generic = sig
  type t
  val mac : t -> t -> t -> unit
end

module type HKDF_generic = sig
  type t
  val expand: t -> t -> t -> unit
  val extract: t -> t -> t -> unit
end

module type ECDSA_generic = sig
  type t
  val sign : t -> t -> t -> t -> bool
  val verify : t -> t -> t -> bool
end

module type Blake2_generic = sig
  type t
  val hash : t -> t -> t -> unit
end

module type Chacha20_Poly1305 = Chacha20_Poly1305_generic with type t = CBytes.t
module type Curve25519 = Curve25519_generic with type t = CBytes.t
module type EdDSA = EdDSA_generic with type t = CBytes.t
module type HashFunction = HashFunction_generic with type t = CBytes.t
module type MAC = MAC_generic with type t = CBytes.t
module type HKDF = HKDF_generic with type t = CBytes.t
module type ECDSA = ECDSA_generic with type t = CBytes.t
module type Blake2 = Blake2_generic with type t = CBytes.t
