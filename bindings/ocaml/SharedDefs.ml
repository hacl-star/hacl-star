open Unsigned

module Hacl_Hash = Hacl_Hash_bindings.Bindings(Hacl_Hash_stubs)
module Hacl_Spec = Hacl_Spec_bindings.Bindings(Hacl_Spec_stubs)

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
end

module type Chacha20_Poly1305 = sig
  val encrypt: Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> unit
  val decrypt: Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> bool
end

module type Curve25519 = sig
  val secret_to_public : Bigstring.t -> Bigstring.t -> unit
  val scalarmult : Bigstring.t -> Bigstring.t -> Bigstring.t -> unit
  val ecdh : Bigstring.t -> Bigstring.t -> Bigstring.t -> bool
end

module type EdDSA = sig
  val secret_to_public : Bigstring.t -> Bigstring.t -> unit
  val sign : Bigstring.t -> Bigstring.t -> Bigstring.t -> unit
  val verify : Bigstring.t -> Bigstring.t -> Bigstring.t -> bool
  val expand_keys : Bigstring.t -> Bigstring.t -> unit
  val sign_expanded : Bigstring.t -> Bigstring.t -> Bigstring.t -> unit
end

module type HashFunction = sig
  val hash : Bigstring.t -> Bigstring.t -> unit
end

module type MAC = sig
  val mac : Bigstring.t -> Bigstring.t -> Bigstring.t -> unit
end

module type HKDF = sig
  val expand: Bigstring.t -> Bigstring.t -> Bigstring.t -> unit
  val extract: Bigstring.t -> Bigstring.t -> Bigstring.t -> unit
end

module type Blake2b = sig
  val hash : Bigstring.t -> Bigstring.t -> Bigstring.t -> unit
end


(* Experimenting with generically defining both Bytes and Bigstring APIs
 * !!! The C functions take uint8_t* but Ctyes.ocaml_bytes_start creates a reference to a Bytes.t on the
 * OCaml heap as a char*, so as far as I understand this will only work when the char type is unsigned char. *)
open Ctypes

module type Buffer = sig
  type t
  type buf
  val size_uint32 : t -> uint32
  val ctypes_buf : t -> buf
end

module CBigstring : Buffer with type t = Bigstring.t and type buf = uint8 Ctypes_static.ptr = struct
  type t = Bigstring.t
  type buf = uint8 Ctypes_static.ptr
  let size_uint32 b = Unsigned.UInt32.of_int (Bigstring.size b)
  let ctypes_buf b = from_voidp uint8_t (to_voidp (bigarray_start array1 b))
end

module CBytes : Buffer with type t = Bytes.t and type buf = Bytes.t Ctypes.ocaml = struct
  type t = Bytes.t
  type buf = Bytes.t Ctypes.ocaml
  let size_uint32 b = Unsigned.UInt32.of_int (Bytes.length b)
  let ctypes_buf = Ctypes.ocaml_bytes_start
end

module type Blake2b_generic = sig
  type t
  val hash : t -> t -> t -> unit
end

module type Blake2b_bigstring = Blake2b_generic with type t = CBigstring.t
module type Blake2b_bytes = Blake2b_generic with type t = CBytes.t
