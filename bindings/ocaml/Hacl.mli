open Unsigned

open SharedDefs

module RandomBuffer : sig
  val randombytes : Bytes.t -> bool
end

module Chacha20_Poly1305_32 : Chacha20_Poly1305
module Chacha20_Poly1305_128 : Chacha20_Poly1305
module Chacha20_Poly1305_256 : Chacha20_Poly1305

module Curve25519_51 : Curve25519
module Curve25519_64 : Curve25519
module Curve25519_64_Slow : Curve25519

module Curve25519_51_Internal : sig
  include Curve25519
  val fadd : Bigstring.t -> Bigstring.t -> Bigstring.t -> unit
  val fsub : Bigstring.t -> Bigstring.t -> Bigstring.t -> unit
  val fmul1 : Bigstring.t -> Bigstring.t -> uint64 -> unit
end

module Ed25519 : EdDSA

module SHA2_224 : HashFunction
module SHA2_256 : HashFunction
module SHA2_384 : HashFunction
module SHA2_512 : HashFunction

module SHA3_224 : HashFunction
module SHA3_256 : HashFunction
module SHA3_384 : HashFunction
module SHA3_512 : HashFunction
module Keccak : sig
  val keccak : int -> int -> int -> Bytes.t -> Bytes.t -> unit
  val shake128 : Bytes.t -> Bytes.t -> unit
  val shake256 : Bytes.t -> Bytes.t -> unit
end

module MD5 : HashFunction [@@deprecated]
module SHA1 : HashFunction [@@deprecated]

module HMAC_SHA2_256 : MAC
module HMAC_SHA2_384 : MAC
module HMAC_SHA2_512 : MAC

module Poly1305_32 : MAC
module Poly1305_128 : MAC
module Poly1305_256 : MAC

module HKDF_SHA2_256 : HKDF
module HKDF_SHA2_512 : HKDF

module NaCl : sig
  val box_beforenm : Bytes.t -> Bytes.t -> Bytes.t -> bool
  module Easy : sig
    val box : Bytes.t -> Bytes.t -> Bytes.t -> Bytes.t -> Bytes.t -> bool
    val box_open : Bytes.t -> Bytes.t -> Bytes.t -> Bytes.t -> Bytes.t -> bool
    val box_afternm : Bytes.t -> Bytes.t -> Bytes.t -> Bytes.t -> bool
    val box_open_afternm : Bytes.t -> Bytes.t -> Bytes.t -> Bytes.t -> bool
    val secretbox : Bytes.t -> Bytes.t -> Bytes.t -> Bytes.t -> bool
    val secretbox_open : Bytes.t -> Bytes.t -> Bytes.t -> Bytes.t -> bool
  end
  module Detached : sig
    val box : Bytes.t -> Bytes.t -> Bytes.t -> Bytes.t -> Bytes.t -> Bytes.t -> bool
    val box_open : Bytes.t -> Bytes.t -> Bytes.t -> Bytes.t -> Bytes.t -> Bytes.t -> bool
    val box_afternm : Bytes.t -> Bytes.t -> Bytes.t -> Bytes.t -> Bytes.t -> bool
    val box_open_afternm : Bytes.t -> Bytes.t -> Bytes.t -> Bytes.t -> Bytes.t -> bool
    val secretbox : Bytes.t -> Bytes.t -> Bytes.t -> Bytes.t -> Bytes.t -> bool
    val secretbox_open : Bytes.t -> Bytes.t -> Bytes.t -> Bytes.t -> Bytes.t -> bool
  end
end

module Blake2b_32 : Blake2b
module Blake2b_256 : Blake2b

(* module ECDSA : sig
 *   val sign : Bytes.t -> Bytes.t -> Bytes.t -> Bytes.t -> bool
 *   val verify : Bytes.t -> Bytes.t -> Bytes.t -> bool
 * end *)

module ECDSA_test : sig
  val compress_c : Bytes.t -> Bytes.t -> unit
  val compress_n : Bytes.t -> Bytes.t -> unit
  val decompress_c : Bytes.t -> Bytes.t -> bool
  val decompress_n : Bytes.t -> Bytes.t -> bool
  val verify : Bytes.t -> Bytes.t -> Bytes.t -> bool
  val sign_with_k : Bytes.t -> Bytes.t -> Bytes.t -> Bytes.t -> bool
  val dh_initiator : Bytes.t -> Bytes.t -> bool
  val reduction : Bytes.t -> Bytes.t -> unit
  val valid_pk : Bytes.t -> bool
end

