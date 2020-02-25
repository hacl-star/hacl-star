open Unsigned

open SharedDefs

module RandomBuffer : sig
  val randombytes : Bigstring.t -> bool
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

(* TODO: SHAKE *)
module SHA3_224 : HashFunction
module SHA3_256 : HashFunction
module SHA3_384 : HashFunction
module SHA3_512 : HashFunction

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
  val box_beforenm : Bigstring.t -> Bigstring.t -> Bigstring.t -> bool
  module Easy : sig
    val box : Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> bool
    val box_open : Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> bool
    val box_afternm : Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> bool
    val box_open_afternm : Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> bool
    val secretbox : Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> bool
    val secretbox_open : Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> bool
  end
  module Detached : sig
    val box : Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> bool
    val box_open : Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> bool
    val box_afternm : Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> bool
    val box_open_afternm : Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> bool
    val secretbox : Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> bool
    val secretbox_open : Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> bool
  end
end

module Blake2b_32 : Blake2b
module Blake2b_256 : Blake2b

module Blake2b_256_bigstring : Blake2b_bigstring
module Blake2b_256_bytes : Blake2b_bytes
