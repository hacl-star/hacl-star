#include "config.h"

open SharedDefs

module C = CBytes

module RandomBuffer : sig
  val randombytes : C.t -> bool
end

module Chacha20_Poly1305_32 : Chacha20_Poly1305

module Curve25519_51 : Curve25519

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
  val keccak : int -> int -> int -> C.t -> C.t -> unit
  val shake128 : C.t -> C.t -> unit
  val shake256 : C.t -> C.t -> unit
end

module MD5 : HashFunction [@@deprecated]
module SHA1 : HashFunction [@@deprecated]

module HMAC_SHA2_256 : MAC
module HMAC_SHA2_384 : MAC
module HMAC_SHA2_512 : MAC

module Poly1305_32 : MAC

module HKDF_SHA2_256 : HKDF
module HKDF_SHA2_512 : HKDF

module NaCl : sig
  val box_beforenm : C.t -> C.t -> C.t -> bool
  module Easy : sig
    val box : C.t -> C.t -> C.t -> C.t -> C.t -> bool
    val box_open : C.t -> C.t -> C.t -> C.t -> C.t -> bool
    val box_afternm : C.t -> C.t -> C.t -> C.t -> bool
    val box_open_afternm : C.t -> C.t -> C.t -> C.t -> bool
    val secretbox : C.t -> C.t -> C.t -> C.t -> bool
    val secretbox_open : C.t -> C.t -> C.t -> C.t -> bool
  end
  module Detached : sig
    val box : C.t -> C.t -> C.t -> C.t -> C.t -> C.t -> bool
    val box_open : C.t -> C.t -> C.t -> C.t -> C.t -> C.t -> bool
    val box_afternm : C.t -> C.t -> C.t -> C.t -> C.t -> bool
    val box_open_afternm : C.t -> C.t -> C.t -> C.t -> C.t -> bool
    val secretbox : C.t -> C.t -> C.t -> C.t -> C.t -> bool
    val secretbox_open : C.t -> C.t -> C.t -> C.t -> C.t -> bool
  end
end

module Blake2b_32 : Blake2

module Blake2s_32 : Blake2

module ECDSA : sig
  val sign : C.t -> C.t -> C.t -> C.t -> bool
  val verify : C.t -> C.t -> C.t -> bool
end

#ifndef BROKEN_INTRINSICS
module Chacha20_Poly1305_128 : Chacha20_Poly1305
module Chacha20_Poly1305_256 : Chacha20_Poly1305

module Curve25519_64 : Curve25519

module Poly1305_128 : MAC
module Poly1305_256 : MAC

module Blake2b_256 : Blake2

module Blake2s_128 : Blake2
#endif
