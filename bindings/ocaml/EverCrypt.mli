open SharedDefs

module C = CBytes

module Error : sig
  type error_code =
    | UnsupportedAlgorithm
    | InvalidKey
    | AuthenticationFailure
    | InvalidIVLength
    | DecodeError
  type 'a result =
    | Success of 'a
    | Error of error_code
end

module AEAD : sig
  type t
  type alg =
    | AES128_GCM
    | AES256_GCM
    | CHACHA20_POLY1305
  val init : alg -> C.t -> t Error.result
  val encrypt : t -> C.t -> C.t -> C.t -> C.t -> C.t -> unit Error.result
  val decrypt : t -> C.t -> C.t -> C.t -> C.t -> C.t -> unit Error.result
end

module Chacha20_Poly1305 : Chacha20_Poly1305

module Curve25519 : Curve25519

module Ed25519 : EdDSA

module Hash : sig
  type t
  val init : HashDefs.alg -> t
  val update : t -> C.t -> unit
  val finish : t -> C.t -> unit
  val hash : HashDefs.alg -> C.t -> C.t -> unit
end

module SHA2_224 : HashFunction

module SHA2_256 : HashFunction

module HMAC : sig
  val is_supported_alg : HashDefs.alg -> bool
  val mac : HashDefs.alg -> C.t -> C.t -> C.t -> unit
end

module HMAC_SHA2_256 : MAC

module HMAC_SHA2_384 : MAC

module HMAC_SHA2_512 : MAC

module Poly1305 : MAC

module HKDF : sig
  val expand : HashDefs.alg -> C.t -> C.t -> C.t -> unit
  val extract : HashDefs.alg -> C.t -> C.t -> C.t -> unit
end

module HKDF_SHA2_256 : HKDF

module HKDF_SHA2_384 : HKDF

module HKDF_SHA2_512 : HKDF

module DRBG : sig
  type t
  val instantiate : ?personalization_string: C.t -> HashDefs.alg -> t option
  val reseed : ?additional_input: C.t -> t -> bool
  val generate : ?additional_input: C.t -> t -> C.t -> bool
  val uninstantiate : t -> unit
end
