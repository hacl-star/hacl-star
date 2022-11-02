module Hacl.Curve25519_64_Slow

open Hacl.Impl.Curve25519.Generic
open Hacl.Impl.Curve25519.Fields

[@@ Comment "Compute the scalar multiple of a point.

@param out Pointer to 32 bytes of memory, allocated by the caller, where the resulting point is written to.
@param priv Pointer to 32 bytes of memory where the secret/private key is read from.
@param pub Pointer to 32 bytes of memory where the public point is read from."]
val scalarmult: scalarmult_st M64 True

[@@ Comment "Calculate a public point from a secret/private key.

This computes a scalar multiplication of the secret/private key with the curve's basepoint.

@param pub Pointer to 32 bytes of memory, allocated by the caller, where the resulting point is written to.
@param priv Pointer to 32 bytes of memory where the secret/private key is read from."]
val secret_to_public: secret_to_public_st M64 True

[@@ Comment "Execute the diffie-hellmann key exchange.

@param out Pointer to 32 bytes of memory, allocated by the caller, where the resulting point is written to.
@param priv Pointer to 32 bytes of memory where **our** secret/private key is read from.
@param pub Pointer to 32 bytes of memory where **their** public point is read from."]
val ecdh: ecdh_st M64 True
