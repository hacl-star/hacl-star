# Non-constant-time functions in this folder

## These functions are not side-channel resistant

Hacl.Impl.P256.Signature.Common.eq_u64_nCT
Hacl.Impl.P256.Signature.Common.eq_0_u64
Hacl.Impl.P256.Signature.Common.isCoordinateValid
Hacl.Impl.P256.Signature.Common.verifyQValidCurvePoint
Hacl.Impl.P256.Signature.Common.isPointAtInfinityPublic
Hacl.Impl.P256.Signature.Common.isPointOnCurvePublic
Hacl.Impl.P256.Signature.Common.isOrderCorrect

Hacl.Impl.ECDSA.P256.Verification.isZero_uint64_nCT
Hacl.Impl.ECDSA.P256.Verification.isMoreThanZeroLessThanOrderMinusOne
Hacl.Impl.ECDSA.P256.Verification.compare_felem_bool
Hacl.Impl.ECDSA.P256.Verification.ecdsa_verification_step1
Hacl.Impl.ECDSA.P256.Verification.ecdsa_verification_step5
Hacl.Impl.ECDSA.P256.Verification.ecdsa_verification

Hacl.Impl.ECDSA.ecdsa_p256_sha2_verify
Hacl.Impl.ECDSA.ecdsa_p256_sha2_verify_u8

Hacl.P256.ecdsa_verif_p256_sha2
Hacl.P256.ecdsa_verif_p256_sha384
Hacl.P256.ecdsa_verif_p256_sha512
Hacl.P256.ecdsa_verif_without_hash
Hacl.P256.verifyQ
Hacl.P256.ecp256dh_r

## These functions are constant-time on `scalar` but not on `pubKey`

Hacl.Impl.P256.DH._ecp256dh_r result pubKey scalar
Hacl.Impl.P256.DH.ecp256dh_r result pubKey scalar

