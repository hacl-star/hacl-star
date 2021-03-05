module EverCrypt_AutoConfig2 = EverCrypt_AutoConfig2_bindings.Bindings(EverCrypt_AutoConfig2_stubs)

open EverCrypt_AutoConfig2
type feature =
  | SHAEXT
  | AES_NI
  | PCLMULQDQ
  | VEC128
  | VEC256
  | BMI2
  | ADX
  | SSE
  | MOVBE
  | RDRAND
let init () = everCrypt_AutoConfig2_init ()
let has_feature = function
  | SHAEXT -> everCrypt_AutoConfig2_has_shaext ()
  | AES_NI -> everCrypt_AutoConfig2_has_aesni ()
  | PCLMULQDQ -> everCrypt_AutoConfig2_has_pclmulqdq ()
  | VEC128 -> everCrypt_AutoConfig2_has_vec128 ()
  | VEC256 -> everCrypt_AutoConfig2_has_vec256 ()
  | BMI2 -> everCrypt_AutoConfig2_has_bmi2 ()
  | ADX -> everCrypt_AutoConfig2_has_adx ()
  | SSE -> everCrypt_AutoConfig2_has_sse ()
  | MOVBE -> everCrypt_AutoConfig2_has_movbe ()
  | RDRAND -> everCrypt_AutoConfig2_has_rdrand ()

let () = init ()
