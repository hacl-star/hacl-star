open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let everCrypt_AutoConfig2_has_shaext =
      foreign "EverCrypt_AutoConfig2_has_shaext" (void @-> (returning bool))
    let everCrypt_AutoConfig2_has_aesni =
      foreign "EverCrypt_AutoConfig2_has_aesni" (void @-> (returning bool))
    let everCrypt_AutoConfig2_has_pclmulqdq =
      foreign "EverCrypt_AutoConfig2_has_pclmulqdq"
        (void @-> (returning bool))
    let everCrypt_AutoConfig2_has_avx2 =
      foreign "EverCrypt_AutoConfig2_has_avx2" (void @-> (returning bool))
    let everCrypt_AutoConfig2_has_avx =
      foreign "EverCrypt_AutoConfig2_has_avx" (void @-> (returning bool))
    let everCrypt_AutoConfig2_has_bmi2 =
      foreign "EverCrypt_AutoConfig2_has_bmi2" (void @-> (returning bool))
    let everCrypt_AutoConfig2_has_adx =
      foreign "EverCrypt_AutoConfig2_has_adx" (void @-> (returning bool))
    let everCrypt_AutoConfig2_has_sse =
      foreign "EverCrypt_AutoConfig2_has_sse" (void @-> (returning bool))
    let everCrypt_AutoConfig2_has_movbe =
      foreign "EverCrypt_AutoConfig2_has_movbe" (void @-> (returning bool))
    let everCrypt_AutoConfig2_has_rdrand =
      foreign "EverCrypt_AutoConfig2_has_rdrand" (void @-> (returning bool))
    let everCrypt_AutoConfig2_has_avx512 =
      foreign "EverCrypt_AutoConfig2_has_avx512" (void @-> (returning bool))
    let everCrypt_AutoConfig2_wants_vale =
      foreign "EverCrypt_AutoConfig2_wants_vale" (void @-> (returning bool))
    let everCrypt_AutoConfig2_wants_hacl =
      foreign "EverCrypt_AutoConfig2_wants_hacl" (void @-> (returning bool))
    let everCrypt_AutoConfig2_wants_openssl =
      foreign "EverCrypt_AutoConfig2_wants_openssl"
        (void @-> (returning bool))
    let everCrypt_AutoConfig2_wants_bcrypt =
      foreign "EverCrypt_AutoConfig2_wants_bcrypt"
        (void @-> (returning bool))
    let everCrypt_AutoConfig2_recall =
      foreign "EverCrypt_AutoConfig2_recall" (void @-> (returning void))
    let everCrypt_AutoConfig2_init =
      foreign "EverCrypt_AutoConfig2_init" (void @-> (returning void))
    let everCrypt_AutoConfig2_disable_avx2 =
      foreign "EverCrypt_AutoConfig2_disable_avx2"
        (void @-> (returning void))
    let everCrypt_AutoConfig2_disable_avx =
      foreign "EverCrypt_AutoConfig2_disable_avx" (void @-> (returning void))
    let everCrypt_AutoConfig2_disable_bmi2 =
      foreign "EverCrypt_AutoConfig2_disable_bmi2"
        (void @-> (returning void))
    let everCrypt_AutoConfig2_disable_adx =
      foreign "EverCrypt_AutoConfig2_disable_adx" (void @-> (returning void))
    let everCrypt_AutoConfig2_disable_shaext =
      foreign "EverCrypt_AutoConfig2_disable_shaext"
        (void @-> (returning void))
    let everCrypt_AutoConfig2_disable_aesni =
      foreign "EverCrypt_AutoConfig2_disable_aesni"
        (void @-> (returning void))
    let everCrypt_AutoConfig2_disable_pclmulqdq =
      foreign "EverCrypt_AutoConfig2_disable_pclmulqdq"
        (void @-> (returning void))
    let everCrypt_AutoConfig2_disable_sse =
      foreign "EverCrypt_AutoConfig2_disable_sse" (void @-> (returning void))
    let everCrypt_AutoConfig2_disable_movbe =
      foreign "EverCrypt_AutoConfig2_disable_movbe"
        (void @-> (returning void))
    let everCrypt_AutoConfig2_disable_rdrand =
      foreign "EverCrypt_AutoConfig2_disable_rdrand"
        (void @-> (returning void))
    let everCrypt_AutoConfig2_disable_avx512 =
      foreign "EverCrypt_AutoConfig2_disable_avx512"
        (void @-> (returning void))
    let everCrypt_AutoConfig2_disable_vale =
      foreign "EverCrypt_AutoConfig2_disable_vale"
        (void @-> (returning void))
    let everCrypt_AutoConfig2_disable_hacl =
      foreign "EverCrypt_AutoConfig2_disable_hacl"
        (void @-> (returning void))
    let everCrypt_AutoConfig2_disable_openssl =
      foreign "EverCrypt_AutoConfig2_disable_openssl"
        (void @-> (returning void))
    let everCrypt_AutoConfig2_disable_bcrypt =
      foreign "EverCrypt_AutoConfig2_disable_bcrypt"
        (void @-> (returning void))
    let everCrypt_AutoConfig2_has_vec128 =
      foreign "EverCrypt_AutoConfig2_has_vec128" (void @-> (returning bool))
    let everCrypt_AutoConfig2_has_vec256 =
      foreign "EverCrypt_AutoConfig2_has_vec256" (void @-> (returning bool))
  end