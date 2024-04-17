open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    module Hacl_Hash_SHA3_Simd256_applied =
      (Hacl_Hash_SHA3_Simd256_bindings.Bindings)(Hacl_Hash_SHA3_Simd256_stubs)
    open Hacl_Hash_SHA3_Simd256_applied
    type hacl_Hash_SHA2_uint8_2p = k____uint8_t___uint8_t_
    let hacl_Hash_SHA2_uint8_2p =
      typedef k____uint8_t___uint8_t_ "Hacl_Hash_SHA2_uint8_2p"
    type hacl_Hash_SHA2_uint8_3p = k____uint8_t__K____uint8_t___uint8_t_
    let hacl_Hash_SHA2_uint8_3p =
      typedef k____uint8_t__K____uint8_t___uint8_t_ "Hacl_Hash_SHA2_uint8_3p"
    type hacl_Hash_SHA2_uint8_4p =
      k____uint8_t___uint8_t____K____uint8_t___uint8_t_
    let hacl_Hash_SHA2_uint8_4p =
      typedef k____uint8_t___uint8_t____K____uint8_t___uint8_t_
        "Hacl_Hash_SHA2_uint8_4p"
    type hacl_Hash_SHA2_uint8_5p = [ `hacl_Hash_SHA2_uint8_5p ] structure
    let (hacl_Hash_SHA2_uint8_5p :
      [ `hacl_Hash_SHA2_uint8_5p ] structure typ) =
      structure "Hacl_Hash_SHA2_uint8_5p_s"
    let hacl_Hash_SHA2_uint8_5p_fst =
      field hacl_Hash_SHA2_uint8_5p "fst" (ptr uint8_t)
    let hacl_Hash_SHA2_uint8_5p_snd =
      field hacl_Hash_SHA2_uint8_5p "snd"
        k____uint8_t___uint8_t____K____uint8_t___uint8_t_
    let _ = seal hacl_Hash_SHA2_uint8_5p
    type hacl_Hash_SHA2_uint8_6p = [ `hacl_Hash_SHA2_uint8_6p ] structure
    let (hacl_Hash_SHA2_uint8_6p :
      [ `hacl_Hash_SHA2_uint8_6p ] structure typ) =
      structure "Hacl_Hash_SHA2_uint8_6p_s"
    let hacl_Hash_SHA2_uint8_6p_fst =
      field hacl_Hash_SHA2_uint8_6p "fst" (ptr uint8_t)
    let hacl_Hash_SHA2_uint8_6p_snd =
      field hacl_Hash_SHA2_uint8_6p "snd" hacl_Hash_SHA2_uint8_5p
    let _ = seal hacl_Hash_SHA2_uint8_6p
    type hacl_Hash_SHA2_uint8_7p = [ `hacl_Hash_SHA2_uint8_7p ] structure
    let (hacl_Hash_SHA2_uint8_7p :
      [ `hacl_Hash_SHA2_uint8_7p ] structure typ) =
      structure "Hacl_Hash_SHA2_uint8_7p_s"
    let hacl_Hash_SHA2_uint8_7p_fst =
      field hacl_Hash_SHA2_uint8_7p "fst" (ptr uint8_t)
    let hacl_Hash_SHA2_uint8_7p_snd =
      field hacl_Hash_SHA2_uint8_7p "snd" hacl_Hash_SHA2_uint8_6p
    let _ = seal hacl_Hash_SHA2_uint8_7p
    type hacl_Hash_SHA2_uint8_8p = [ `hacl_Hash_SHA2_uint8_8p ] structure
    let (hacl_Hash_SHA2_uint8_8p :
      [ `hacl_Hash_SHA2_uint8_8p ] structure typ) =
      structure "Hacl_Hash_SHA2_uint8_8p_s"
    let hacl_Hash_SHA2_uint8_8p_fst =
      field hacl_Hash_SHA2_uint8_8p "fst" (ptr uint8_t)
    let hacl_Hash_SHA2_uint8_8p_snd =
      field hacl_Hash_SHA2_uint8_8p "snd" hacl_Hash_SHA2_uint8_7p
    let _ = seal hacl_Hash_SHA2_uint8_8p
    type hacl_Hash_SHA2_uint8_2x4p = [ `hacl_Hash_SHA2_uint8_2x4p ] structure
    let (hacl_Hash_SHA2_uint8_2x4p :
      [ `hacl_Hash_SHA2_uint8_2x4p ] structure typ) =
      structure "Hacl_Hash_SHA2_uint8_2x4p_s"
    let hacl_Hash_SHA2_uint8_2x4p_fst =
      field hacl_Hash_SHA2_uint8_2x4p "fst"
        k____uint8_t___uint8_t____K____uint8_t___uint8_t_
    let hacl_Hash_SHA2_uint8_2x4p_snd =
      field hacl_Hash_SHA2_uint8_2x4p "snd"
        k____uint8_t___uint8_t____K____uint8_t___uint8_t_
    let _ = seal hacl_Hash_SHA2_uint8_2x4p
    type hacl_Hash_SHA2_uint8_2x8p = [ `hacl_Hash_SHA2_uint8_2x8p ] structure
    let (hacl_Hash_SHA2_uint8_2x8p :
      [ `hacl_Hash_SHA2_uint8_2x8p ] structure typ) =
      structure "Hacl_Hash_SHA2_uint8_2x8p_s"
    let hacl_Hash_SHA2_uint8_2x8p_fst =
      field hacl_Hash_SHA2_uint8_2x8p "fst" hacl_Hash_SHA2_uint8_8p
    let hacl_Hash_SHA2_uint8_2x8p_snd =
      field hacl_Hash_SHA2_uint8_2x8p "snd" hacl_Hash_SHA2_uint8_8p
    let _ = seal hacl_Hash_SHA2_uint8_2x8p
  end