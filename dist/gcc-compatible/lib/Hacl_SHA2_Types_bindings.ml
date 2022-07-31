open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    type hacl_Impl_SHA2_Types_uint8_2p =
      [ `hacl_Impl_SHA2_Types_uint8_2p ] structure
    let (hacl_Impl_SHA2_Types_uint8_2p :
      [ `hacl_Impl_SHA2_Types_uint8_2p ] structure typ) =
      structure "Hacl_Impl_SHA2_Types_uint8_2p_s"
    let hacl_Impl_SHA2_Types_uint8_2p_fst =
      field hacl_Impl_SHA2_Types_uint8_2p "fst" (ptr uint8_t)
    let hacl_Impl_SHA2_Types_uint8_2p_snd =
      field hacl_Impl_SHA2_Types_uint8_2p "snd" (ptr uint8_t)
    let _ = seal hacl_Impl_SHA2_Types_uint8_2p
    type hacl_Impl_SHA2_Types_uint8_3p =
      [ `hacl_Impl_SHA2_Types_uint8_3p ] structure
    let (hacl_Impl_SHA2_Types_uint8_3p :
      [ `hacl_Impl_SHA2_Types_uint8_3p ] structure typ) =
      structure "Hacl_Impl_SHA2_Types_uint8_3p_s"
    let hacl_Impl_SHA2_Types_uint8_3p_fst =
      field hacl_Impl_SHA2_Types_uint8_3p "fst" (ptr uint8_t)
    let hacl_Impl_SHA2_Types_uint8_3p_snd =
      field hacl_Impl_SHA2_Types_uint8_3p "snd" hacl_Impl_SHA2_Types_uint8_2p
    let _ = seal hacl_Impl_SHA2_Types_uint8_3p
    type hacl_Impl_SHA2_Types_uint8_4p =
      [ `hacl_Impl_SHA2_Types_uint8_4p ] structure
    let (hacl_Impl_SHA2_Types_uint8_4p :
      [ `hacl_Impl_SHA2_Types_uint8_4p ] structure typ) =
      structure "Hacl_Impl_SHA2_Types_uint8_4p_s"
    let hacl_Impl_SHA2_Types_uint8_4p_fst =
      field hacl_Impl_SHA2_Types_uint8_4p "fst" (ptr uint8_t)
    let hacl_Impl_SHA2_Types_uint8_4p_snd =
      field hacl_Impl_SHA2_Types_uint8_4p "snd" hacl_Impl_SHA2_Types_uint8_3p
    let _ = seal hacl_Impl_SHA2_Types_uint8_4p
    type hacl_Impl_SHA2_Types_uint8_5p =
      [ `hacl_Impl_SHA2_Types_uint8_5p ] structure
    let (hacl_Impl_SHA2_Types_uint8_5p :
      [ `hacl_Impl_SHA2_Types_uint8_5p ] structure typ) =
      structure "Hacl_Impl_SHA2_Types_uint8_5p_s"
    let hacl_Impl_SHA2_Types_uint8_5p_fst =
      field hacl_Impl_SHA2_Types_uint8_5p "fst" (ptr uint8_t)
    let hacl_Impl_SHA2_Types_uint8_5p_snd =
      field hacl_Impl_SHA2_Types_uint8_5p "snd" hacl_Impl_SHA2_Types_uint8_4p
    let _ = seal hacl_Impl_SHA2_Types_uint8_5p
    type hacl_Impl_SHA2_Types_uint8_6p =
      [ `hacl_Impl_SHA2_Types_uint8_6p ] structure
    let (hacl_Impl_SHA2_Types_uint8_6p :
      [ `hacl_Impl_SHA2_Types_uint8_6p ] structure typ) =
      structure "Hacl_Impl_SHA2_Types_uint8_6p_s"
    let hacl_Impl_SHA2_Types_uint8_6p_fst =
      field hacl_Impl_SHA2_Types_uint8_6p "fst" (ptr uint8_t)
    let hacl_Impl_SHA2_Types_uint8_6p_snd =
      field hacl_Impl_SHA2_Types_uint8_6p "snd" hacl_Impl_SHA2_Types_uint8_5p
    let _ = seal hacl_Impl_SHA2_Types_uint8_6p
    type hacl_Impl_SHA2_Types_uint8_7p =
      [ `hacl_Impl_SHA2_Types_uint8_7p ] structure
    let (hacl_Impl_SHA2_Types_uint8_7p :
      [ `hacl_Impl_SHA2_Types_uint8_7p ] structure typ) =
      structure "Hacl_Impl_SHA2_Types_uint8_7p_s"
    let hacl_Impl_SHA2_Types_uint8_7p_fst =
      field hacl_Impl_SHA2_Types_uint8_7p "fst" (ptr uint8_t)
    let hacl_Impl_SHA2_Types_uint8_7p_snd =
      field hacl_Impl_SHA2_Types_uint8_7p "snd" hacl_Impl_SHA2_Types_uint8_6p
    let _ = seal hacl_Impl_SHA2_Types_uint8_7p
    type hacl_Impl_SHA2_Types_uint8_8p =
      [ `hacl_Impl_SHA2_Types_uint8_8p ] structure
    let (hacl_Impl_SHA2_Types_uint8_8p :
      [ `hacl_Impl_SHA2_Types_uint8_8p ] structure typ) =
      structure "Hacl_Impl_SHA2_Types_uint8_8p_s"
    let hacl_Impl_SHA2_Types_uint8_8p_fst =
      field hacl_Impl_SHA2_Types_uint8_8p "fst" (ptr uint8_t)
    let hacl_Impl_SHA2_Types_uint8_8p_snd =
      field hacl_Impl_SHA2_Types_uint8_8p "snd" hacl_Impl_SHA2_Types_uint8_7p
    let _ = seal hacl_Impl_SHA2_Types_uint8_8p
    type hacl_Impl_SHA2_Types_uint8_2x4p =
      [ `hacl_Impl_SHA2_Types_uint8_2x4p ] structure
    let (hacl_Impl_SHA2_Types_uint8_2x4p :
      [ `hacl_Impl_SHA2_Types_uint8_2x4p ] structure typ) =
      structure "Hacl_Impl_SHA2_Types_uint8_2x4p_s"
    let hacl_Impl_SHA2_Types_uint8_2x4p_fst =
      field hacl_Impl_SHA2_Types_uint8_2x4p "fst"
        hacl_Impl_SHA2_Types_uint8_4p
    let hacl_Impl_SHA2_Types_uint8_2x4p_snd =
      field hacl_Impl_SHA2_Types_uint8_2x4p "snd"
        hacl_Impl_SHA2_Types_uint8_4p
    let _ = seal hacl_Impl_SHA2_Types_uint8_2x4p
    type hacl_Impl_SHA2_Types_uint8_2x8p =
      [ `hacl_Impl_SHA2_Types_uint8_2x8p ] structure
    let (hacl_Impl_SHA2_Types_uint8_2x8p :
      [ `hacl_Impl_SHA2_Types_uint8_2x8p ] structure typ) =
      structure "Hacl_Impl_SHA2_Types_uint8_2x8p_s"
    let hacl_Impl_SHA2_Types_uint8_2x8p_fst =
      field hacl_Impl_SHA2_Types_uint8_2x8p "fst"
        hacl_Impl_SHA2_Types_uint8_8p
    let hacl_Impl_SHA2_Types_uint8_2x8p_snd =
      field hacl_Impl_SHA2_Types_uint8_2x8p "snd"
        hacl_Impl_SHA2_Types_uint8_8p
    let _ = seal hacl_Impl_SHA2_Types_uint8_2x8p
  end