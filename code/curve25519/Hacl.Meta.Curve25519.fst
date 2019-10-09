module Hacl.Meta.Curve25519

#set-options "--print_implicits --print_full_names --print_effect_args"

friend Hacl.Impl.Curve25519.Generic

// Hacl_Meta_Curve25519_addanddouble_point_add_and_double_higher
//   (needs: Hacl_Impl_Curve25519_Fields_Core_fmul, Hacl_Impl_Curve25519_Fields_Core_fsqr2, Hacl_Impl_Curve25519_Fields_Core_fmul1, Hacl_Impl_Curve25519_Fields_Core_fmul2, Hacl_Impl_Curve25519_Fields_Core_fsub, Hacl_Impl_Curve25519_Fields_Core_fadd)
// Hacl_Meta_Curve25519_addanddouble_point_double_higher
//   (needs: Hacl_Impl_Curve25519_Fields_Core_fmul2, Hacl_Impl_Curve25519_Fields_Core_fmul1, Hacl_Impl_Curve25519_Fields_Core_fsqr2, Hacl_Impl_Curve25519_Fields_Core_fsub, Hacl_Impl_Curve25519_Fields_Core_fadd)
// Hacl_Meta_Curve25519_generic_montgomery_ladder_higher
//   (needs: Hacl_Impl_Curve25519_AddAndDouble_point_double, Hacl_Impl_Curve25519_Fields_Core_cswap2, Hacl_Impl_Curve25519_AddAndDouble_point_add_and_double)
// Hacl_Meta_Curve25519_finv_fsquare_times_higher
//   (needs: Hacl_Impl_Curve25519_Fields_Core_fsqr)
// Hacl_Meta_Curve25519_finv_finv_higher
//   (needs: Hacl_Impl_Curve25519_Finv_fsquare_times, Hacl_Impl_Curve25519_Fields_Core_fmul)
// Hacl_Meta_Curve25519_fields_store_felem_higher
//   (needs: Hacl_Impl_Curve25519_Fields_Core_add1)
// Hacl_Meta_Curve25519_generic_encode_point_higher
//   (needs: Hacl_Impl_Curve25519_Fields_store_felem, Hacl_Impl_Curve25519_Fields_Core_fmul, Hacl_Impl_Curve25519_Finv_finv)
// Hacl_Meta_Curve25519_generic_scalarmult_higher
//   (needs: Hacl_Impl_Curve25519_Generic_encode_point, Hacl_Impl_Curve25519_Generic_montgomery_ladder, Hacl_Impl_Curve25519_Generic_decode_point)
// Hacl_Meta_Curve25519_generic_secret_to_public_higher
//   (needs: Hacl_Impl_Curve25519_Generic_scalarmult)
// Hacl_Meta_Curve25519_generic_ecdh_higher
//   (needs: Hacl_Impl_Curve25519_Generic_scalarmult)
%splice[
  addanddouble_point_add_and_double_higher;
  addanddouble_point_double_higher;
  generic_montgomery_ladder_higher;
  finv_fsquare_times_higher;
  finv_finv_higher;
  fields_store_felem_higher;
  generic_encode_point_higher;
  generic_scalarmult_higher;
  generic_secret_to_public_higher;
  generic_ecdh_higher
]
(Meta.Interface.specialize (`Hacl.Impl.Curve25519.Fields.field_spec) [
  `Hacl.Impl.Curve25519.Generic.scalarmult;
  `Hacl.Impl.Curve25519.Generic.secret_to_public;
  `Hacl.Impl.Curve25519.Generic.ecdh
])
