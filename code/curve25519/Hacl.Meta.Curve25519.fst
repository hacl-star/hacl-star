module Hacl.Meta.Curve25519

#set-options "--print_implicits --print_full_names"

friend Hacl.Impl.Curve25519.Generic

%splice[
  generic_cswap2_higher;
  fields_fadd_higher;
  fields_fsub_higher;
  fields_fmul2_higher;
  addanddouble_point_add_and_double0_higher;
  fields_fsqr2_higher;
  fields_fmul1_higher;
  addanddouble_point_add_and_double1_higher;
  fields_fmul_higher;
  addanddouble_point_add_and_double_higher;
  generic_ladder_step_higher;
  generic_ladder_step_loop_higher;
  generic_ladder0__higher;
  addanddouble_point_double_higher;
  generic_ladder1__higher;
  generic_ladder2__higher;
  generic_ladder4__higher;
  generic_montgomery_ladder_higher;
  finv_fsqr_s_higher;
  finv_fsquare_times_higher;
  finv_fmul_s_higher;
  finv_finv0_higher;
  finv_finv_higher;
  field64_carry_pass_store_higher;
  field64_store_felem_higher;
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
