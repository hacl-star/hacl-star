module Hacl.Meta.Curve25519

#set-options "--max_fuel 2 --max_ifuel 1 --z3rlimit 300 --print_implicits --print_full_names"

// For debugging
#set-options "--admit_smt_queries true --print_effect_args"

friend Hacl.Impl.Curve25519.Generic

%splice[
(*  // From Finv.
  fsqr_s_higher;
  fmul_s_higher;
  fsquare_times_higher;
  finv_higher;
  // From AddAnddouble
  point_add_and_double_higher;
  point_double_higher;
  // From Generic
  encode_higher;
  cswap2_higher;
  montgomery_ladder_higher;
  decode_point_higher;
  scalarmult_higher;
  secret_to_public_higher;
  ecdh_higher *)
]
(Meta.Interface.specialize (`Hacl.Impl.Curve25519.Fields.field_spec) [
  `Hacl.Impl.Curve25519.Generic.scalarmult;
  `Hacl.Impl.Curve25519.Generic.secret_to_public;
  `Hacl.Impl.Curve25519.Generic.ecdh
])
