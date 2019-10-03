module Hacl.Meta.Curve25519

#set-options "--z3rlimit 250 --max_fuel 0 --max_ifuel 1"

friend Hacl.Impl.Curve25519.Generic

%splice[
  // From Finv.
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
  ecdh_higher
] (Meta.Interface.specialize [
    `Hacl.Impl.Curve25519.Generic.ecdh;
    `Hacl.Impl.Curve25519.Generic.secret_to_public;
    `Hacl.Impl.Curve25519.Generic.scalarmult
])
