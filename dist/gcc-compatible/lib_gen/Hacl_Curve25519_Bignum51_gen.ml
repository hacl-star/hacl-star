let _ =
  (((Format.set_formatter_out_channel
       (open_out_bin "lib/Hacl_Curve25519_Bignum51_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module Hacl_Curve25519_Bignum51_bindings.Bindings));
    Format.set_formatter_out_channel
      (open_out_bin "lib/Hacl_Curve25519_Bignum51_c_stubs.c"));
   Format.printf "#include \"Hacl_Curve25519_Bignum51.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module Hacl_Curve25519_Bignum51_bindings.Bindings)