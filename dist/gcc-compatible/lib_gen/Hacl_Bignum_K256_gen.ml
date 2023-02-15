let _ =
  (((Format.set_formatter_out_channel
       (open_out_bin "lib/Hacl_Bignum_K256_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module Hacl_Bignum_K256_bindings.Bindings));
    Format.set_formatter_out_channel
      (open_out_bin "lib/Hacl_Bignum_K256_c_stubs.c"));
   Format.printf "#include \"internal/Hacl_Bignum_K256.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module Hacl_Bignum_K256_bindings.Bindings)