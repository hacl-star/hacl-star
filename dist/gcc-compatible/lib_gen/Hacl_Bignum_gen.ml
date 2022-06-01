let _ =
  (((Format.set_formatter_out_channel
       (open_out_bin "lib/Hacl_Bignum_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module Hacl_Bignum_bindings.Bindings));
    Format.set_formatter_out_channel
      (open_out_bin "lib/Hacl_Bignum_c_stubs.c"));
   Format.printf "#include \"internal/Hacl_Bignum.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module Hacl_Bignum_bindings.Bindings)