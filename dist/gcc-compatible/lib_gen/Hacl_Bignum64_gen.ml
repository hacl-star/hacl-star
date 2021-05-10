let _ =
  (((Format.set_formatter_out_channel
       (open_out_bin "lib/Hacl_Bignum64_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module Hacl_Bignum64_bindings.Bindings));
    Format.set_formatter_out_channel
      (open_out_bin "lib/Hacl_Bignum64_c_stubs.c"));
   Format.printf "#include \"Hacl_Bignum64.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module Hacl_Bignum64_bindings.Bindings)