let _ =
  (((Format.set_formatter_out_channel
       (open_out_bin "lib/Hacl_Bignum4096_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module Hacl_Bignum4096_bindings.Bindings));
    Format.set_formatter_out_channel
      (open_out_bin "lib/Hacl_Bignum4096_c_stubs.c"));
   Format.printf "#include \"Hacl_Bignum4096.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module Hacl_Bignum4096_bindings.Bindings)