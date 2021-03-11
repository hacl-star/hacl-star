let _ =
  (((Format.set_formatter_out_channel
       (open_out_bin "lib/Hacl_RSAPSS2048_SHA256_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module Hacl_RSAPSS2048_SHA256_bindings.Bindings));
    Format.set_formatter_out_channel
      (open_out_bin "lib/Hacl_RSAPSS2048_SHA256_c_stubs.c"));
   Format.printf "#include \"Hacl_RSAPSS2048_SHA256.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module Hacl_RSAPSS2048_SHA256_bindings.Bindings)