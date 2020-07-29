let _ =
  (((Format.set_formatter_out_channel
       (open_out_bin "lib/Hacl_HMAC_Blake2s_128_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module Hacl_HMAC_Blake2s_128_bindings.Bindings));
    Format.set_formatter_out_channel
      (open_out_bin "lib/Hacl_HMAC_Blake2s_128_c_stubs.c"));
   Format.printf "#include \"Hacl_HMAC_Blake2s_128.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module Hacl_HMAC_Blake2s_128_bindings.Bindings)