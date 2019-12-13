let _ =
  (((Format.set_formatter_out_channel
       (open_out_bin "lib/Hacl_HMAC_DRBG_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module Hacl_HMAC_DRBG_bindings.Bindings));
    Format.set_formatter_out_channel
      (open_out_bin "lib/Hacl_HMAC_DRBG_c_stubs.c"));
   Format.printf "#include \"Hacl_HMAC_DRBG.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module Hacl_HMAC_DRBG_bindings.Bindings)