let _ =
  (((Format.set_formatter_out_channel (open_out_bin "lib/Hacl_HMAC_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module Hacl_HMAC_bindings.Bindings));
    Format.set_formatter_out_channel (open_out_bin "lib/Hacl_HMAC_c_stubs.c"));
   Format.printf
     "#include \"Hacl_HMAC.h\"\n#include \"internal/Hacl_HMAC.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module Hacl_HMAC_bindings.Bindings)