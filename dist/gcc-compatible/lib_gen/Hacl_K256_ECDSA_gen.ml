let _ =
  (((Format.set_formatter_out_channel
       (open_out_bin "lib/Hacl_K256_ECDSA_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module Hacl_K256_ECDSA_bindings.Bindings));
    Format.set_formatter_out_channel
      (open_out_bin "lib/Hacl_K256_ECDSA_c_stubs.c"));
   Format.printf
     "#include \"Hacl_K256_ECDSA.h\"\n#include \"internal/Hacl_K256_ECDSA.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module Hacl_K256_ECDSA_bindings.Bindings)