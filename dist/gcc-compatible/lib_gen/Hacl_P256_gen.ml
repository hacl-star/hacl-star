let _ =
  (((Format.set_formatter_out_channel (open_out_bin "lib/Hacl_P256_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module Hacl_P256_bindings.Bindings));
    Format.set_formatter_out_channel (open_out_bin "lib/Hacl_P256_c_stubs.c"));
   Format.printf
     "#include \"Hacl_P256.h\"\n#include \"internal/Hacl_P256.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module Hacl_P256_bindings.Bindings)