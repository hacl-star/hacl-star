let _ =
  (((Format.set_formatter_out_channel
       (open_out_bin "lib/Hacl_Ed25519_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module Hacl_Ed25519_bindings.Bindings));
    Format.set_formatter_out_channel
      (open_out_bin "lib/Hacl_Ed25519_c_stubs.c"));
   Format.printf
     "#include \"Hacl_Ed25519.h\"\n#include \"internal/Hacl_Ed25519.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module Hacl_Ed25519_bindings.Bindings)