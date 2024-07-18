let _ =
  (((Format.set_formatter_out_channel
       (open_out_bin "lib/Hacl_MAC_Poly1305_Simd128_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module Hacl_MAC_Poly1305_Simd128_bindings.Bindings));
    Format.set_formatter_out_channel
      (open_out_bin "lib/Hacl_MAC_Poly1305_Simd128_c_stubs.c"));
   Format.printf
     "#include \"Hacl_MAC_Poly1305_Simd128.h\"\n#include \"internal/Hacl_MAC_Poly1305_Simd128.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module Hacl_MAC_Poly1305_Simd128_bindings.Bindings)