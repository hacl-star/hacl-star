let _ =
  (((Format.set_formatter_out_channel
       (open_out_bin "lib/Hacl_AES_128_BitSlice_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module Hacl_AES_128_BitSlice_bindings.Bindings));
    Format.set_formatter_out_channel
      (open_out_bin "lib/Hacl_AES_128_BitSlice_c_stubs.c"));
   Format.printf
     "#include \"Hacl_AES_128_BitSlice.h\"\n#include \"internal/Hacl_AES_128_BitSlice.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module Hacl_AES_128_BitSlice_bindings.Bindings)