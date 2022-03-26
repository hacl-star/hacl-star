let _ =
  (((Format.set_formatter_out_channel
       (open_out_bin "lib/Hacl_Hash_Blake2_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module Hacl_Hash_Blake2_bindings.Bindings));
    Format.set_formatter_out_channel
      (open_out_bin "lib/Hacl_Hash_Blake2_c_stubs.c"));
   Format.printf
     "#include \"Hacl_Hash_Blake2.h\"\n#include \"internal/Hacl_Hash_Blake2.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module Hacl_Hash_Blake2_bindings.Bindings)