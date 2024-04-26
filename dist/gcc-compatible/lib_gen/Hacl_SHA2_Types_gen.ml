let _ =
  (((Format.set_formatter_out_channel
       (open_out_bin "lib/Hacl_SHA2_Types_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module Hacl_SHA2_Types_bindings.Bindings));
    Format.set_formatter_out_channel
      (open_out_bin "lib/Hacl_SHA2_Types_c_stubs.c"));
   Format.printf
     "#include \"Hacl_SHA2_Types.h\"\n#include \"internal/Hacl_SHA2_Types.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module Hacl_SHA2_Types_bindings.Bindings)