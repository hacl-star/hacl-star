let _ =
  (((Format.set_formatter_out_channel (open_out_bin "lib/Hacl_Spec_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module Hacl_Spec_bindings.Bindings));
    Format.set_formatter_out_channel (open_out_bin "lib/Hacl_Spec_c_stubs.c"));
   Format.printf
     "#include \"Hacl_Spec.h\"\n#include \"internal/Hacl_Spec.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module Hacl_Spec_bindings.Bindings)