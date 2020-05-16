let _ =
  (((Format.set_formatter_out_channel (open_out_bin "lib/Hacl_SHA3_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module Hacl_SHA3_bindings.Bindings));
    Format.set_formatter_out_channel (open_out_bin "lib/Hacl_SHA3_c_stubs.c"));
   Format.printf "#include \"Hacl_SHA3.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module Hacl_SHA3_bindings.Bindings)