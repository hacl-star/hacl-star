let _ =
  (((Format.set_formatter_out_channel
       (open_out_bin "lib/Hacl_SHA2_Vec512_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module Hacl_SHA2_Vec512_bindings.Bindings));
    Format.set_formatter_out_channel
      (open_out_bin "lib/Hacl_SHA2_Vec512_c_stubs.c"));
   Format.printf "#include \"Hacl_SHA2_Vec512.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module Hacl_SHA2_Vec512_bindings.Bindings)