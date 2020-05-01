let _ =
  (((Format.set_formatter_out_channel (open_out_bin "lib/Hacl_NaCl_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module Hacl_NaCl_bindings.Bindings));
    Format.set_formatter_out_channel (open_out_bin "lib/Hacl_NaCl_c_stubs.c"));
   Format.printf "#include \"Hacl_NaCl.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module Hacl_NaCl_bindings.Bindings)