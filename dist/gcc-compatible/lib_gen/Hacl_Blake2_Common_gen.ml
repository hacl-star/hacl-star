let _ =
  (((Format.set_formatter_out_channel
       (open_out_bin "lib/Hacl_Blake2_Common_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module Hacl_Blake2_Common_bindings.Bindings));
    Format.set_formatter_out_channel
      (open_out_bin "lib/Hacl_Blake2_Common_c_stubs.c"));
   Format.printf "#include \"Hacl_Blake2_Common.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module Hacl_Blake2_Common_bindings.Bindings)