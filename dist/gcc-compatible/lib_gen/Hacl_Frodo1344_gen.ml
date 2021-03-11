let _ =
  (((Format.set_formatter_out_channel
       (open_out_bin "lib/Hacl_Frodo1344_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module Hacl_Frodo1344_bindings.Bindings));
    Format.set_formatter_out_channel
      (open_out_bin "lib/Hacl_Frodo1344_c_stubs.c"));
   Format.printf "#include \"Hacl_Frodo1344.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module Hacl_Frodo1344_bindings.Bindings)