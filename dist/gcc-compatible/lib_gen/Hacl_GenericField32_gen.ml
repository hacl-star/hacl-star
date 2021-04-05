let _ =
  (((Format.set_formatter_out_channel
       (open_out_bin "lib/Hacl_GenericField32_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module Hacl_GenericField32_bindings.Bindings));
    Format.set_formatter_out_channel
      (open_out_bin "lib/Hacl_GenericField32_c_stubs.c"));
   Format.printf "#include \"Hacl_GenericField32.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module Hacl_GenericField32_bindings.Bindings)