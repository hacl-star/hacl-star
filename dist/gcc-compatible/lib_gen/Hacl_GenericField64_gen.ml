let _ =
  (((Format.set_formatter_out_channel
       (open_out_bin "lib/Hacl_GenericField64_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module Hacl_GenericField64_bindings.Bindings));
    Format.set_formatter_out_channel
      (open_out_bin "lib/Hacl_GenericField64_c_stubs.c"));
   Format.printf "#include \"Hacl_GenericField64.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module Hacl_GenericField64_bindings.Bindings)