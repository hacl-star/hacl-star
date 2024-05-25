let _ =
  (((Format.set_formatter_out_channel
       (open_out_bin "lib/Hacl_Gf128_NI_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module Hacl_Gf128_NI_bindings.Bindings));
    Format.set_formatter_out_channel
      (open_out_bin "lib/Hacl_Gf128_NI_c_stubs.c"));
   Format.printf "#include \"Hacl_Gf128_NI.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module Hacl_Gf128_NI_bindings.Bindings)