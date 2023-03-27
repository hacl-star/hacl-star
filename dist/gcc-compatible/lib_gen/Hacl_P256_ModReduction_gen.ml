let _ =
  (((Format.set_formatter_out_channel
       (open_out_bin "lib/Hacl_P256_ModReduction_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module Hacl_P256_ModReduction_bindings.Bindings));
    Format.set_formatter_out_channel
      (open_out_bin "lib/Hacl_P256_ModReduction_c_stubs.c"));
   Format.printf "#include \"Hacl_P256_ModReduction.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module Hacl_P256_ModReduction_bindings.Bindings)