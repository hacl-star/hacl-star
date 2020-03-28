let _ =
  (((Format.set_formatter_out_channel
       (open_out_bin "lib/Hacl_Impl_Blake2_Constants_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module Hacl_Impl_Blake2_Constants_bindings.Bindings));
    Format.set_formatter_out_channel
      (open_out_bin "lib/Hacl_Impl_Blake2_Constants_c_stubs.c"));
   Format.printf "#include \"Hacl_Impl_Blake2_Constants.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module Hacl_Impl_Blake2_Constants_bindings.Bindings)
  