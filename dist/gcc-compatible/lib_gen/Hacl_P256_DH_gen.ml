let _ =
  (((Format.set_formatter_out_channel
       (open_out_bin "lib/Hacl_P256_DH_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module Hacl_P256_DH_bindings.Bindings));
    Format.set_formatter_out_channel
      (open_out_bin "lib/Hacl_P256_DH_c_stubs.c"));
   Format.printf "#include \"Hacl_P256_DH.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module Hacl_P256_DH_bindings.Bindings)
  