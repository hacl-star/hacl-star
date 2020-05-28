let _ =
  (((Format.set_formatter_out_channel
       (open_out_bin "lib/Hacl_Chacha20_Vec256_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module Hacl_Chacha20_Vec256_bindings.Bindings));
    Format.set_formatter_out_channel
      (open_out_bin "lib/Hacl_Chacha20_Vec256_c_stubs.c"));
   Format.printf "#include \"Hacl_Chacha20_Vec256.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module Hacl_Chacha20_Vec256_bindings.Bindings)