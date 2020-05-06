let _ =
  (((Format.set_formatter_out_channel
       (open_out_bin "lib/EverCrypt_Hacl_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module EverCrypt_Hacl_bindings.Bindings));
    Format.set_formatter_out_channel
      (open_out_bin "lib/EverCrypt_Hacl_c_stubs.c"));
   Format.printf "#include \"EverCrypt_Hacl.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module EverCrypt_Hacl_bindings.Bindings)
  