let _ =
  (((Format.set_formatter_out_channel
       (open_out_bin "lib/EverCrypt_Helpers_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module EverCrypt_Helpers_bindings.Bindings));
    Format.set_formatter_out_channel
      (open_out_bin "lib/EverCrypt_Helpers_c_stubs.c"));
   Format.printf "#include \"EverCrypt_Helpers.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module EverCrypt_Helpers_bindings.Bindings)
  