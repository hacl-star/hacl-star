let _ =
  (((Format.set_formatter_out_channel
       (open_out_bin "lib/EverCrypt_StaticConfig_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module EverCrypt_StaticConfig_bindings.Bindings));
    Format.set_formatter_out_channel
      (open_out_bin "lib/EverCrypt_StaticConfig_c_stubs.c"));
   Format.printf "#include \"EverCrypt_StaticConfig.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module EverCrypt_StaticConfig_bindings.Bindings)