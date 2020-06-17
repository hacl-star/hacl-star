let _ =
  (((Format.set_formatter_out_channel
       (open_out_bin "lib/EverCrypt_CTR_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module EverCrypt_CTR_bindings.Bindings));
    Format.set_formatter_out_channel
      (open_out_bin "lib/EverCrypt_CTR_c_stubs.c"));
   Format.printf "#include \"EverCrypt_CTR.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module EverCrypt_CTR_bindings.Bindings)