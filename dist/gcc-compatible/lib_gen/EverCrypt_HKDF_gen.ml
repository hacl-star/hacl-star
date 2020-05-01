let _ =
  (((Format.set_formatter_out_channel
       (open_out_bin "lib/EverCrypt_HKDF_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module EverCrypt_HKDF_bindings.Bindings));
    Format.set_formatter_out_channel
      (open_out_bin "lib/EverCrypt_HKDF_c_stubs.c"));
   Format.printf "#include \"EverCrypt_HKDF.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module EverCrypt_HKDF_bindings.Bindings)