let _ =
  (((Format.set_formatter_out_channel
       (open_out_bin "lib/EverCrypt_Cipher_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module EverCrypt_Cipher_bindings.Bindings));
    Format.set_formatter_out_channel
      (open_out_bin "lib/EverCrypt_Cipher_c_stubs.c"));
   Format.printf "#include \"EverCrypt_Cipher.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module EverCrypt_Cipher_bindings.Bindings)