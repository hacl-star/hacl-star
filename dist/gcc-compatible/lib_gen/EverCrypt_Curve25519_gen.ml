let _ =
  (((Format.set_formatter_out_channel
       (open_out_bin "lib/EverCrypt_Curve25519_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module EverCrypt_Curve25519_bindings.Bindings));
    Format.set_formatter_out_channel
      (open_out_bin "lib/EverCrypt_Curve25519_c_stubs.c"));
   Format.printf "#include \"EverCrypt_Curve25519.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module EverCrypt_Curve25519_bindings.Bindings)