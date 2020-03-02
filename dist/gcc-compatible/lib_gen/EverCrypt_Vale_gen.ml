let _ =
  (((Format.set_formatter_out_channel
       (open_out_bin "lib/EverCrypt_Vale_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module EverCrypt_Vale_bindings.Bindings));
    Format.set_formatter_out_channel
      (open_out_bin "lib/EverCrypt_Vale_c_stubs.c"));
   Format.printf "#include \"EverCrypt_Vale.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module EverCrypt_Vale_bindings.Bindings)