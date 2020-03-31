let _ =
  (((Format.set_formatter_out_channel
       (open_out_bin "lib/EverCrypt_AutoConfig2_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module EverCrypt_AutoConfig2_bindings.Bindings));
    Format.set_formatter_out_channel
      (open_out_bin "lib/EverCrypt_AutoConfig2_c_stubs.c"));
   Format.printf "#include \"EverCrypt_AutoConfig2.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module EverCrypt_AutoConfig2_bindings.Bindings)