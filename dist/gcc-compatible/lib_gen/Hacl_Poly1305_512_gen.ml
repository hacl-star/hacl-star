let _ =
  (((Format.set_formatter_out_channel
       (open_out_bin "lib/Hacl_Poly1305_512_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module Hacl_Poly1305_512_bindings.Bindings));
    Format.set_formatter_out_channel
      (open_out_bin "lib/Hacl_Poly1305_512_c_stubs.c"));
   Format.printf "#include \"Hacl_Poly1305_512.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module Hacl_Poly1305_512_bindings.Bindings)