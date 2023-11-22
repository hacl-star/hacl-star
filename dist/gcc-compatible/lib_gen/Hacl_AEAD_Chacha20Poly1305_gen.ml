let _ =
  (((Format.set_formatter_out_channel
       (open_out_bin "lib/Hacl_AEAD_Chacha20Poly1305_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module Hacl_AEAD_Chacha20Poly1305_bindings.Bindings));
    Format.set_formatter_out_channel
      (open_out_bin "lib/Hacl_AEAD_Chacha20Poly1305_c_stubs.c"));
   Format.printf "#include \"Hacl_AEAD_Chacha20Poly1305.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module Hacl_AEAD_Chacha20Poly1305_bindings.Bindings)