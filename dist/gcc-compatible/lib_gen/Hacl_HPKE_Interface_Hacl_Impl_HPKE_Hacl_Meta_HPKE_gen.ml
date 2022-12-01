let _ =
  (((Format.set_formatter_out_channel
       (open_out_bin
          "lib/Hacl_HPKE_Interface_Hacl_Impl_HPKE_Hacl_Meta_HPKE_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module
          Hacl_HPKE_Interface_Hacl_Impl_HPKE_Hacl_Meta_HPKE_bindings.Bindings));
    Format.set_formatter_out_channel
      (open_out_bin
         "lib/Hacl_HPKE_Interface_Hacl_Impl_HPKE_Hacl_Meta_HPKE_c_stubs.c"));
   Format.printf
     "#include \"Hacl_HPKE_Interface_Hacl_Impl_HPKE_Hacl_Meta_HPKE.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module
       Hacl_HPKE_Interface_Hacl_Impl_HPKE_Hacl_Meta_HPKE_bindings.Bindings)