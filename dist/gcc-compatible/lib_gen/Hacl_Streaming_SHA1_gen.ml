let _ =
  (((Format.set_formatter_out_channel
       (open_out_bin "lib/Hacl_Streaming_SHA1_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module Hacl_Streaming_SHA1_bindings.Bindings));
    Format.set_formatter_out_channel
      (open_out_bin "lib/Hacl_Streaming_SHA1_c_stubs.c"));
   Format.printf "#include \"Hacl_Streaming_SHA1.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module Hacl_Streaming_SHA1_bindings.Bindings)