let _ =
  (((Format.set_formatter_out_channel
       (open_out_bin "lib/Hacl_Blake2bUnkeyed_stubs.ml");
     Cstubs.write_ml Format.std_formatter ~prefix:""
       (module Hacl_Blake2bUnkeyed_bindings.Bindings));
    Format.set_formatter_out_channel
      (open_out_bin "lib/Hacl_Blake2bUnkeyed_c_stubs.c"));
   Format.printf "#include \"Hacl_Blake2bUnkeyed.h\"\n");
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module Hacl_Blake2bUnkeyed_bindings.Bindings)
  