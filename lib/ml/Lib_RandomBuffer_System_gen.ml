let _ =
  Format.set_formatter_out_channel (open_out_bin "lib/Lib_RandomBuffer_System_stubs.ml");
  Cstubs.write_ml Format.std_formatter ~prefix:""
    (module Lib_RandomBuffer_System_bindings.Bindings);
  Format.set_formatter_out_channel (open_out_bin "lib/Lib_RandomBuffer_System_c_stubs.c");
  Format.printf "#include \"Lib_RandomBuffer_System.h\"\n";
  Cstubs.write_c Format.std_formatter ~prefix:""
    (module Lib_RandomBuffer_System_bindings.Bindings)

