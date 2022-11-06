open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
struct
  open F
  let randombytes =
    foreign "Lib_RandomBuffer_System_randombytes"
      (ocaml_bytes @-> uint32_t @-> returning bool)
end
