open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_FFDHE4096_ffdhe_secret_to_public =
      foreign "Hacl_FFDHE4096_ffdhe_secret_to_public"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning void)))
    let hacl_FFDHE4096_ffdhe_shared_secret =
      foreign "Hacl_FFDHE4096_ffdhe_shared_secret"
        (ocaml_bytes @->
           (ocaml_bytes @-> (ocaml_bytes @-> (returning uint64_t))))
  end