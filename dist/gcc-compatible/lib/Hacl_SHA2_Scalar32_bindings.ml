open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_SHA2_Scalar32_sha224 =
      foreign "Hacl_SHA2_Scalar32_sha224"
        (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void))))
    let hacl_SHA2_Scalar32_sha256 =
      foreign "Hacl_SHA2_Scalar32_sha256"
        (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void))))
    let hacl_SHA2_Scalar32_sha384 =
      foreign "Hacl_SHA2_Scalar32_sha384"
        (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void))))
    let hacl_SHA2_Scalar32_sha512 =
      foreign "Hacl_SHA2_Scalar32_sha512"
        (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void))))
  end