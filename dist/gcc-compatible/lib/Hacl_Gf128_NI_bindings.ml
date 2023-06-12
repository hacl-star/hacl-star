open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Impl_Gf128_FieldPreComp_fmul =
      foreign "Hacl_Impl_Gf128_FieldPreComp_fmul"
        ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void)))
    let hacl_Impl_Gf128_FieldPreComp_load_precompute_r =
      foreign "Hacl_Impl_Gf128_FieldPreComp_load_precompute_r"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_Impl_Gf128_FieldPreComp_fmul_r4 =
      foreign "Hacl_Impl_Gf128_FieldPreComp_fmul_r4"
        ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void)))
    let hacl_Impl_Gf128_FieldPreComp_normalize4 =
      foreign "Hacl_Impl_Gf128_FieldPreComp_normalize4"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_Gf128_NI_ghash =
      foreign "Hacl_Gf128_NI_ghash"
        (ocaml_bytes @->
           (uint32_t @-> (ocaml_bytes @-> (ocaml_bytes @-> (returning void)))))
  end