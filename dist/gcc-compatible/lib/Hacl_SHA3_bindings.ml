open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Impl_SHA3_rotl =
      foreign "Hacl_Impl_SHA3_rotl"
        (uint64_t @-> (uint32_t @-> (returning uint64_t)))
    let hacl_Impl_SHA3_state_permute =
      foreign "Hacl_Impl_SHA3_state_permute"
        ((ptr uint64_t) @-> (returning void))
    let hacl_Impl_SHA3_loadState =
      foreign "Hacl_Impl_SHA3_loadState"
        (uint32_t @-> (ocaml_bytes @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_Impl_SHA3_storeState =
      foreign "Hacl_Impl_SHA3_storeState"
        (uint32_t @-> ((ptr uint64_t) @-> (ocaml_bytes @-> (returning void))))
    let hacl_Impl_SHA3_absorb =
      foreign "Hacl_Impl_SHA3_absorb"
        ((ptr uint64_t) @->
           (uint32_t @->
              (uint32_t @-> (ocaml_bytes @-> (uint8_t @-> (returning void))))))
    let hacl_Impl_SHA3_squeeze =
      foreign "Hacl_Impl_SHA3_squeeze"
        ((ptr uint64_t) @->
           (uint32_t @-> (uint32_t @-> (ocaml_bytes @-> (returning void)))))
    let hacl_Impl_SHA3_keccak =
      foreign "Hacl_Impl_SHA3_keccak"
        (uint32_t @->
           (uint32_t @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint8_t @->
                       (uint32_t @-> (ocaml_bytes @-> (returning void))))))))
    let hacl_SHA3_shake128_hacl =
      foreign "Hacl_SHA3_shake128_hacl"
        (uint32_t @->
           (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void)))))
    let hacl_SHA3_shake256_hacl =
      foreign "Hacl_SHA3_shake256_hacl"
        (uint32_t @->
           (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void)))))
    let hacl_SHA3_sha3_224 =
      foreign "Hacl_SHA3_sha3_224"
        (uint32_t @-> (ocaml_bytes @-> (ocaml_bytes @-> (returning void))))
    let hacl_SHA3_sha3_256 =
      foreign "Hacl_SHA3_sha3_256"
        (uint32_t @-> (ocaml_bytes @-> (ocaml_bytes @-> (returning void))))
    let hacl_SHA3_sha3_384 =
      foreign "Hacl_SHA3_sha3_384"
        (uint32_t @-> (ocaml_bytes @-> (ocaml_bytes @-> (returning void))))
    let hacl_SHA3_sha3_512 =
      foreign "Hacl_SHA3_sha3_512"
        (uint32_t @-> (ocaml_bytes @-> (ocaml_bytes @-> (returning void))))
  end