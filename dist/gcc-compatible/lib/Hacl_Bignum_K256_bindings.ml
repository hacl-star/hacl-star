open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_K256_Field_is_felem_zero_vartime =
      foreign "Hacl_K256_Field_is_felem_zero_vartime"
        ((ptr uint64_t) @-> (returning bool))
    let hacl_K256_Field_is_felem_eq_vartime =
      foreign "Hacl_K256_Field_is_felem_eq_vartime"
        ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning bool)))
    let hacl_K256_Field_is_felem_lt_prime_minus_order_vartime =
      foreign "Hacl_K256_Field_is_felem_lt_prime_minus_order_vartime"
        ((ptr uint64_t) @-> (returning bool))
    let hacl_K256_Field_load_felem =
      foreign "Hacl_K256_Field_load_felem"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_K256_Field_load_felem_lt_prime_vartime =
      foreign "Hacl_K256_Field_load_felem_lt_prime_vartime"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (returning bool)))
    let hacl_K256_Field_store_felem =
      foreign "Hacl_K256_Field_store_felem"
        (ocaml_bytes @-> ((ptr uint64_t) @-> (returning void)))
    let hacl_K256_Field_fmul_small_num =
      foreign "Hacl_K256_Field_fmul_small_num"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @-> (uint64_t @-> (returning void))))
    let hacl_K256_Field_fadd =
      foreign "Hacl_K256_Field_fadd"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_K256_Field_fsub =
      foreign "Hacl_K256_Field_fsub"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @-> (uint64_t @-> (returning void)))))
    let hacl_K256_Field_fmul =
      foreign "Hacl_K256_Field_fmul"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_K256_Field_fsqr =
      foreign "Hacl_K256_Field_fsqr"
        ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void)))
    let hacl_K256_Field_fnormalize_weak =
      foreign "Hacl_K256_Field_fnormalize_weak"
        ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void)))
    let hacl_K256_Field_fnormalize =
      foreign "Hacl_K256_Field_fnormalize"
        ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void)))
    let hacl_K256_Field_fnegate_conditional_vartime =
      foreign "Hacl_K256_Field_fnegate_conditional_vartime"
        ((ptr uint64_t) @-> (bool @-> (returning void)))
    let hacl_Impl_K256_Finv_fsquare_times_in_place =
      foreign "Hacl_Impl_K256_Finv_fsquare_times_in_place"
        ((ptr uint64_t) @-> (uint32_t @-> (returning void)))
    let hacl_Impl_K256_Finv_fsquare_times =
      foreign "Hacl_Impl_K256_Finv_fsquare_times"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @-> (uint32_t @-> (returning void))))
    let hacl_Impl_K256_Finv_fexp_223_23 =
      foreign "Hacl_Impl_K256_Finv_fexp_223_23"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_Impl_K256_Finv_finv =
      foreign "Hacl_Impl_K256_Finv_finv"
        ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void)))
    let hacl_Impl_K256_Finv_fsqrt =
      foreign "Hacl_Impl_K256_Finv_fsqrt"
        ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void)))
  end