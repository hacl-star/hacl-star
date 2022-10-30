open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_IntTypes_Intrinsics_add_carry_u32 =
      foreign "Hacl_IntTypes_Intrinsics_add_carry_u32"
        (uint32_t @->
           (uint32_t @->
              (uint32_t @-> ((ptr uint32_t) @-> (returning uint32_t)))))
    let hacl_IntTypes_Intrinsics_sub_borrow_u32 =
      foreign "Hacl_IntTypes_Intrinsics_sub_borrow_u32"
        (uint32_t @->
           (uint32_t @->
              (uint32_t @-> ((ptr uint32_t) @-> (returning uint32_t)))))
    let hacl_IntTypes_Intrinsics_add_carry_u64 =
      foreign "Hacl_IntTypes_Intrinsics_add_carry_u64"
        (uint64_t @->
           (uint64_t @->
              (uint64_t @-> ((ptr uint64_t) @-> (returning uint64_t)))))
    let hacl_IntTypes_Intrinsics_sub_borrow_u64 =
      foreign "Hacl_IntTypes_Intrinsics_sub_borrow_u64"
        (uint64_t @->
           (uint64_t @->
              (uint64_t @-> ((ptr uint64_t) @-> (returning uint64_t)))))
  end