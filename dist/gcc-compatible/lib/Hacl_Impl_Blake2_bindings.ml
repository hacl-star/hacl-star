open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    type hacl_Impl_Blake2_Core_m_spec = Unsigned.UInt8.t
    let hacl_Impl_Blake2_Core_m_spec =
      typedef uint8_t "Hacl_Impl_Blake2_Core_m_spec"
    let hacl_Impl_Blake2_Core_m_spec_Hacl_Impl_Blake2_Core_M32 =
      Unsigned.UInt8.of_int 0
    let hacl_Impl_Blake2_Core_m_spec_Hacl_Impl_Blake2_Core_M128 =
      Unsigned.UInt8.of_int 1
    let hacl_Impl_Blake2_Core_m_spec_Hacl_Impl_Blake2_Core_M256 =
      Unsigned.UInt8.of_int 2
  end