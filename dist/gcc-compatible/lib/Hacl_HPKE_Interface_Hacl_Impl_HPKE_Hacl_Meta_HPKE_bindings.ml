open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    type hacl_Impl_HPKE_context_s = [ `hacl_Impl_HPKE_context_s ] structure
    let (hacl_Impl_HPKE_context_s :
      [ `hacl_Impl_HPKE_context_s ] structure typ) =
      structure "Hacl_Impl_HPKE_context_s_s"
    let hacl_Impl_HPKE_context_s_ctx_key =
      field hacl_Impl_HPKE_context_s "ctx_key" (ptr uint8_t)
    let hacl_Impl_HPKE_context_s_ctx_nonce =
      field hacl_Impl_HPKE_context_s "ctx_nonce" (ptr uint8_t)
    let hacl_Impl_HPKE_context_s_ctx_seq =
      field hacl_Impl_HPKE_context_s "ctx_seq" (ptr uint64_t)
    let hacl_Impl_HPKE_context_s_ctx_exporter =
      field hacl_Impl_HPKE_context_s "ctx_exporter" (ptr uint8_t)
    let _ = seal hacl_Impl_HPKE_context_s
  end