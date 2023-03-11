open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Hash_Blake2s_32_init =
      foreign "Hacl_Hash_Blake2s_32_init"
        ((ptr uint32_t) @-> (uint32_t @-> (uint32_t @-> (returning void))))
    let hacl_Hash_Blake2s_32_update_key =
      foreign "Hacl_Hash_Blake2s_32_update_key"
        ((ptr uint32_t) @->
           ((ptr uint32_t) @->
              (uint32_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))))
    let hacl_Hash_Blake2s_32_update_multi =
      foreign "Hacl_Hash_Blake2s_32_update_multi"
        (uint32_t @->
           ((ptr uint32_t) @->
              ((ptr uint32_t) @->
                 (uint64_t @->
                    (ocaml_bytes @-> (uint32_t @-> (returning void)))))))
    let hacl_Hash_Blake2s_32_update_last =
      foreign "Hacl_Hash_Blake2s_32_update_last"
        (uint32_t @->
           ((ptr uint32_t) @->
              ((ptr uint32_t) @->
                 (uint64_t @->
                    (uint32_t @-> (ocaml_bytes @-> (returning void)))))))
    let hacl_Hash_Blake2s_32_finish =
      foreign "Hacl_Hash_Blake2s_32_finish"
        (uint32_t @-> (ocaml_bytes @-> ((ptr uint32_t) @-> (returning void))))
    let hacl_Hash_Blake2s_32_hash_with_key =
      foreign "Hacl_Hash_Blake2s_32_hash_with_key"
        (ocaml_bytes @->
           (uint32_t @->
              (ocaml_bytes @->
                 (uint32_t @->
                    (ocaml_bytes @-> (uint32_t @-> (returning void)))))))
    let hacl_Hash_Blake2s_32_malloc_with_key =
      foreign "Hacl_Hash_Blake2s_32_malloc_with_key"
        (void @-> (returning (ptr uint32_t)))
    type hacl_Hash_Blake2s_32_block_state_t =
      [ `hacl_Hash_Blake2s_32_block_state_t ] structure
    let (hacl_Hash_Blake2s_32_block_state_t :
      [ `hacl_Hash_Blake2s_32_block_state_t ] structure typ) =
      structure "Hacl_Hash_Blake2s_32_block_state_t_s"
    let hacl_Hash_Blake2s_32_block_state_t_fst =
      field hacl_Hash_Blake2s_32_block_state_t "fst" (ptr uint32_t)
    let hacl_Hash_Blake2s_32_block_state_t_snd =
      field hacl_Hash_Blake2s_32_block_state_t "snd" (ptr uint32_t)
    let _ = seal hacl_Hash_Blake2s_32_block_state_t
    type hacl_Hash_Blake2s_32_state_t =
      [ `hacl_Hash_Blake2s_32_state_t ] structure
    let (hacl_Hash_Blake2s_32_state_t :
      [ `hacl_Hash_Blake2s_32_state_t ] structure typ) =
      structure "Hacl_Hash_Blake2s_32_state_t_s"
    let hacl_Hash_Blake2s_32_state_t_block_state =
      field hacl_Hash_Blake2s_32_state_t "block_state"
        hacl_Hash_Blake2s_32_block_state_t
    let hacl_Hash_Blake2s_32_state_t_buf =
      field hacl_Hash_Blake2s_32_state_t "buf" (ptr uint8_t)
    let hacl_Hash_Blake2s_32_state_t_total_len =
      field hacl_Hash_Blake2s_32_state_t "total_len" uint64_t
    let _ = seal hacl_Hash_Blake2s_32_state_t
    let hacl_Hash_Blake2s_32_malloc =
      foreign "Hacl_Hash_Blake2s_32_malloc"
        (void @-> (returning (ptr hacl_Hash_Blake2s_32_state_t)))
    let hacl_Hash_Blake2s_32_reset =
      foreign "Hacl_Hash_Blake2s_32_reset"
        ((ptr hacl_Hash_Blake2s_32_state_t) @-> (returning void))
    let hacl_Hash_Blake2s_32_update =
      foreign "Hacl_Hash_Blake2s_32_update"
        ((ptr hacl_Hash_Blake2s_32_state_t) @->
           (ocaml_bytes @-> (uint32_t @-> (returning uint32_t))))
    let hacl_Hash_Blake2s_32_digest =
      foreign "Hacl_Hash_Blake2s_32_digest"
        ((ptr hacl_Hash_Blake2s_32_state_t) @->
           (ocaml_bytes @-> (returning void)))
    let hacl_Hash_Blake2s_32_free =
      foreign "Hacl_Hash_Blake2s_32_free"
        ((ptr hacl_Hash_Blake2s_32_state_t) @-> (returning void))
  end