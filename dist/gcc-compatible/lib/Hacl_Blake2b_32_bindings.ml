open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    type t_K___uint32_t_uint32_t = [ `t_K___uint32_t_uint32_t ] structure
    let (t_K___uint32_t_uint32_t :
      [ `t_K___uint32_t_uint32_t ] structure typ) =
      structure "K___uint32_t_uint32_t_s" 
    let t_K___uint32_t_uint32_t_fst =
      field t_K___uint32_t_uint32_t "fst" uint32_t 
    let t_K___uint32_t_uint32_t_snd =
      field t_K___uint32_t_uint32_t "snd" uint32_t 
    let _ = seal t_K___uint32_t_uint32_t 
    let hacl_Blake2b_32_blake2b =
      foreign "Hacl_Blake2b_32_blake2b"
        (uint32_t @->
           ((ptr uint8_t) @->
              (uint32_t @->
                 ((ptr uint8_t) @->
                    (uint32_t @-> ((ptr uint8_t) @-> (returning void)))))))
      
  end