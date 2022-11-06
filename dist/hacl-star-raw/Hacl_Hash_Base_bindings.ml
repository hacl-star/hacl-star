open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    module Hacl_Spec_applied = (Hacl_Spec_bindings.Bindings)(Hacl_Spec_stubs)
    open Hacl_Spec_applied
    let hacl_Hash_Definitions_word_len =
      foreign "Hacl_Hash_Definitions_word_len"
        (spec_Hash_Definitions_hash_alg @-> (returning uint32_t))
    let hacl_Hash_Definitions_block_len =
      foreign "Hacl_Hash_Definitions_block_len"
        (spec_Hash_Definitions_hash_alg @-> (returning uint32_t))
    let hacl_Hash_Definitions_hash_word_len =
      foreign "Hacl_Hash_Definitions_hash_word_len"
        (spec_Hash_Definitions_hash_alg @-> (returning uint32_t))
    let hacl_Hash_Definitions_hash_len =
      foreign "Hacl_Hash_Definitions_hash_len"
        (spec_Hash_Definitions_hash_alg @-> (returning uint32_t))
  end