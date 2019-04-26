module Hacl.Impl.Frodo.Params

open Lib.IntTypes
open Lib.Buffer

include Frodo.Params

inline_for_extraction noextract
let cshake_frodo = Hacl.SHA3.cshake256_frodo

inline_for_extraction noextract
let frodo_gen_matrix = Hacl.Impl.Frodo.Gen.frodo_gen_matrix_cshake
