module Hacl.Gf128

let ghash tag text len key = Hacl.Impl.Gf128.NI.ghash tag text len key
