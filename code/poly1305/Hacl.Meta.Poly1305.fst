module Hacl.Meta.Poly1305

friend Hacl.Impl.Poly1305

#set-options "--z3rlimit 250 --max_fuel 0 --max_ifuel 0"



%splice[
  poly1305_poly1305_mac_higher
] (Meta.Interface.specialize (`Hacl.Impl.Poly1305.Fields.field_spec) [
    `Hacl.Impl.Poly1305.poly1305_mac

])
