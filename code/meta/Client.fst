module Client

/// This is a client written against the interface.

module I = Interface

[@ MetaAttribute.inline_ ]
let times_two (x: int) =
  I.add x x

[@ MetaAttribute.specialize ]
let times_four (x: int) =
  times_two (times_two x)

[@ MetaAttribute.inline_ ]
let times_four' (x: int) =
  I.mul 4 x

[@ MetaAttribute.specialize ]
let times_sixteen (x: int) =
  times_four (times_four x)

[@ MetaAttribute.specialize ]
let times_sixteen' (x: int) =
  times_four (times_four' x)
