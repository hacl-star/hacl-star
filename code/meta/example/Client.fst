module Client

/// This is a client written against the interface.

module I = Interface

[@ MetaAttribute.inline_ ]
let times_two #w (x: I.word w) =
  I.add x x

[@ MetaAttribute.specialize ]
let times_four #w (x: I.word w) =
  times_two (times_two x)

[@ MetaAttribute.inline_ ]
let four #w: I.word w = if w = I.W32 then 4ul else 4UL

[@ MetaAttribute.inline_ ]
let times_four' #w (x: I.word w) =
  I.mul four x

[@ MetaAttribute.specialize ]
let times_sixteen #w (x: I.word w) =
  times_four (times_four x)

[@ MetaAttribute.specialize ]
let times_sixteen' #w (x: I.word w) =
  times_four (times_four' x)
