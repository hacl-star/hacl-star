module Client

/// This is a client written against the interface.

module I = Interface

[@ Meta.Attribute.inline_ ]
let times_two #w (x: I.word w) =
  I.add x x

[@ Meta.Attribute.specialize ]
let times_four #w (x: I.word w) =
  times_two (times_two x)

[@ Meta.Attribute.inline_ ]
let four #w: I.word w = if w = I.W32 then 4ul else 4UL

[@ Meta.Attribute.inline_ ]
let times_four' #w (x: I.word w) =
  I.mul four x

[@ Meta.Attribute.specialize ]
let times_sixteen #w (x: I.word w) =
  times_four (times_four x)

[@ Meta.Attribute.specialize ]
let times_sixteen' #w (x: I.word w) =
  times_four (times_four' x)


/// Second example

[@ Meta.Attribute.specialize ]
let rec lookup (l: I.a_list) (k: I.key): option I.value =
  match l with
  | [] -> None
  | (k', v)::xs ->
      if I.key_eq k k' then
        Some v
      else
        lookup xs k
