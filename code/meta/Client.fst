module Client

/// This is a client written against the interface.

module I = Interface

let times_two (x: int) =
  I.add x x

let times_four (x: int) =
  times_two (times_two x)

let times_four' (x: int) =
  I.mul 4 x

let times_sixteen (x: int) =
  times_four (times_four x)

let times_sixteen' (x: int) =
  times_four (times_four' x)
