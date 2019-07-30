module Lib.Result

type result 'a =
  | Success: v:'a -> result 'a
  | Error: string -> result 'a

let return (a:'a) : result 'a = Success a

let bind (a:result 'a) (f:'a -> result 'b) : result 'b =
  match a with
  | Error x -> Error x
  | Success x -> f x
