module Spec.MD5

let init = Seq.create 4 0ul

let update h _ = init

let pad l =
  let l = 64 - l % 64 in
  Seq.create l 0uy

let finish _ =
  Seq.create 16 0uy

let test () =
  true
