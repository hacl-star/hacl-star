open Bytes

module Lib_RandomSequence = struct
  external write : Bytes.t -> unit =
    "ml_randombytes" [@@noalloc]

  let gen len =
    let buf = Bytes.create len in
    write buf ;
    buf
end
