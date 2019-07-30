module Lib.Network

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

type protocol =
  | UDP
  | TCP

val stream: #p:protocol -> eqtype
val listener: #p:protocol -> eqtype

(* Server side *)
val listen: #p:protocol -> s:string -> port:size_nat -> Tot (option (listener #p))
val acceptTimeout: #p:protocol -> size_nat -> listener #p -> Tot (option (stream #p))
val accept: #p:protocol -> listener #p -> Tot (option (stream #p))
val stop: #p:protocol -> listener #p -> Tot bool

(* Client side *)
val connectTimeout: #p:protocol -> timeout:nat -> string -> port:nat -> Tot (option (stream #p))
val connect: #p:protocol -> string -> port:nat -> Tot (option (stream #p))

(* Input/Output *)
val recv: #p:protocol -> stream #p -> max:size_nat -> Tot (option (len:size_nat{len <= max} & b:(lbytes max)))
val send: #p:protocol -> stream #p -> len:size_nat -> b:lbytes len -> Tot bool
val send_retry: #p:protocol -> stream #p -> retries:nat -> len:size_nat -> b:lbytes len -> Tot bool
val close: #p:protocol -> stream #p -> Tot bool
