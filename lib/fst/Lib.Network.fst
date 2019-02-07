module Lib.Network

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

(* Server side *)
let stream #p = magic()
let listener #p = magic()

let listen #p s port = magic()
let acceptTimeout #p tm l = magic()
let accept #p l = magic()
let stop #p l = magic()

(* Client side *)
let connectTimeout #p timeout s port = magic()
let connect #p s port = magic()

(* Input/Output *)
let recv #p s max = magic()
let send #p s len b = magic()
let send_retry #p s retries len b = magic()
let close #p s = magic()
