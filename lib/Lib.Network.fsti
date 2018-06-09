module Lib.Network

open FStar.Error
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

new val networkStream: eqtype u#0
new val tcpListener: Type0

val set_nonblock: networkStream -> unit
val clear_nonblock: networkStream -> unit

type ioerror_t = string

(* Server side *)
val listen: s:string -> i:size_nat -> Tot (optResult ioerror_t tcpListener)
val acceptTimeout: size_nat -> tcpListener -> Tot (optResult ioerror_t networkStream)
val accept: tcpListener -> Tot (optResult ioerror_t networkStream)
val stop: tcpListener -> Tot (optResult ioerror_t unit)

(* Client side *)

val connectTimeout: nat -> string -> nat -> Tot (optResult ioerror_t networkStream)
val connect: string -> nat -> Tot (optResult ioerror_t networkStream)

(* Input/Output *)

// adding support for (potentially) non-blocking I/O
// NB for now, send *fails* on partial writes, and *loops* on EAGAIN/EWOULDBLOCK.

// noeq type recv_result (len:size_nat) (max:size_nat{len <= max}) =
//   | RecvWouldBlock
//   | RecvError of string
//   | Received of (lbytes len)

//val recv_async: networkStream -> max:size_nat -> Tot (optResult ioerror_t (len:size_nat{len <= max} & b:recv_result len max))
val recv: networkStream -> max:size_nat -> Tot (optResult ioerror_t (len:size_nat{len <= max} * b:(lbytes max)))
val send: networkStream -> len:size_nat -> b:lbytes len -> Tot (optResult ioerror_t unit)
val close: networkStream -> Tot unit

