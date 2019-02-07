module Lib.Network

open FStar.Error
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

new val networkStream: eqtype
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


(* type protocol = *)
(*   | UDP *)
(*   | TCP *)

(* new val stream: #p:protocol -> eqtype *)
(* new val listener: #p:protocol -> eqtype *)

(* (\* Server side *\) *)
(* val listen: #p:protocol -> s:string -> port:size_nat -> Tot (option (listener #p)) *)
(* val acceptTimeout: #p:protocol -> size_nat -> listener #p -> Tot (option (stream #p)) *)
(* val accept: #p:protocol -> listener #p -> Tot (option (stream #p)) *)
(* val stop: #p:protocol -> listener #p -> Tot bool *)

(* (\* Client side *\) *)
(* val connectTimeout: #p:protocol -> timeout:nat -> string -> port:nat -> Tot (option (stream #p)) *)
(* val connect: #p:protocol -> string -> port:nat -> Tot (option (stream #p)) *)

(* (\* Input/Output *\) *)
(* val recv: #p:protocol -> stream #p -> max:size_nat -> Tot (option (len:size_nat{len <= max} & b:(lbytes max))) *)
(* val send: #p:protocol -> stream #p -> len:size_nat -> b:lbytes len -> Tot bool *)
(* val send_retry: #p:protocol -> stream #p -> retries:nat -> len:size_nat -> b:lbytes len -> Tot bool *)
(* val close: #p:protocol -> stream #p -> Tot bool *)

