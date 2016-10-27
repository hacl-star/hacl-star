module SocketIO

open FStar.Buffer
open FStar.UInt8
open Hacl.Constants

type string = buffer u8
val socket: Type0

type socket_state = 
     | Open: socket_state
     | Closed: socket_state
     | Error: socket_state

val current_state: FStar.HyperStack.mem -> socket -> GTot socket_state

type sresult = 
     | SocketOk: socket -> sresult
     | SocketError: sresult

val tcp_connect: host: string -> port:u32 -> Stack sresult
    (requires (fun _ -> True))
    (ensures  (fun h0 s h1 -> match s with | SocketOk s -> current_state h1 s = Open))
val tcp_listen: port:u32 -> Stack sresult
    (requires (fun _ -> True))
    (ensures  (fun h0 s h1 -> match s with | SocketOk s -> current_state h1 s = Open))
val tcp_accept: l:socket -> Stack sresult
    (requires (fun h0 -> current_state h0 l = Open))
    (ensures  (fun h0 s h1 -> match s with | SocketOk s -> current_state h1 s = Open))

val tcp_write_all: s:socket -> string -> len:u64 -> Stack bool
    (requires (fun h0 -> current_state h0 s = Open))
    (ensures  (fun _ r h1 -> r ==> current_state h1 s = Open))

val tcp_read_all: s:socket -> buffer u8 -> len:u64 -> Stack bool
    (requires (fun h0 -> current_state h0 s = Open))
    (ensures  (fun _ r h1 -> r ==> current_state h1 s = Open))

val tcp_close: s:socket -> Stack bool
    (requires (fun h0 -> current_state h0 s = Open))
    (ensures  (fun _ r h1 -> r ==> current_state h1 s = Closed))

