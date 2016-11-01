module SocketIO

open FStar.Buffer
open FStar.UInt8
open Hacl.Constants
open FileIO.Types

assume val current_state: FStar.HyperStack.mem -> socket -> GTot socket_state

assume val init_socket: socket
assume val tcp_connect: host: string -> port:u32 -> s:buffer socket -> Stack sresult
    (requires (fun _ -> True))
    (ensures  (fun h0 r h1 -> match r with 
    	      	              | SocketOk -> 
			      	let sh = get h1 s 0 in
				current_state h1 sh = Open))
assume val tcp_listen: port:u32 -> s:buffer socket -> Stack sresult
    (requires (fun _ -> True))
    (ensures  (fun h0 r h1 -> match r with 
    	      	              | SocketOk -> 
			      	let sh = get h1 s 0 in
				current_state h1 sh = Open))
assume val tcp_accept: l:socket -> s:buffer socket -> Stack sresult
    (requires (fun h0 -> current_state h0 l = Open))
    (ensures  (fun h0 r h1 -> match r with 
    	      	              | SocketOk -> 
			      	let sh = get h1 s 0 in
				current_state h1 sh = Open))

assume val tcp_write_all: s:socket -> string -> len:u64 -> Stack sresult
    (requires (fun h0 -> current_state h0 s = Open))
    (ensures  (fun _ r h1 -> r = SocketOk ==> current_state h1 s = Open))

assume val tcp_read_all: s:socket -> buffer u8 -> len:u64 -> Stack sresult
    (requires (fun h0 -> current_state h0 s = Open))
    (ensures  (fun _ r h1 -> r = SocketOk ==> current_state h1 s = Open))

assume val tcp_close: s:socket -> Stack sresult
    (requires (fun h0 -> current_state h0 s = Open))
    (ensures  (fun _ r h1 -> r = SocketOk ==> current_state h1 s = Closed))
