module SocketIO

open FStar.Buffer
open FStar.UInt8
open Hacl.Constants

open FileIO.Types
open PaddedFileIO

assume val current_state: FStar.HyperStack.mem -> socket -> GTot socket_state

assume val tcp_connect: host: uint8_p -> port:u32 -> s:buffer socket -> Stack sresult
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
assume val tcp_accept: l:buffer socket -> s:buffer socket -> Stack sresult
    (requires (fun h0 -> current_state h0 (get h0 l 0) = Open))
    (ensures  (fun h0 r h1 -> match r with 
    	      	              | SocketOk -> 
			      	let sh = get h1 s 0 in
				current_state h1 sh = Open))

assume val tcp_write_all: s:buffer socket -> uint8_p -> len:u64 -> Stack sresult
    (requires (fun h0 -> current_state h0 (get h0 s 0) = Open))
    (ensures  (fun _ r h1 -> r = SocketOk ==> current_state h1 (get h1 s 0) = Open))

assume val tcp_read_all: s:buffer socket -> buffer u8 -> len:u64 -> Stack sresult
    (requires (fun h0 -> current_state h0 (get h0 s 0) = Open))
    (ensures  (fun _ r h1 -> r = SocketOk ==> current_state h1 (get h1 s 0) = Open))

assume val tcp_close: s:buffer socket -> Stack sresult
    (requires (fun h0 -> current_state h0 (get h0 s 0) = Open))
    (ensures  (fun _ r h1 -> r = SocketOk ==> current_state h1 (get h1 s 0) = Closed))
