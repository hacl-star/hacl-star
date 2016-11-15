module SocketIO

open FStar.Buffer
open FStar.UInt8
open Hacl.Constants

open FileIO.Types
open PaddedFileIO

module U64 = FStar.UInt64
module H64 = Hacl.UInt64

assume val current_state: FStar.HyperStack.mem -> socket -> GTot socket_state

assume val tcp_connect: host: uint8_p ->
  port:u32 ->
  s:buffer socket{length s = 1 /\ disjoint host s} ->
  Stack sresult
    (requires (fun h -> live h host /\ live h s))
    (ensures  (fun h0 r h1 -> modifies_1 s h0 h1 /\ live h1 s /\ live h0 host /\ (match r with
    	      	              | SocketOk ->
			      	let sh = get h1 s 0 in
				current_state h1 sh = Open
                               | _ -> True)))

assume val tcp_listen: port:u32 -> s:buffer socket{length s = 1} -> Stack sresult
    (requires (fun h -> live h s))
    (ensures  (fun h0 r h1 -> live h1 s /\ modifies_1 s h0 h1
      /\ (match r with | SocketOk -> let sh = get h1 s 0 in current_state h1 sh = Open
                      | _ -> True)))

assume val tcp_accept: l:buffer socket{length l = 1} -> s:buffer socket{length s = 1} -> Stack sresult
    (requires (fun h -> live h s /\ live h l /\ current_state h (get h l 0) = Open))
    (ensures  (fun h0 r h1 -> live h1 s /\ modifies_1 s h0 h1
      /\ (match r with | SocketOk -> let sh = get h1 s 0 in current_state h1 sh = Open
                      | _ -> True)))

assume val tcp_write_all: s:buffer socket{length s = 1} ->
  b:uint8_p ->
  len:u64{U64.v len <= length b} ->
  Stack sresult
    (requires (fun h0 -> live h0 s /\ live h0 b /\ current_state h0 (get h0 s 0) = Open))
    (ensures  (fun h0 r h1 -> live h1 s /\ live h1 b /\ h0 == h1
      /\ (r = SocketOk ==> current_state h1 (get h1 s 0) = Open)))

assume val tcp_read_all: s:buffer socket{length s = 1} ->
  b:buffer u8 ->
  len:u64{length b >= U64.v len} ->
  Stack sresult
    (requires (fun h0 -> live h0 s /\ live h0 b /\ current_state h0 (get h0 s 0) = Open))
    (ensures  (fun h0 r h1 -> live h1 s /\ live h1 b /\ modifies_1 b h0 h1
      /\ (r = SocketOk ==> current_state h1 (get h1 s 0) = Open)))

assume val tcp_close: s:buffer socket{length s = 1} -> Stack sresult
    (requires (fun h0 -> live h0 s /\ current_state h0 (get h0 s 0) = Open))
    (ensures  (fun h0 r h1 -> live h1 s /\ h0 == h1
      /\ (r = SocketOk ==> current_state h1 (get h1 s 0) = Closed)))
