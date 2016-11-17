module SocketIO

open FStar.HyperHeap
open FStar.HyperStack
open FStar.Buffer
open FStar.UInt8
open Hacl.Constants

open FileIO.Types
open PaddedFileIO

module U64 = FStar.UInt64
module H64 = Hacl.UInt64
module HS = FStar.HyperStack
module HH = FStar.HyperHeap


(* The region in which sockets live *)
assume val socket_rgn: r:rid{is_eternal_region r /\ file_rgn <> r}
type socket_ref = sb:buffer socket{length sb = 1 /\ socket_rgn = (frameOf sb)}

(* The socket state only depends on the socket region *)
assume val current_state_: FStar.Heap.heap -> socket -> GTot socket_state
val current_state: FStar.HyperStack.mem -> socket -> GTot socket_state
let current_state h s = current_state_ (Map.sel h.h socket_rgn) s


assume val tcp_connect:
  host: uint8_p ->
  port:u32 ->
  s:socket_ref ->
  ST sresult
    (requires (fun h -> live h host /\ live h s))
    (ensures  (fun h0 r h1 ->
      HS.modifies (Set.singleton socket_rgn) h0 h1
      /\ modifies_buf_1 socket_rgn s h0 h1 (* When connecting the socket reference was modified *)
      /\ live h1 s /\ live h1 host
      /\ (match r with | SocketOk -> let sh = get h1 s 0 in current_state h1 sh = Open
                      | _ -> True)))

assume val tcp_listen: port:u32 -> s:socket_ref -> ST sresult
    (requires (fun h -> live h s))
    (ensures  (fun h0 r h1 ->
      HS.modifies (Set.singleton socket_rgn) h0 h1
      /\ modifies_buf_1 socket_rgn s h0 h1 (* When connecting the socket reference was modified *)
      /\ live h1 s
      /\ (match r with | SocketOk -> let sh = get h1 s 0 in current_state h1 sh = Open
                      | _ -> True)))


assume val tcp_accept: l:socket_ref -> s:socket_ref{disjoint l s} -> ST sresult
    (requires (fun h -> live h s /\ live h l /\ current_state h (get h l 0) = Open))
    (ensures  (fun h0 r h1 -> live h1 s /\ live h1 l
      /\ HS.modifies (Set.singleton socket_rgn) h0 h1
      /\ modifies_buf_1 socket_rgn s h0 h1
      /\ (match r with | SocketOk -> (let sh = get h1 s 0 in current_state h1 sh = Open
                                     /\ current_state h1 (get h1 l 0) = Open)
                      | _ -> True)))


assume val tcp_write_all: s:socket_ref ->
  b:uint8_p ->
  len:u64{U64.v len <= length b} ->
  Stack sresult
    (requires (fun h0 -> live h0 s /\ live h0 b /\ current_state h0 (get h0 s 0) = Open))
    (ensures  (fun h0 r h1 -> live h1 s /\ live h1 b
      /\ h0 == h1 // JK: assuming that nothing changes for simplicity
      (* /\ HS.modifies (Set.singleton socket_rgn) h0 h1 *)
      (* /\ HS.modifies_ref socket_rgn !{} h0 h1 *)
      /\ (r = SocketOk ==> current_state h1 (get h1 s 0) = Open)))


assume val tcp_read_all:
  s:socket_ref ->
  b:buffer u8{frameOf b <> socket_rgn} ->
  len:u64{length b >= U64.v len} ->
  Stack sresult
    (requires (fun h0 -> live h0 s /\ live h0 b /\ current_state h0 (get h0 s 0) = Open))
    (ensures  (fun h0 r h1 -> live h1 s /\ live h1 b /\ modifies_1 b h0 h1
      /\ (r = SocketOk ==> current_state h1 (get h1 s 0) = Open)))


assume val tcp_close: s:socket_ref -> ST sresult
    (requires (fun h0 -> live h0 s (* /\ current_state h0 (get h0 s 0) = Open *)))
    (ensures  (fun h0 r h1 -> live h1 s
      /\ HS.modifies (Set.singleton socket_rgn) h0 h1
      /\ modifies_buf_1 socket_rgn s h0 h1
      /\ (r = SocketOk ==> current_state h1 (get h1 s 0) = Closed)))
