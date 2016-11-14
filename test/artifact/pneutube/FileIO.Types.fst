module FileIO.Types

open FStar.Seq
open FStar.Buffer
open Hacl.Cast
open Hacl.Constants
open Hacl.UInt64

module U64 = FStar.UInt64
module H64 =  Hacl.UInt64
module B   = FStar.Buffer

type string = uint8_p

noeq type file_stat: Type0 = {
     name: uint8_p;
     mtime: h64;
     size: x:h64{H64.v x < pow2 32};	
}

type fd_state = 
     | FileOpen: fd_state
     | FileClosed: fd_state


noeq type file_descriptor = {
  fd_fd:FStar.Int32.t;
  current:U64.t;
  mmap:uint8_p;
  last:uint8_p;
}

noeq type file_handle =  {
     stat:   file_stat;
     fd:     file_descriptor
}

type fresult : Type0 = 
     | FileOk    : fresult
     | FileError : fresult

noeq type socket = {
  socket_fd:FStar.Int32.t;
  sent_bytes:U64.t;
  received_bytes:U64.t;
}

type socket_state = 
     | Open: socket_state
     | Closed: socket_state
     | Error: socket_state

type sresult = 
     | SocketOk: sresult
     | SocketError: sresult

let init_file_handle (dummy_ptr:uint8_p) : Tot file_handle =
  let zero = Hacl.Cast.uint64_to_sint64 0uL in
  let fs = {name = dummy_ptr; mtime = zero; size = zero} in
  let fd = {fd_fd = 0l; current = 0uL; mmap = dummy_ptr; last = dummy_ptr} in
  {stat = fs; fd = fd}

let init_socket () : Tot socket =
  {socket_fd = 0l; sent_bytes = 0uL; received_bytes = 0uL}
