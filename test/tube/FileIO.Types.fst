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

type file_stat: Type0 = {
     name: uint8_p;
     mtime: h64;
     size: h64;	
}

type fd_state = 
     | FileOpen: fd_state
     | FileClosed: fd_state

type file_descriptor = FStar.Int32.t // Assuming that is the default C "int"

type file_handle =  {
     stat:   file_stat;
     fd:     file_descriptor
}

type fresult : Type0 = 
     | FileOk    : fresult
     | FileError : fresult

type socket = FStar.Int32.t

type socket_state = 
     | Open: socket_state
     | Closed: socket_state
     | Error: socket_state

type sresult = 
     | SocketOk: sresult
     | SocketError: sresult
