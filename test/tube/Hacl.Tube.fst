module Hacl.Tube


open FStar.Seq
open FStar.Buffer
open PaddedFileIO
open SocketIO
open Hacl.Constants

type clock = u64
type string = seq u8


type streamID = {
     id: u64;
     ts: u64;
}

type principals = {
     pkA: seq u8;
     pkB: seq u8
}


assume val sent: FStar.HyperStack.mem -> principals -> streamID -> file_stat -> (seq u8) -> GTot bool

assume val file_send: file:string -> roundup:u64 ->
       host:string -> port:u32 -> 
       skA:buffer u8 -> pkA:buffer u8 -> pkB:buffer u8 ->
           Stack (fresult * file_stat * streamID)
	   (requires (fun _ -> True))
	   (ensures  (fun h0 s h1 -> match s with 
      	   	                   | FileOk,fs,sid ->
				     let prins = {pkA = as_seq h0 pkA; pkB = as_seq h0 pkB} in
				     file_content h0 fs = file_content h1 fs /\	
				     sent h1 prins sid fs (file_content h0 fs)
				   | _ -> true))

assume val file_recv: port:u32 -> pkA:buffer u8 -> skB:buffer u8 -> pkB:buffer u8 -> Stack (fresult * file_stat * streamID)
       	   (requires (fun _ -> True))
	   (ensures  (fun h0 s h1 -> match s with 
      	   	                   | FileOk,fs,sid ->
				     let prins = {pkA = as_seq h0 pkA; pkB = as_seq h0 pkB} in
				     sent h0 prins sid fs (file_content h1 fs)
				   | _ -> true))



val main: unit -> ST FStar.Int32.t
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> True))
let main () =
  C.exit_success
