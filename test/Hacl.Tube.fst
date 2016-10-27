module Hacl.Tube


open FStar.Seq
open FStar.Buffer
open SecureFileIO
open SocketIO
open Hacl.Constants

type clock = u64
type string = seq u8


type streamID = {
     id: u64;
     ts: u64;
     pkA: seq u8;
     pkB: seq u8
}

     
type event : Type0 = 
    | Sent: sid:streamID -> header:file_stat -> content: seq u8 -> event

assume val happened: FStar.HyperStack.mem -> event -> GTot bool
assume val log: e:event -> Stack unit
    (requires (fun _ -> True))
    (ensures  (fun h0 s h1 -> happened h1 e))

assume val file_send: file:string -> roundup:u64 ->
       host:string -> port:u32 -> 
       skA:buffer u8 -> pkA:buffer u8 -> pkB:buffer u8 ->
           Stack (fresult * file_stat * streamID)
	   (requires (fun _ -> True))
	   (ensures  (fun h0 s h1 -> match s with 
      	   	                   | FileOk,fs,sid ->
				     sid.pkA = as_seq h0 pkA /\	sid.pkB = as_seq h0 pkB /\
				     file_content h0 fs = file_content h1 fs /\	
				     happened h1 (Sent sid fs (as_seq h0 (file_content h0 fs)))
				   | _ -> true))

assume val file_recv: port:u32 -> pkA:buffer u8 -> skB:buffer u8 -> pkB:buffer u8 -> Stack (fresult * file_stat * streamID)
       	   (requires (fun _ -> True))
	   (ensures  (fun h0 s h1 -> match s with 
      	   	                   | FileOk,fs,sid ->
				     sid.pkA = as_seq h0 pkA /\	sid.pkB = as_seq h0 pkB /\
				     happened h0 (Sent sid fs (as_seq h1 (file_content h1 fs)))
				   | _ -> true))


