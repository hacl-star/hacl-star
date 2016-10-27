module SecureFileIO

open FStar.Seq
open FStar.Buffer
open Hacl.Cast
open Hacl.Constants
open Hacl.UInt64

(* Need to get rid of these  following ones *)
type string = seq u8
val zero: u64
val sub: buffer u8 -> u64 -> u64 -> Tot (buffer u8)
val v: u64 -> Tot nat
(* The above need to come from some library module *)

type file_stat: Type0 = {
     name: uint8_p;
     mtime: h64;
     size: h64;	
     padded_size: u64
}

val file_descriptor: Type0

type fd_state = 
     | FileOpen: fd_state
     | FileClosed: fd_state

type file_handle: Type0 =  {
     stat:   file_stat;
     fd:     file_descriptor
}

val file_state: FStar.HyperStack.mem -> file_handle -> GTot fd_state
val file_offset: FStar.HyperStack.mem -> file_handle -> GTot u64
val file_content: FStar.HyperStack.mem -> file_stat -> GTot (buffer u8)

let file_sub (m:FStar.HyperStack.mem) (f:file_handle) (i:u64) (j:u64) =	
    sub (file_content m f.stat) i j
    
type fresult : Type0 = 
     | FileOk    : fresult
     | FileError : fresult


val file_open_read_sequential: n:uint8_p -> roundup:u64 -> fb:buffer file_handle -> Stack fresult
    (requires (fun h -> length fb = 1 /\ live h fb))
    (ensures  (fun h0 s h1 -> match s with 
	      	       	    | FileOk -> 
			      live h1 fb /\
			      (let fh = get h1 fb 0 in
    	      	     	       file_state h1 fh = FileOpen /\	
			       file_offset h1 fh = zero /\	
			       file_content h0 fh.stat = file_content h1 fh.stat)
			    | _ -> true))

val file_next_sequential: f:file_handle -> len:u64 -> Stack uint8_p
    (requires (fun h0 -> let j = file_offset h0 f +^ len in
    	      	      	 file_state h0 f = FileOpen /\ 
    	      	      	 v j <= v f.stat.padded_size))
    (ensures  (fun h0 s h1 -> let i = file_offset h0 f in
    	      	      	      let j = file_offset h0 f +^ len in
    	      	      	      file_state h1 f = FileOpen /\ 
    	      	      	      file_offset h1 f = j /\
			      file_content h0 f.stat = file_content h1 f.stat /\
			      ((v i <= v f.stat.size /\ v j <= v f.stat.size) ==> s = file_sub h1 f i len) /\
			      ((v i <= v f.stat.size /\ v j > v f.stat.size) ==>  sub s zero (f.stat.size -^ i) = file_sub h1 f i (f.stat.size -^ i))))
			      

val file_open_write_sequential: file_stat -> fb:buffer file_handle -> Stack fresult
    (requires (fun h -> length fb = 1 /\ live h fb))
    (ensures  (fun h0 s h1 -> match s with 
    	      	      	    | FileOk -> 
			      live h1 fb /\
			      (let fh = get h1 fb 0 in
    	      	      	       file_state h1 fh = FileOpen /\ 
			       file_offset h1 fh = zero /\
			       file_content h0 fh.stat = file_content h1 fh.stat)
			    | _ -> true))

val file_close: f:file_handle -> Stack bool
    (requires (fun h0 -> file_state h0 f = FileOpen))
    (ensures  (fun h0 r h1 -> r ==> (file_state h1 f = FileClosed /\
    			      	     file_content h0 f.stat = file_content h1 f.stat)))

