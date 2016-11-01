module PaddedFileIO

open FStar.Seq
open FStar.Buffer
open Hacl.Cast
open Hacl.Constants
open Hacl.UInt64
open FileIO.Types

module U64 = FStar.UInt64
module H64 =  Hacl.UInt64
module B   = FStar.Buffer

(* Need to get rid of these  following ones *)
type string = seq u8
val zero: u64
(* The above need to come from some library module *)

(* File System Buffer Size, currently 256KB *)
val max_block_size: u64

val init_file_handle: file_handle


val file_state: FStar.HyperStack.mem -> file_handle -> GTot fd_state
val file_offset: FStar.HyperStack.mem -> file_handle -> GTot u64
val file_buffer: FStar.HyperStack.mem -> file_stat -> GTot (buffer h8)
val file_content: FStar.HyperStack.mem -> file_stat -> GTot (seq h8)

let file_sub (m:FStar.HyperStack.mem) (f:file_handle) (i:u64) (j:u64) =	
    B.sub (file_buffer m f.stat) (Int.Cast.uint64_to_uint32 i) (Int.Cast.uint64_to_uint32 j)
    

(* TODO: check the live/modifies clauses below *)
val file_open_read_sequential: n:uint8_p -> fb:buffer file_handle -> Stack fresult
    (requires (fun h -> length fb = 1 /\ live h fb))
    (ensures  (fun h0 s h1 -> match s with 
	      	       	    | FileOk -> 
			      live h1 fb /\
			      modifies_1 fb h0 h1 /\
			      (let fh = get h1 fb 0 in
    	      	     	       file_state h1 fh = FileOpen /\	
			       file_offset h1 fh = zero /\	
			       file_content h0 fh.stat = file_content h1 fh.stat)
			    | _ -> true))


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

val file_next_read_buffer: fb:buffer file_handle -> len:u64 -> Stack uint8_p
    (requires (fun h0 -> U64.v len <= U64.v max_block_size /\
    	      	         length fb = 1 /\ live h0 fb /\
    	      	         (let f = get h0 fb 0 in
			  file_state h0 f = FileOpen)))
    (ensures  (fun h0 s h1 -> let f = get h1 fb 0 in
    	      	              let i = file_offset h0 f in
    	      	      	      let j = U64 (file_offset h0 f +^ len) in
			      modifies_1 s h0 h1 /\
    	      	      	      file_state h1 f = FileOpen /\ 
    	      	      	      file_offset h1 f = j /\
			      file_content h0 f.stat = file_content h1 f.stat /\
			      ((U64.v i <= H64.v f.stat.size /\ U64.v j <= H64.v f.stat.size) ==> s = file_sub h1 f i len)(*  /\ *)
			      (* ((U64.v i <= v f.stat.size /\ U64.v j > v f.stat.size) ==>  B.sub s 0ul (Int.Cast.uint64_to_uint32 ((f.stat.size -^ i))) = file_sub h1 f i (f.stat.size -^ i)) *)
                              ))
			      

val file_next_write_buffer: fb:buffer file_handle -> len:u64 -> Stack uint8_p
    (requires (fun h0 -> U64.v len <= U64.v max_block_size /\
    	      	         length fb = 1 /\ live h0 fb /\
    	      	         (let f = get h0 fb 0 in
			  file_state h0 f = FileOpen)))
    (ensures  (fun h0 s h1 -> let f = get h1 fb 0 in
    	      	              let i = file_offset h0 f in
    	      	      	      let j = U64 (file_offset h0 f +^ len) in
			      modifies_1 s h0 h1 /\
    	      	      	      file_state h1 f = FileOpen /\ 
    	      	      	      file_offset h1 f = j /\
			      file_content h0 f.stat = file_content h1 f.stat /\
			      ((U64.v i <= v f.stat.size /\ U64.v j <= v f.stat.size) ==> s = file_sub h1 f i len)(*  /\ *)
			      (* ((U64.v i <= v f.stat.size /\ U64.v j > v f.stat.size) ==>  sub s zero (f.stat.size -^ i) = file_sub h1 f i (f.stat.size -^ i)) *)
                              ))
			      

val file_close: fb:buffer file_handle -> Stack bool
    (requires (fun h0 -> length fb = 1 /\ live h0 fb /\
                         (let f = get h0 fb 0 in
			  file_state h0 f = FileOpen)))
    (ensures  (fun h0 r h1 -> r ==> 
                         (let f = get h1 fb 0 in
       	      	      	  file_state h1 f = FileClosed /\
    			  file_content h0 f.stat = file_content h1 f.stat)))
