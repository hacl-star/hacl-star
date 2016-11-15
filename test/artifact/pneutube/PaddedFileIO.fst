module PaddedFileIO

open FStar.Seq
open FStar.HyperHeap
open FStar.HyperStack
open FStar.Buffer
open Hacl.Cast
open Hacl.Constants
open Hacl.UInt64

open FileIO.Types

module U32 = FStar.UInt32
module H32 =  Hacl.UInt32
module U64 = FStar.UInt64
module H64 =  Hacl.UInt64
module B   = FStar.Buffer
module HS  = FStar.HyperStack
module HH  = FStar.HyperHeap

assume val file_rgn: r:rid{is_eternal_region r}
type fh_ref = fb:buffer file_handle{length fb = 1 /\ frameOf fb = file_rgn}


#reset-options "--initial_fuel 0 --max_fuel 0"
private val lemma_max_uint8: n:nat -> Lemma
 (requires (n = 8))
 (ensures  (pow2 n = 256))
 [SMTPat (pow2 n)]
let lemma_max_uint8 n = assert_norm(pow2 8 = 256)
private val lemma_max_uint32: n:nat -> Lemma
 (requires (n = 32))
 (ensures  (pow2 n = 4294967296))
 [SMTPat (pow2 n)]
let lemma_max_uint32 n = assert_norm(pow2 32 = 4294967296)
private val lemma_max_uint64: n:nat -> Lemma
 (requires (n = 64))
 (ensures  (pow2 n = 18446744073709551616))
 [SMTPat (pow2 n)]
let lemma_max_uint64 n = assert_norm(pow2 64 = 18446744073709551616)

inline_for_extraction val zero: u64
inline_for_extraction let zero = 0uL

(* File System Buffer Size, currently 256KB *)
inline_for_extraction val max_block_size: u64
inline_for_extraction let max_block_size = 262144uL

type bufsize = x:U64.t{U64.v x < pow2 32}

private let bufsize_bound (x:bufsize) : Lemma (requires (True)) (ensures (U32.v (Int.Cast.uint64_to_uint32 x) = U64.v x)) [SMTPat (Int.Cast.uint64_to_uint32 x)] = Math.Lemmas.modulo_lemma (U64.v x) (pow2 32)


assume val file_state_: FStar.Heap.heap -> file_handle -> GTot fd_state
let file_state (h:mem) fh : GTot fd_state = file_state_ (Map.sel h.h file_rgn) fh
assume val file_offset_: FStar.Heap.heap -> file_handle -> GTot u64
let file_offset (h:mem) fh : GTot u64 = file_offset_ (Map.sel h.h file_rgn) fh
assume val file_buffer: file_stat -> GTot (buffer h8)

let file_sub (m:FStar.HyperStack.mem) (f:file_handle) (i:u64) (j:u64{U64.v j + U64.v i <= length (file_buffer f.stat)}) =
    B.sub (file_buffer f.stat) (Int.Cast.uint64_to_uint32 i) (Int.Cast.uint64_to_uint32 j)


(* A live file handle maps to a buffer which max_length is the size indicated in the file_stat *)
let live_fh h (fh:file_handle) : GTot Type0 =
  live h (file_buffer fh.stat)
  /\ max_length (file_buffer fh.stat) = H64.v fh.stat.size
  /\ length (file_buffer fh.stat) = H64.v fh.stat.size
  /\ U64.v (file_offset h fh) <= H64.v fh.stat.size

(* Type of a workable file *)
let live_file h (f:fh_ref) : GTot Type0 =
  live h f /\ (let fh = get h f 0 in live_fh h fh)

(* Files are not changed through reads/writes *)
let same_file h f h' f' : GTot Type0 =
  live_file h f /\ live_file h' f'
  /\ (let fh = get h f 0 in let fh' = get h' f' 0 in  fh.stat == fh'.stat)

val file_content: h:FStar.HyperStack.mem -> fs:file_stat{live h (file_buffer fs)}  -> GTot (seq h8)
let file_content m fs = as_seq m (file_buffer fs)


(* TODO: check the live/modifies clauses below *)
assume val file_open_read_sequential: n:uint8_p ->
  fb:fh_ref ->
  Stack fresult
    (requires (fun h -> live h fb /\ live h n))
    (ensures  (fun h0 s h1 -> (match s with
	      	       	    | FileOk ->
			      (* modifies_1 fb h0 h1 /\ *)
                              HS.modifies (Set.singleton file_rgn) h0 h1
                              /\ live_file h1 fb /\
			      (let fh = get h1 fb 0 in
    	      	     	       file_state h1 fh = FileOpen /\
			       file_offset h1 fh = zero /\
			       length (file_buffer fh.stat) = max_length (file_buffer fh.stat))
			       (* /\ file_content h0 fh.stat == file_content h1 fh.stat) *)
			    | _ -> true)))


assume val file_open_write_sequential: file_stat ->
  fb:fh_ref ->
  Stack fresult
    (requires (fun h -> live h fb))
    (ensures  (fun h0 s h1 -> match s with
    	      	      	    | FileOk ->
                              HS.modifies (Set.singleton file_rgn) h0 h1
			      /\ live_file h1 fb /\
			      (let fh = get h1 fb 0 in
    	      	      	       file_state h1 fh = FileOpen /\
			       file_offset h1 fh = zero /\
			       length (file_buffer fh.stat) = max_length (file_buffer fh.stat))
			       (* file_content h0 fh.stat == file_content h1 fh.stat) *)
			    | _ -> true))


private let sint64_to_uint64 (x:H64.t) : GTot U64.t = U64.uint_to_t (H64.v x)
private let sint64_to_uint32 (x:H64.t) : GTot U32.t = Int.Cast.uint64_to_uint32 (U64.uint_to_t (H64.v x))


(* assume val file_next_read_buffer: fb:buffer file_handle{length fb = 1} -> *)
(*   len:u64 -> *)
(*   Stack uint8_p *)
(*     (requires (fun h0 -> U64.v len <= U64.v max_block_size /\ *)
(*     	      	         length fb = 1 /\ live h0 fb /\ *)
(*     	      	         (let f = get h0 fb 0 in *)
(* 			  file_state h0 f = FileOpen))) *)
(*     (ensures  (fun h0 s h1 -> live h1 fb /\ let f = get h1 fb 0 in *)
(*     	      	              let i = (file_offset h0 f) in *)
(*     	      	      	      let j = Hacl.Cast.uint64_to_sint64 (U64 (file_offset h0 f +^ len)) in *)
(* 			      modifies_1 s h0 h1 /\ *)
(*     	      	      	      file_state h1 f = FileOpen /\ *)
(*     	      	      	      Hacl.Cast.uint64_to_sint64 (file_offset h1 f) == j /\ *)
(* 			      file_content h0 f.stat == file_content h1 f.stat /\ *)
(* 			      ((U64.v i <= H64.v f.stat.size /\ H64.v j <= H64.v f.stat.size) ==> s == file_sub h1 f i len) /\ *)
(* 			      ((U64.v i <= v f.stat.size /\ H64.v j > v f.stat.size) ==> (B.sub s 0ul (sint64_to_uint32 ((f.stat.size -^ Hacl.Cast.uint64_to_sint64 i))) == file_sub h1 f i (sint64_to_uint64 (f.stat.size -^ Hacl.Cast.uint64_to_sint64 i)))) *)
(*                               )) *)

let file_next_read_buffer_pre h (fb:fh_ref) (len:U64.t) : GTot Type0 =
  live_file h fb /\ U64.v len <= U64.v max_block_size
  /\ (let fh = get h fb 0 in file_state h fh = FileOpen)

let file_next_read_buffer_post h0 (s:uint8_p) h1 (fb:fh_ref{length fb = 1})
                               (len:bufsize) : GTot Type0 =
  file_next_read_buffer_pre h0 fb len
  /\ live_file h0 fb /\ live_file h1 fb /\ same_file h0 fb h1 fb
  /\ (let fh0 = get h0 fb 0 in let fh1 = get h1 fb 0 in
      let nlen = (file_offset h0 fh0) +^ len in
      U64.v (file_offset h1 fh1) = U64.v nlen
      /\ file_state h1 fh1 = FileOpen
      /\ (U64.v nlen <= H64.v fh0.stat.size ==> 
               s  == Buffer.sub (file_buffer fh0.stat) 
                                (Int.Cast.uint64_to_uint32 (file_offset h0 fh0)) 
   	                        (Int.Cast.uint64_to_uint32 len)) 
      /\ (U64.v nlen > H64.v fh0.stat.size ==> 
      	       as_seq h1 s ==
	       as_seq h0 (Buffer.sub (file_buffer fh0.stat) 
                                     (Int.Cast.uint64_to_uint32 (file_offset h0 fh0)) 
   	                             (Int.Cast.uint64_to_uint32 (nlen -^ fh0.stat.size)))))
      /\ HS.modifies (Set.singleton file_rgn) h0 h1


assume val file_next_read_buffer:
  fb:fh_ref ->
  len:bufsize ->
  Stack uint8_p
    (requires (fun h0 -> file_next_read_buffer_pre h0 fb len))
    (ensures  (fun h0 s h1 -> file_next_read_buffer_post h0 s h1 fb len))


let file_next_write_buffer_pre h (fb:fh_ref) (len:U64.t) : GTot Type0 =
  live_file h fb /\ U64.v len <= U64.v max_block_size
  /\ (let fh = get h fb 0 in file_state h fh = FileOpen
  /\ U64.v (file_offset h fh) + U64.v len <= H64.v fh.stat.size)

let file_next_write_buffer_post h0 (s:uint8_p) h1 (fb:fh_ref)
                               (len:bufsize) : GTot Type0 =
  file_next_read_buffer_pre h0 fb len
  /\ live_file h0 fb /\ live_file h1 fb /\ same_file h0 fb h1 fb
  /\ (let fh0 = get h0 fb 0 in let fh1 = get h1 fb 0 in
      let nlen = (file_offset h0 fh0) +^ len in
      U64.v (file_offset h1 fh1) = U64.v nlen
      /\ file_state h1 fh1 = FileOpen
      /\ (U64.v nlen <= H64.v fh0.stat.size ==>
               s  == Buffer.sub (file_buffer fh0.stat) 
                                (Int.Cast.uint64_to_uint32 (file_offset h0 fh0)) 
   	                        (Int.Cast.uint64_to_uint32 len)))
  /\ HS.modifies (Set.singleton file_rgn) h0 h1

assume val file_next_write_buffer: fb:fh_ref -> len:bufsize -> Stack uint8_p
    (requires (fun h0 -> file_next_write_buffer_pre h0 fb len))
    (ensures  (fun h0 s h1 -> file_next_read_buffer_post h0 s h1 fb len))

(* assume val file_next_write_buffer: fb:buffer file_handle -> len:u64 -> Stack uint8_p *)
(*     (requires (fun h0 -> U64.v len <= U64.v max_block_size /\ *)
(*     	      	         length fb = 1 /\ live h0 fb /\ *)
(*     	      	         (let f = get h0 fb 0 in *)
(* 			  file_state h0 f = FileOpen))) *)
(*     (ensures  (fun h0 s h1 -> let f = get h1 fb 0 in *)
(*     	      	              let i = file_offset h0 f in *)
(*     	      	      	      let j = U64 (file_offset h0 f +^ len) in *)
(* 			      modifies_1 s h0 h1 /\ *)
(*     	      	      	      file_state h1 f = FileOpen /\ *)
(*     	      	      	      file_offset h1 f = j /\ *)
(* 			      file_content h0 f.stat = file_content h1 f.stat /\ *)
(* 			      ((U64.v i <= v f.stat.size /\ U64.v j <= v f.stat.size) ==> s = file_sub h1 f i len)(\*  /\ *\) *)
(* 			      (\* ((U64.v i <= v f.stat.size /\ U64.v j > v f.stat.size) ==>  sub s zero (f.stat.size -^ i) = file_sub h1 f i (f.stat.size -^ i)) *\) *)
(*                               )) *)


assume val file_close: fb:fh_ref -> Stack bool
    (requires (fun h0 -> length fb = 1 /\ live_file h0 fb /\
                         (let f = get h0 fb 0 in
			  file_state h0 f = FileOpen)))
    (ensures  (fun h0 r h1 -> live_file h0 fb /\ live_file h1 fb /\ same_file h0 fb h1 fb
      /\ HS.modifies (Set.singleton file_rgn) h0 h1
      /\ (r ==> (let f = get h1 fb 0 in file_state h1 f = FileClosed /\
    			              file_content h0 f.stat == file_content h1 f.stat))))
