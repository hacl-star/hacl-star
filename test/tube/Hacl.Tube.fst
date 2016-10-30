module Hacl.Tube


open FStar.Seq
open FStar.Buffer
open PaddedFileIO
open SocketIO
open Hacl.Constants
open Hacl.Cast
open Box.Ideal 
module U64=FStar.UInt64
type clock = u64
type str = buffer u8

type boxtype = 
  | BOX_CHACHA_POLY
  | SECRETBOX_CHACHA_POLY

type streamID = b:buffer u8{length b = 16}

type open_result = {
  r: PaddedFileIO.fresult;
  sid: streamID;
  fs: PaddedFileIO.file_stat
}

val opened: PaddedFileIO.fresult -> PaddedFileIO.file_stat -> streamID -> Tot open_result
let opened r fs sid = {r = r; sid = sid; fs = fs}

(* TODO: make streamID less opaque:
{
     ty: boxtype;
     ts: C.clock_t;
     id: buffer u8;
}
*)

assume val sent: FStar.HyperStack.mem -> pkA: seq u8 -> pkB: seq u8 -> sid:seq u8 -> file_stat -> (seq u8) -> GTot bool

val makeStreamID: unit -> StackInline streamID
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> True))
let makeStreamID () = 
    let b = create 0uy 16ul in
    randombytes_buf b (U64.uint_to_t 16);
    b

val putU64: z:u64 -> b:buffer u8 -> StackInline unit
  (requires (fun h -> live h b /\ length b = 8))
  (ensures  (fun h0 r h1 -> live h1 b))
let putU64 z b = 
  let open Hacl.UInt64 in
  b.(0ul) <- sint64_to_sint8 z;
  b.(1ul) <- sint64_to_sint8 (z >>^ 8ul);
  b.(2ul) <- sint64_to_sint8 (z >>^ 16ul);
  b.(3ul) <- sint64_to_sint8 (z >>^ 24ul);
  b.(4ul) <- sint64_to_sint8 (z >>^ 32ul);
  b.(5ul) <- sint64_to_sint8 (z >>^ 40ul);
  b.(6ul) <- sint64_to_sint8 (z >>^ 48ul);
  b.(7ul) <- sint64_to_sint8 (z >>^ 56ul)

val file_send: file:str -> roundup:u64 ->
       host:str -> port:u32 -> 
       skA:buffer u8 -> pkB:buffer u8 ->
           Stack open_result
	   (requires (fun _ -> True))
	   (ensures  (fun h0 s h1 -> match s.r with 
      	   	                   | FileOk ->
				     let fs = s.fs in
				     let sidb = s.sid in
				     let pA = pubKey (as_seq h0 skA) in
				     let pB = as_seq h0 pkB in
				     let sid = as_seq h0 sidb in
				     file_content h0 fs = file_content h1 fs /\	
				     sent h1 pA pB sid fs (file_content h0 fs)
				   | _ -> true))
let file_send f r h p skA pkB =
  let sid = makeStreamID() in
  let fh = init_file_handle in
  let fb = Buffer.create fh 1ul in
  match (file_open_read_sequential f fb) with
  | FileOk -> 
      let fh = fb.(0ul) in
      let s = init_socket in
      let sb = Buffer.create s 1ul in
     (match tcp_connect h p sb with
      | SocketOk ->
	  let s = sb.(0ul) in
	  (match tcp_write_all s sid 8uL with
	   | SocketOk -> opened FileOk fh.stat sid
	   | SocketError -> opened FileError fh.stat sid)
      | SocketError -> opened FileError fh.stat sid)
  | FileError -> opened FileError fh.stat sid
  


val file_recv: port:u32 -> pkA:buffer u8 -> skB:buffer u8 -> Stack open_result
       	   (requires (fun _ -> True))
	   (ensures  (fun h0 s h1 -> match s.r with 
      	   	                   | FileOk ->
				     let fs = s.fs in
				     let sidb = s.sid in
				     let pA = as_seq h0 pkA in
				     let pB = pubKey (as_seq h0 skB) in
				     let sid = as_seq h0 sidb in
				     sent h0 pA pB sid fs (file_content h1 fs)
				   | _ -> true))
let file_recv p pkA skB =
 let sid = makeStreamID() in
 let fh = init_file_handle in
 opened FileError fh.stat sid


