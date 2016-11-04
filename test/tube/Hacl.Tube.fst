module Hacl.Tube


open FStar.Seq
open FStar.Buffer
open FileIO.Types
open PaddedFileIO
open SocketIO
open Hacl.Constants
open Hacl.Cast
open Box.Ideal

module U64=FStar.UInt64

#set-options "--lax"

type clock = u64
type str = uint8_p

type boxtype =
  | BOX_CHACHA_POLY
  | SECRETBOX_CHACHA_POLY

type streamID = b:buffer h8{length b = 16}

type open_result = {
  r: FileIO.Types.fresult;
  sid: streamID;
  fs: FileIO.Types.file_stat
}

val opened: FileIO.Types.fresult -> FileIO.Types.file_stat -> streamID -> Tot open_result
let opened r fs sid = {r = r; sid = sid; fs = fs}

(* TODO: make streamID less opaque:
{
     ty: boxtype;
     ts: C.clock_t;
     id: buffer u8;
}
*)

assume val sent: FStar.HyperStack.mem -> pkA: seq h8 -> pkB: seq h8 -> sid:seq h8 -> FileIO.Types.file_stat -> (seq h8) -> GTot bool

val makeStreamID: unit -> StackInline streamID
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> True))
let makeStreamID () =
    let b = create (Hacl.Cast.uint8_to_sint8 0uy) 16ul in
    randombytes_buf b (U64.uint_to_t 16);
    b

val putU64: z:h64 -> b:uint8_p -> StackInline unit
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
       skA:uint8_p -> pkB:uint8_p ->
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
  push_frame();
  let sid = makeStreamID() in
  let dummy_ptr = FStar.Buffer.create (Hacl.Cast.uint8_to_sint8 0uy) 1ul in
  let fh = init_file_handle(dummy_ptr) in
  let fb = Buffer.create fh 1ul in
  let res =
    match (file_open_read_sequential f fb) with
    | FileOk ->
        let fh = fb.(0ul) in
        let s = init_socket() in
        let sb = Buffer.create s 1ul in
        (match tcp_connect h p sb with
        | SocketOk ->
	    (* let s = sb.(0ul) in *)
	    (match tcp_write_all sb sid 8uL with
	    | SocketOk -> opened FileOk fh.stat sid
	    | SocketError -> opened FileError fh.stat sid)
        | SocketError -> opened FileError fh.stat sid)
    | FileError -> opened FileError fh.stat sid in
  pop_frame();
  res


val get_fh_stat: file_handle -> Tot file_stat
let get_fh_stat fh = fh.stat

val file_recv: port:u32 -> pkA:uint8_p -> skB:uint8_p -> Stack open_result
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
  push_frame();
  let dummy_ptr = FStar.Buffer.create (Hacl.Cast.uint8_to_sint8 0uy) 1ul in
  let sid = makeStreamID() in
  let fh = init_file_handle(dummy_ptr) in
  let stat = get_fh_stat fh in
  let res = opened FileError stat sid in
  pop_frame();
  res
