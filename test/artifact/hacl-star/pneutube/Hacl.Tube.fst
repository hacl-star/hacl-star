module Hacl.Tube


open FStar.Seq
open FStar.Buffer
open FileIO.Types
open PaddedFileIO
open SocketIO
open Hacl.Constants
open Hacl.Cast
open Box.Ideal

#reset-options "--initial_fuel 0 --max_fuel 0"


module  U8=FStar.UInt8
module U32=FStar.UInt32
module U64=FStar.UInt64

module  H8=Hacl.UInt8
module H32=Hacl.UInt32
module H64=Hacl.UInt64

assume val declassify: h64 -> Tot u64

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


#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 5"

(* Blocksize needs to be a power of 2 *)
inline_for_extraction let blocksize_bits = 18ul
inline_for_extraction let blocksize = U64 (256uL *^ 1024uL) //1uL <<^ blocksize_bits) // 256 * 1024
inline_for_extraction let blocksize_32 = U32 (256ul *^ 1024ul)

inline_for_extraction let cipherlen (x:U64.t{ U64.v x <= U64.v blocksize}) : U64.t = U64 (x +^ 16uL)

inline_for_extraction let cipherlen_32 (x:U32.t{ U32.v x <= U32.v blocksize_32}) : Tot U32.t = U32 (x +^ 16ul)
inline_for_extraction let ciphersize = cipherlen (blocksize)
inline_for_extraction let ciphersize_32 = cipherlen_32 (blocksize_32)
inline_for_extraction let headersize = 1024uL
inline_for_extraction let headersize_32 = 1024ul

inline_for_extraction let one_64  = Hacl.Cast.uint64_to_sint64 1uL
inline_for_extraction let zero_64 = Hacl.Cast.uint64_to_sint64 0uL
inline_for_extraction let one_8  = Hacl.Cast.uint8_to_sint8 1uy
inline_for_extraction let zero_8 = Hacl.Cast.uint8_to_sint8 0uy


(* type clock = u64 *)
type str = uint8_p


type boxtype =
  | BOX_CHACHA_POLY
  | SECRETBOX_CHACHA_POLY


type streamID = b:buffer h8{length b = 16}


noeq type open_result = {
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
  (ensures  (fun h0 sid h1 -> live h1 sid /\ ~(contains h0 sid) /\ length sid = 16))
let makeStreamID () =
    let b = create (Hacl.Cast.uint8_to_sint8 0uy) 16ul in
    randombytes_buf b 16uL;
    b


(* val putU64: z:h64 -> b:uint8_p -> StackInline unit *)
(*   (requires (fun h -> live h b /\ length b = 8)) *)
(*   (ensures  (fun h0 r h1 -> live h1 b)) *)
(* let putU64 z b = *)
(*   let open Hacl.UInt64 in *)
(*   b.(0ul) <- sint64_to_sint8 z; *)
(*   b.(1ul) <- sint64_to_sint8 (z >>^ 8ul); *)
(*   b.(2ul) <- sint64_to_sint8 (z >>^ 16ul); *)
(*   b.(3ul) <- sint64_to_sint8 (z >>^ 24ul); *)
(*   b.(4ul) <- sint64_to_sint8 (z >>^ 32ul); *)
(*   b.(5ul) <- sint64_to_sint8 (z >>^ 40ul); *)
(*   b.(6ul) <- sint64_to_sint8 (z >>^ 48ul); *)
(*   b.(7ul) <- sint64_to_sint8 (z >>^ 56ul) *)


#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 10"

(* type timespec = { *)
(*   tv_sec: U64.t; *)
(*   tv_nsec: U64.t; *)
(* } *)


(* assume val clock_gettime: unit -> St timespec *)


val store64_le:
  b:uint8_p{length b = 8} ->
  z:H64.t ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))
let store64_le b z =
  let open Hacl.UInt64 in
  b.(0ul) <- sint64_to_sint8 z;
  b.(1ul) <- sint64_to_sint8 (z >>^ 8ul);
  b.(2ul) <- sint64_to_sint8 (z >>^ 16ul);
  b.(3ul) <- sint64_to_sint8 (z >>^ 24ul);
  b.(4ul) <- sint64_to_sint8 (z >>^ 32ul);
  b.(5ul) <- sint64_to_sint8 (z >>^ 40ul);
  b.(6ul) <- sint64_to_sint8 (z >>^ 48ul);
  b.(7ul) <- sint64_to_sint8 (z >>^ 56ul)


val load64_le:
  b:uint8_p{length b >= 8} ->
  Stack h64
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> h0 == h1))
let load64_le b =
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let b4 = b.(4ul) in
  let b5 = b.(5ul) in
  let b6 = b.(6ul) in
  let b7 = b.(7ul) in
  H64 (
    sint8_to_sint64 b0
    |^ (sint8_to_sint64 b1 <<^ 8ul)
    |^ (sint8_to_sint64 b2 <<^ 16ul)
    |^ (sint8_to_sint64 b3 <<^ 24ul)
    |^ (sint8_to_sint64 b4 <<^ 32ul)
    |^ (sint8_to_sint64 b5 <<^ 40ul)
    |^ (sint8_to_sint64 b6 <<^ 48ul)
    |^ (sint8_to_sint64 b7 <<^ 56ul)
  )

open FStar.Mul


#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 10"

module HH = FStar.HyperHeap
module HS = FStar.HyperStack


noextract let triple (a:HH.rid) (b:HH.rid) (c:HH.rid) = Set.union (Set.singleton a) (Set.union (Set.singleton b) (Set.singleton c))

type uint8_p = b:uint8_p{HS.is_stack_region (frameOf b)}


#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 200 --lax"

val file_send_loop:
  fh:fh_ref ->
  sb:socket_ref ->
  ciphertext:uint8_p{Buffer.length ciphertext = U64.v blocksize + 16} ->
  nonce:uint8_p{Buffer.length nonce = 24 /\ frameOf nonce = frameOf ciphertext} ->
  key:uint8_p{Buffer.length key = 32 /\ frameOf key = frameOf nonce} ->
  seqno:H64.t ->
  len:U64.t{U64.v len + H64.v seqno < pow2 32} ->
  Stack sresult
    (requires (fun h -> 
      live_file h fh
      /\ (let fh = get h fh 0 in file_state h fh = FileOpen
      /\ U64.v (file_offset h fh) + U64.v len * U64.v blocksize <= H64.v fh.stat.size)
      /\ live h sb /\ live h ciphertext /\ live h nonce /\ live h key
      /\ current_state h (get h sb 0) = Open))
    (ensures  (fun h0 res h1 -> 
      (match res with
      | SocketOk -> (
        live_file h0 fh /\ U64.v blocksize <= U64.v max_block_size
        /\ (let fh = get h0 fh 0 in file_state h0 fh = FileOpen
        /\ U64.v (file_offset h0 fh) + U64.v len * U64.v blocksize <= H64.v fh.stat.size)
        /\ (U64.v len * U64.v blocksize) <= H64.v (get h0 fh 0).stat.size
        /\ live_file h0 fh /\ live_file h1 fh /\ same_file h0 fh h1 fh
        /\ (let fh0 = get h0 fh 0 in let fh1 = get h1 fh 0 in
          U64.v (file_offset h1 fh1) = U64.v (file_offset h0 fh0) + U64.v len * U64.v blocksize
          /\ file_state h1 fh1 = FileOpen)    
        /\ live h1 nonce /\ live_file h1 fh /\ live h1 ciphertext /\ live h1 sb
        /\ HS.modifies (triple socket_rgn file_rgn (frameOf ciphertext)) h0 h1
        /\ modifies_buf_2 (frameOf ciphertext) nonce ciphertext h0 h1
        (* /\ modifies_3 nonce fh ciphertext h0 h1 *)
        /\ current_state h1 (get h1 sb 0) = Open
        /\ same_file h0 fh h1 fh)
      | _ -> true)))
let rec file_send_loop fh sb ciphertext nonce key seqno len =
  if U64 (len =^ 0uL) then (
    SocketOk
  )
  else (
    let i = U64 (len -^ 1uL) in
    let next = file_next_read_buffer fh blocksize in
    let h0 = ST.get() in
    store64_le (sub nonce 16ul 8ul) seqno;
    let h1 = ST.get() in
    lemma_reveal_modifies_1 nonce h0 h1;
    let seqno = H64 (seqno +^ Hacl.Cast.uint64_to_sint64 1uL) in
    let _ = crypto_box_easy_afternm ciphertext next blocksize nonce key in
    let h2 = ST.get() in
    lemma_reveal_modifies_1 ciphertext h1 h2;
    let sock_res = tcp_write_all sb ciphertext ciphersize in
    let h3 = ST.get() in
    match sock_res with
    | SocketOk -> file_send_loop fh sb ciphertext nonce key seqno i
    | SocketError -> SocketError
  )


(*
val file_send_loop_2:
  fh:fh_ref ->
  sb:socket_ref ->
  ciphertext:uint8_p{Buffer.length ciphertext = U64.v blocksize + 16} ->
  plaintext:uint8_p{Buffer.length plaintext = U64.v blocksize} ->
  nonce:uint8_p{Buffer.length nonce = 24 /\ frameOf nonce = frameOf ciphertext} ->
  key:uint8_p{Buffer.length key = 32 /\ frameOf key = frameOf ciphertext} ->
  len:U64.t  ->
  Stack sresult
    (requires (fun h -> 
      live h sb /\ live h ciphertext /\ live h nonce /\ live h key /\ live h plaintext
      /\ current_state h (get h sb 0) = Open))
    (ensures (fun h0 res h1 -> 
      (match res with
      | SocketOk -> (
        live h1 ciphertext /\ live h1 sb
        /\ HS.modifies (Set.union (Set.singleton socket_rgn) (Set.singleton (frameOf ciphertext))) h0 h1
        /\ modifies_buf_1 (frameOf ciphertext) ciphertext h0 h1
        /\ current_state h1 (get h1 sb 0) = Open)
      | _ -> true)))

let rec file_send_loop_2 fh sb ciphertext plaintext nonce key len =
  if U64 (len =^ 0uL) then SocketOk
  else (
    let i = U64 (len -^ 1uL) in
    let h0 = ST.get() in
    let _ = crypto_box_easy_afternm ciphertext plaintext blocksize nonce key in
    let h1 = ST.get() in
    lemma_reveal_modifies_1 ciphertext h0 h1;
    match tcp_write_all sb ciphertext ciphersize with
    | SocketOk -> file_send_loop_2 fh sb ciphertext plaintext nonce key i
    | SocketError -> SocketError
  )
*)


(* security spec *)
(*
val file_send:
  fsize:u32 -> file:str -> roundup:u64 ->
  host:str -> port:u32 ->
  skA:uint8_p -> pkB:uint8_p ->
  Stack open_result
    (requires (fun _ -> U32.v fsize <= length file))
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
*)


#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 200 --lax"


val file_send_fragments:
  sb:socket_ref ->
  fb:fh_ref ->
  pkA:uint8_p ->
  pkB:uint8_p ->
  sid:streamID ->
  ciphertext:uint8_p{Buffer.length ciphertext = U64.v blocksize + 16} ->
  nonce:uint8_p{Buffer.length nonce = 24 /\ frameOf nonce = frameOf ciphertext} ->
  key:uint8_p{Buffer.length key = 32 /\ frameOf key = frameOf nonce} ->
  seqno:H64.t ->
  len:U64.t{U64.v len + H64.v seqno < pow2 32} ->
  rem:U64.t{U64.v rem < U64.v blocksize} ->
  Stack open_result
    (requires (fun h ->
      live_file h fb
      /\ (let fh = get h fb 0 in file_state h fh = FileOpen
      /\ U64.v (file_offset h fh) + U64.v len * U64.v blocksize <= H64.v fh.stat.size)
      /\ live h sb /\ live h ciphertext /\ live h nonce /\ live h key /\ live h pkA /\ live h pkB
      /\ current_state h (get h sb 0) = Open))
    (ensures (fun h0 r h1 -> True))
let file_send_fragments sb fb pkA pkB sid ciphertext nonce key seqno fragments rem =
  let fh  = Buffer.index fb 0ul in
  match file_send_loop fb sb ciphertext nonce key seqno fragments with
  | SocketOk -> (
      if U64 (rem  >^ 0uL) then (
        let next = file_next_read_buffer fb rem in
        let seqno = Hacl.Cast.uint64_to_sint64 (U64 (fragments +%^ 1uL)) in
	let h0 = ST.get() in
        store64_le (sub nonce 16ul 8ul) seqno;
	let h1 = ST.get() in
	lemma_reveal_modifies_1 nonce h0 h1;
        let clen = U32 (Int.Cast.uint64_to_uint32 rem +^ 16ul) in
        assume (U32.v clen = U64.v rem + 16);
        assume (as_seq h1 key == agreedKey (as_seq h1 pkA) (as_seq h1 pkB));
        let _ = crypto_box_easy_afternm #pkA #pkB (sub ciphertext 0ul clen) next rem nonce key in
	(* let _ = crypto_box_easy_afternm #pkA #pkB ciphertext next blocksize nonce key in *)
	let h2 = ST.get() in
	lemma_reveal_modifies_1 ciphertext h1 h2;
	let sock_res = tcp_write_all sb ciphertext (cipherlen rem) in
	let h3 = ST.get() in
        (match sock_res with
        | SocketOk -> opened FileOk fh.stat sid
        | SocketError -> opened FileError fh.stat sid)
      ) else (
        opened FileOk fh.stat sid
      ) )
  | SocketError -> opened FileError fh.stat sid


val file_flush_all:
  sb:socket_ref ->
  fb:fh_ref ->
  skA:uint8_p ->
  pkA:uint8_p ->
  pkB:uint8_p ->
  sid:streamID ->
  header:uint8_p ->
  ciphertext:uint8_p{Buffer.length ciphertext = U64.v blocksize + 16} ->
  len:U64.t{U64.v len < pow2 32} ->
  hsize:U64.t ->
  rem:U64.t{U64.v rem < U64.v blocksize} ->
  buf:uint8_p ->
  Stack open_result
    (requires (fun _ -> true))
    (ensures (fun _ _ _ -> true))
let file_flush_all sb fb skA pkA pkB sid header ciphertext fragments hsize rem buf =
  let fh  = Buffer.index fb 0ul in
  (match tcp_write_all sb sid 16uL with
    | SocketOk -> (
                store64_le buf hsize;
                match tcp_write_all sb buf 8uL with
                | SocketOk -> (
                    match tcp_write_all sb pkA 32uL with
                    | SocketOk -> (
                        match tcp_write_all sb pkB 32uL with
                        | SocketOk -> (
                            let seqno = zero_64 in
                            let nonce = Buffer.create zero_8 24ul in
                            let key   = Buffer.create zero_8 32ul in
                            if U32 (crypto_box_beforenm key pkB skA =^ 0ul) then (
                              (* Populating the nonce *)
                              blit sid 0ul nonce 0ul 16ul;
                              store64_le (sub nonce 16ul 8ul) seqno;
                              let seqno = H64 (seqno +%^ one_64) in
                              let _ = crypto_box_easy_afternm #pkA #pkB ciphertext header headersize
                                                               nonce key in
                              (match tcp_write_all sb ciphertext (cipherlen headersize) with
                              | SocketOk -> file_send_fragments sb fb pkA pkB sid ciphertext nonce key seqno fragments rem                              
                                  (* match file_send_loop fb sb ciphertext nonce key seqno fragments with *)
                                  (* | SocketOk -> ( *)
                                  (*     if U64 (rem  >^ 0uL) then ( *)
                                  (*       let next = file_next_read_buffer fb rem in *)
                                  (*       let seqno = Hacl.Cast.uint64_to_sint64 (U64 (fragments +%^ 1uL)) in *)
				  (*       let h0 = ST.get() in *)
                                  (*       store64_le (sub nonce 16ul 8ul) seqno; *)
				  (*       let h1 = ST.get() in *)
				  (*       lemma_reveal_modifies_1 nonce h0 h1; *)
				  (*       let _ = crypto_box_easy_afternm #pkA #pkB ciphertext next blocksize nonce key in *)
				  (*       let h2 = ST.get() in *)
				  (*       lemma_reveal_modifies_1 ciphertext h1 h2; *)
				  (*       let sock_res = tcp_write_all sb ciphertext (cipherlen rem) in *)
				  (*       let h3 = ST.get() in *)
                                  (*       (match sock_res with *)
                                  (*       | SocketOk -> opened FileOk fh.stat sid *)
                                  (*       | SocketError -> opened FileError fh.stat sid) *)
                                  (*     ) else ( *)
                                  (*       opened FileOk fh.stat sid *)
                                  (*     ) ) *)
                                  (* | SocketError -> opened FileError fh.stat sid ) *)
                              | SocketError -> opened FileError fh.stat sid )
                            ) else (
                              opened FileOk fh.stat sid
                            ) )
                        | SocketError -> opened FileError fh.stat sid )
                    | SocketError -> opened FileError fh.stat sid )
                | SocketError -> opened FileError fh.stat sid )
            | SocketError -> opened FileError fh.stat sid )


val file_send:
  fsize:u32 -> file:str{length file = U32.v fsize /\ length file < 100} -> roundup:u64 ->
  host:str -> port:u32 ->
  skA:privateKey -> pkB:publicKey ->
  ST open_result
    (requires (fun h -> live h file /\ live h host /\ live h skA /\ live h pkB /\
    	      	        U32.v fsize <= length file))
    (ensures  (fun h0 s h1 -> match s.r with
      	   	                   | FileOk -> true
				     (* HS.modifies Set.empty h0 h1 *)
				   | _ -> true))

let file_send fsize f r h p skA pkB =
  push_frame();
  (* Initializing all buffers on the stack *)
  let pkA = Buffer.create (Hacl.Cast.uint8_to_sint8 0uy) 32ul in
  let h0 = ST.get() in
  getPublicKey skA pkA;
  let h1 = ST.get() in
  lemma_reveal_modifies_1 pkA h0 h1;

  let zero = Hacl.Cast.uint8_to_sint8 0uy in

  (* Initialization of the file_handle *)
  let dummy_ptr = FStar.Buffer.create (Hacl.Cast.uint8_to_sint8 0uy) 1ul in
  let fb = Buffer.rcreate file_rgn (init_file_handle(dummy_ptr)) 1ul in

  (* let c1 = C.clock() in *)

  (* Initialization of the sessionID *)
  let sid = makeStreamID() in

  let res =
    match (file_open_read_sequential f fb) with
    | FileOk ->
        (* Read file handle value *)
        let fh = fb.(0ul) in
        (* Initialization of the socket *)
        let s = init_socket() in
        let sb = Buffer.rcreate socket_rgn s 1ul in
        (match tcp_connect h p sb with
        | SocketOk ->
	    let s = sb.(0ul) in
            let ciphertext = Buffer.create zero ciphersize_32 in
            let file_size = fh.stat.size in

            (* We assume that blocksize and roundup are both powers of 2;	
	       Otherwise we will need "modulo" which is not constant-time *)
	    let sblock = Hacl.Cast.uint64_to_sint64 blocksize in
            let roundup = Hacl.Cast.uint64_to_sint64 r in
	    let file_size_mod_roundup = H64 (file_size &^ (roundup-%^one_64)) in 
            let mask = H64 (gte_mask roundup one_64 &^ (lognot (eq_mask file_size_mod_roundup zero_64))) in 
            let frem = H64 ((roundup -%^ file_size_mod_roundup) &^ mask) in 
            let hsize = H64 (file_size +%^ frem) in
            let hfragments = H64 (hsize >>^ blocksize_bits) in 
            let hrem = H64 (file_size &^ (sblock-^one_64)) in 
	    let fragments = declassify hfragments in
            assume (Hacl.Policies.declassifiable hrem);
	    let rem = Hacl.Policies.declassify_u64 hrem in
            let mtime = fh.stat.mtime in
            let header = Buffer.create zero_8 headersize_32 in
	    let f64: h64 = Hacl.Cast.uint32_to_sint64 fsize in
            (* JK: Omitting memset to 0 for now *)
            store64_le (Buffer.sub header  0ul 8ul) file_size;
            store64_le (Buffer.sub header  8ul 8ul) mtime;
            store64_le (Buffer.sub header 16ul 8ul) f64;
            (* JK: Ignoring the test on the file name length for convenience *)
            Buffer.blit f 0ul header 24ul fsize;
            (* A buffer to store uint64 values before flushing them *)
            let buf = Buffer.create zero 8ul in
            (* Flush the streamID *)
            file_flush_all sb fb skA pkA pkB sid header ciphertext fragments hsize rem buf      
	    (* (match tcp_write_all sb sid 16uL with *)
	    (* | SocketOk -> ( *)
            (*     store64_le buf hsize; *)
            (*     match tcp_write_all sb buf 8uL with *)
            (*     | SocketOk -> ( *)
            (*         match tcp_write_all sb pkA 32uL with *)
            (*         | SocketOk -> ( *)
            (*             match tcp_write_all sb pkB 32uL with *)
            (*             | SocketOk -> ( *)
            (*                 let seqno = zero_64 in *)
            (*                 let nonce = Buffer.create zero 24ul in *)
            (*                 let key   = Buffer.create zero 32ul in *)
            (*                 if U32 (crypto_box_beforenm key pkB skA =^ 0ul) then ( *)
            (*                   (\* Populating the nonce *\) *)
            (*                   blit sid 0ul nonce 0ul 16ul; *)
            (*                   store64_le (sub nonce 16ul 8ul) seqno; *)
            (*                   let seqno = H64 (seqno +%^ one_64) in *)
            (*                   let _ = crypto_box_easy_afternm #pkA #pkB ciphertext header headersize *)
            (*                                                    nonce key in *)
            (*                   (match tcp_write_all sb ciphertext (cipherlen headersize) with *)
            (*                   | SocketOk -> ( *)
            (*                       match file_send_loop fb sb ciphertext nonce key seqno fragments with *)
            (*                       | SocketOk -> ( *)
            (*                           if U64 (rem  >^ 0uL) then ( *)
            (*                             let next = file_next_read_buffer fb rem in *)
            (*                             let seqno = Hacl.Cast.uint64_to_sint64 (U64 (fragments +%^ 1uL)) in *)
	    (*     			let h0 = ST.get() in *)
            (*                             store64_le (sub nonce 16ul 8ul) seqno; *)
	    (*     			let h1 = ST.get() in *)
	    (*     			lemma_reveal_modifies_1 nonce h0 h1; *)
	    (*     			let _ = crypto_box_easy_afternm #pkA #pkB ciphertext next blocksize nonce key in *)
	    (*     			let h2 = ST.get() in *)
	    (*     			lemma_reveal_modifies_1 ciphertext h1 h2; *)
	    (*     			let sock_res = tcp_write_all sb ciphertext (cipherlen rem) in *)
	    (*     			let h3 = ST.get() in *)
            (*                             (match sock_res with *)
            (*                             | SocketOk -> opened FileOk fh.stat sid *)
            (*                             | SocketError -> opened FileError fh.stat sid) *)
            (*                           ) else ( *)
            (*                             opened FileOk fh.stat sid *)
            (*                           ) ) *)
            (*                       | SocketError -> opened FileError fh.stat sid ) *)
            (*                   | SocketError -> opened FileError fh.stat sid ) *)
            (*                 ) else ( *)
            (*                   opened FileOk fh.stat sid *)
            (*                 ) ) *)
            (*             | SocketError -> opened FileError fh.stat sid ) *)
            (*         | SocketError -> opened FileError fh.stat sid ) *)
            (*     | SocketError -> opened FileError fh.stat sid ) *)
            (* | SocketError -> opened FileError fh.stat sid ) *)
        | SocketError -> opened FileError fh.stat sid )
    | FileError -> opened FileError (fb.(0ul)).stat sid in
  pop_frame();
  (* let c2 = C.clock() in *)
  (* TestLib.print_clock_diff c1 c2; *)
  res

#set-options "--lax"

(** Non-Constant time comparison function **)
val memcmp:
  b:buffer u8 ->
  b':buffer u8 ->
  len:U32.t ->
  Stack U8.t
    (requires (fun _ -> True))
    (ensures  (fun _ _ _ -> True))
let rec memcmp b b' len =
  if U32 (len =^ 0ul) then (
    0xffuy
  ) else (
    let i = U32 (len -^ 1ul) in
    if U8 (b.(i) =^ b'.(i)) then
       memcmp b b' i
    else 0x00uy)


val get_fh_stat: file_handle -> Tot file_stat
let get_fh_stat fh = fh.stat

val file_recv_loop_2:
  fb:buffer file_handle ->
  connb:buffer socket ->
  ciphertext:buffer u8 ->
  nonce:uint8_p ->
  key:uint8_p ->
  seqno:H64.t ->
  len:U64.t ->
  Stack sresult
    (requires (fun _ -> True))
    (ensures  (fun _ _ _ -> True))
let rec file_recv_loop_2 fb connb ciphertext nonce key seqno len =
  if U64 (len =^ 0uL) then SocketOk
  else 
  if U64 (len <^ blocksize) then (
    match tcp_read_all connb ciphertext (cipherlen len) with
    | SocketOk -> (
        let next = file_next_write_buffer fb blocksize in
        store64_le (sub nonce 16ul 8ul) seqno;
        let seqno = H64 (seqno +^ one_64) in
        if U32 (crypto_box_open_easy_afternm next ciphertext (cipherlen len) nonce key =^ 0ul) then
	  SocketOk 
	else  (TestLib.perr(20ul); SocketError))
    | SocketError -> TestLib.perr(21ul); TestLib.perr(Int.Cast.uint64_to_uint32 len); SocketError)
  else (
    match tcp_read_all connb ciphertext ciphersize with
    | SocketOk -> (
        let rem = U64 (len -^ blocksize) in
        let next = file_next_write_buffer fb blocksize in
        store64_le (sub nonce 16ul 8ul) seqno;
        let seqno = H64 (seqno +^ one_64) in
        if U32 (crypto_box_open_easy_afternm next ciphertext ciphersize nonce key =^ 0ul) then
          file_recv_loop_2 fb connb ciphertext nonce key seqno rem
        (* JK: not distinguishing between socket error and decryption failure *)
        else (TestLib.perr(20ul); SocketError) )
    | SocketError -> TestLib.perr(21ul); TestLib.perr(Int.Cast.uint64_to_uint32 len); SocketError
  )


val file_recv_loop:
  fb:buffer file_handle ->
  connb:buffer socket ->
  lhb:buffer socket ->
  sid:uint8_p ->
  pkA:publicKey ->
  pkB:publicKey ->
  skB:privateKey ->
  Stack sresult
    (requires (fun h -> True))
    (ensures  (fun h0 _ h1 -> True))
let rec file_recv_loop fb connb lhb sid pkA pkB skB =
  push_frame();
  let res =
  match tcp_accept lhb connb with
  | SocketOk -> (
      let ciphertext = create zero_8 ciphersize_32 in
      let pk1 = create zero_8 32ul in
      let pk2 = create zero_8 32ul in
      let nonce = create zero_8 24ul in
      let hsizeb = create zero_8 8ul in
      let c1 = C.clock() in
      (match tcp_read_all connb (sub nonce 0ul 16ul) 16uL with
      | SocketOk -> (
          (* JK: no check on the streamID formatting *)
          match tcp_read_all connb hsizeb 8uL with
          | SocketOk -> (
	      let hsize = load64_le hsizeb in
              match tcp_read_all connb pk1 32uL with
              | SocketOk -> (
                  match tcp_read_all connb pk2 32uL with
                  | SocketOk -> (
                      if U8 (memcmp pk1 pkA 32ul =^ 0xffuy) then (
                         if U8 (memcmp pk2 pkB 32ul =^ 0xffuy) then (
                           let key = create zero_8 32ul in
                           (* JK: ignoring check on beforenm *)
                           let _ = crypto_box_beforenm key pkA skB in
                           let seqno = 0uL in
                           let header = create zero_8 headersize_32 in
                           fill header zero_8 headersize_32;
                           (match tcp_read_all connb ciphertext (cipherlen(headersize)) with
                           | SocketOk -> (
                               store64_le (sub nonce 16ul 8ul) seqno;
                               let seqno = H64 (seqno +^ 1uL) in
                               if U32 (crypto_box_open_easy_afternm header ciphertext (cipherlen(headersize)) nonce key =^ 0ul) then (
                                 let file_size = load64_le (sub header 0ul  8ul) in
                                 let nsize     = load64_le (sub header 8ul  8ul) in
                                 let mtime     = load64_le (sub header 16ul 8ul) in
                                 (* JK: no checking the size of the filename *)
                                 (* JK: need declassification on nsize value *)
                                 let file = sub header 24ul (Int.Cast.uint64_to_uint32 nsize) in
                                 let fstat = {name = file; mtime = mtime; size = nsize} in
                                 (match file_open_write_sequential fstat fb with
                                 | FileOk -> 
                                     (match file_recv_loop_2 fb connb ciphertext nonce key seqno hsize with
                                     | SocketOk -> (
				           match file_close fb with
                                             | false -> (
                                                 match tcp_close connb with
                                                 | SocketOk -> (
                                                     let c2 = C.clock() in
                                                     TestLib.print_clock_diff c1 c2;
                                                     SocketOk )
                                                 | SocketError -> TestLib.perr(13ul); SocketError )
                                             | true -> TestLib.perr(12ul); SocketError )
                                      | SocketError -> TestLib.perr(10ul); SocketError )
                                 | FileError -> TestLib.perr(9ul); SocketError )
                               ) else (
                                 TestLib.perr(8ul); SocketError ) )
                           | SocketError -> SocketError )
                         ) else (
                           TestLib.perr(7ul); SocketError
                         )
                       ) else (
                         TestLib.perr(6ul); SocketError ))
                  | SocketError -> TestLib.perr(5ul); SocketError )
              | SocketError -> TestLib.perr(4ul); SocketError )
          | SocketError -> TestLib.perr(3ul); SocketError )
      | SocketError -> TestLib.perr(2ul); SocketError ))
  | SocketError -> TestLib.perr(1ul); SocketError in
  pop_frame();
  match res with
  | SocketOk -> file_recv_loop  fb connb lhb sid pkA pkB skB
  | SocketError -> TestLib.perr(0ul); SocketError


val file_recv: port:u32 -> pkA:publicKey -> skB:privateKey -> Stack open_result
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
  (* Initialization of the file_handle *)
  let dummy_ptr = FStar.Buffer.create (Hacl.Cast.uint8_to_sint8 0uy) 1ul in
  let fh = init_file_handle(dummy_ptr) in
  let fb = create fh 1ul in
  let sid = makeStreamID() in
  let stat = get_fh_stat fh in
  (* Initialization of the two sockets *)
  let s = init_socket() in
  let connb = Buffer.create s 1ul in
  let lhb = Buffer.create s 1ul in
  let res = (match tcp_listen p lhb with
  | SocketOk -> (
      let pkB = Buffer.create (Hacl.Cast.uint8_to_sint8 0uy) 32ul in
      let h0 = ST.get() in
      getPublicKey skB pkB;
      let h1 = ST.get() in
      lemma_reveal_modifies_1 pkB h0 h1;
      match file_recv_loop fb connb lhb sid pkA pkB skB with
      | SocketOk -> opened FileOk fh.stat sid
      | SocketError -> opened FileError fh.stat sid )
  | SocketError -> opened FileError fh.stat sid ) in
  pop_frame();
  res
