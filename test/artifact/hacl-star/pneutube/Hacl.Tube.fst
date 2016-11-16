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


val makeStreamID: s:streamID -> StackInline unit
  (requires (fun h -> live h s))
  (ensures  (fun h0 sid h1 -> live h1 s /\ modifies_1 s h0 h1))
let makeStreamID b =
    (* let b = create (Hacl.Cast.uint8_to_sint8 0uy) 16ul in *)
    randombytes_buf b 16uL
    (* b *)


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

type uint8_p = b:uint8_p{frameOf b <> file_rgn /\ frameOf b <> socket_rgn}


#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 200"

val file_send_loop:
  fh:fh_ref ->
  sb:socket_ref ->
  immut_state:uint8_p{length immut_state = 1244} ->
  mut_state:uint8_p{length mut_state = U64.v ciphersize + 24 /\ frameOf mut_state <> frameOf immut_state} ->  
  seqno:H64.t ->
  len:U64.t{U64.v len + H64.v seqno < pow2 32} ->
  Stack sresult
    (requires (fun h -> 
      live_file h fh
      /\ (let fh = get h fh 0 in file_state h fh = FileOpen)
      (* /\ U64.v (file_offset h fh) + U64.v len * U64.v blocksize <= H64.v fh.stat.size + U64.v max_block_size) *)
      /\ live h sb /\ live h immut_state /\ live h mut_state
      /\ current_state h (get h sb 0) = Open))
    (ensures  (fun h0 res h1 -> 
      (match res with
      | SocketOk -> (
        live_file h0 fh
        /\ (let fh = get h0 fh 0 in file_state h0 fh = FileOpen)
        (* /\ U64.v (file_offset h0 fh) + U64.v len * U64.v blocksize <= H64.v fh.stat.size + U64.v max_block_size) *)
        (* /\ (U64.v len * U64.v blocksize) <= H64.v (get h0 fh 0).stat.size *)
        /\ live_file h0 fh /\ live_file h1 fh /\ same_file h0 fh h1 fh
        /\ (let fh0 = get h0 fh 0 in let fh1 = get h1 fh 0 in
          (* U64.v (file_offset h1 fh1) = U64.v (file_offset h0 fh0) + U64.v len * U64.v blocksize *)
          file_state h1 fh1 = FileOpen)
        /\ live_file h1 fh /\ live h1 mut_state /\ live h1 sb
        /\ HS.modifies (triple socket_rgn file_rgn (frameOf mut_state)) h0 h1
        /\ modifies_buf_1 (frameOf mut_state) mut_state h0 h1
        (* /\ modifies_3 nonce fh ciphertext h0 h1 *)
        /\ current_state h1 (get h1 sb 0) = Open
        /\ same_file h0 fh h1 fh)
      | _ -> true)))
let rec file_send_loop fh sb immut_state mut_state seqno len =
  let pkA   = Buffer.sub immut_state 0ul 32ul in
  let pkB   = Buffer.sub immut_state 32ul 32ul in
  let key   = Buffer.sub immut_state 64ul 32ul in
  let sid   = Buffer.sub immut_state 96ul 16ul in
  let hsbuf   = Buffer.sub immut_state 112ul 8ul in
  let fname   = Buffer.sub immut_state 120ul 100ul in
  let header  = Buffer.sub immut_state 220ul 1024ul in
  let ciphertext = Buffer.sub mut_state 0ul (ciphersize_32) in
  let nonce      = Buffer.sub mut_state ciphersize_32 24ul in
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
    assume (as_seq h1 key = agreedKey (as_seq h1 pkA) (as_seq h1 pkB));
    let _ = crypto_box_easy_afternm #pkA #pkB ciphertext next blocksize nonce key in
    let h2 = ST.get() in
    lemma_reveal_modifies_1 mut_state h1 h2;
    let sock_res = tcp_write_all sb ciphertext ciphersize in
    let h3 = ST.get() in
    match sock_res with
    | SocketOk -> file_send_loop fh sb immut_state mut_state seqno i
    | SocketError -> SocketError
  )



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


#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 200"

val file_send_fragments:
  sb:socket_ref ->
  fb:fh_ref ->
  immut_state:uint8_p{length immut_state = 1244} ->
  mut_state:uint8_p{length mut_state = U64.v ciphersize + 24 /\ frameOf mut_state <> frameOf immut_state} ->
  seqno:H64.t ->
  len:U64.t{U64.v len + H64.v seqno < pow2 32} ->
  rem:U64.t{U64.v rem < U64.v blocksize} ->
  Stack open_result
    (requires (fun h ->
      live_file h fb
      /\ (let fh = get h fb 0 in file_state h fh = FileOpen)
      (* /\ U64.v (file_offset h fh) + U64.v len * U64.v blocksize <= H64.v fh.stat.size) *)
      /\ live h sb /\ live h immut_state /\ live h mut_state
      /\ current_state h (get h sb 0) = Open))
    (ensures (fun h0 r h1 -> True))
let file_send_fragments sb fb immut_state mut_state seqno fragments rem =
  let fh  = Buffer.index fb 0ul in
  let pkA   = Buffer.sub immut_state 0ul 32ul in
  let pkB   = Buffer.sub immut_state 32ul 32ul in
  let key   = Buffer.sub immut_state 64ul 32ul in
  let sid   = Buffer.sub immut_state 96ul 16ul in
  let hsbuf   = Buffer.sub immut_state 112ul 8ul in
  let fname   = Buffer.sub immut_state 120ul 100ul in
  let header  = Buffer.sub immut_state 220ul 1024ul in
  let ciphertext = Buffer.sub mut_state 0ul (ciphersize_32) in
  let nonce      = Buffer.sub mut_state ciphersize_32 24ul in
  match file_send_loop fb sb immut_state mut_state seqno fragments with
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

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 400"

val file_flush_all:
  sb:socket_ref ->
  fb:fh_ref ->
  immut_state:uint8_p{length immut_state = 1244} ->
  mut_state:uint8_p{length mut_state = U64.v ciphersize + 24 /\ frameOf immut_state <> frameOf mut_state} ->
  ctr:U64.t{U64.v ctr < pow2 32 - 1} ->
  rem:U64.t{U64.v rem < U64.v blocksize} ->
  Stack open_result
    (requires (fun h -> live h sb /\ current_state h (get h sb 0) = Open
      /\ live_file h fb /\ (let fh = get h fb 0 in file_state h fh = FileOpen)
      /\ live h immut_state /\ live h mut_state))
    (ensures (fun h0 r h1 -> True))
let file_flush_all sb fb immut_state mut_state ctr rem =
  let fh  = Buffer.index fb 0ul in
  let pkA   = Buffer.sub immut_state 0ul 32ul in
  let pkB   = Buffer.sub immut_state 32ul 32ul in
  let key   = Buffer.sub immut_state 64ul 32ul in
  let sid   = Buffer.sub immut_state 96ul 16ul in
  let hsbuf   = Buffer.sub immut_state 112ul 8ul in
  let fname   = Buffer.sub immut_state 120ul 100ul in
  let header  = Buffer.sub immut_state 220ul 1024ul in
  let ciphertext = Buffer.sub mut_state 0ul (ciphersize_32) in
  let nonce      = Buffer.sub mut_state ciphersize_32 24ul in
  (match tcp_write_all sb sid 16uL with
    | SocketOk -> (
                match tcp_write_all sb hsbuf 8uL with
                | SocketOk -> (
                    match tcp_write_all sb pkA 32uL with
                    | SocketOk -> (
                        match tcp_write_all sb pkB 32uL with
                        | SocketOk -> (
                            let seqno = zero_64 in
                            let h0 = ST.get() in
                            (* Populating the nonce *)
                            blit sid 0ul nonce 0ul 16ul;
                            store64_le (sub nonce 16ul 8ul) seqno;
                            let seqno = H64 (seqno +%^ one_64) in
                            let h = ST.get() in
                            assume (as_seq h key == agreedKey (as_seq h pkA) (as_seq h pkB));
                            let ciphertext' = sub ciphertext 0ul (U32 (headersize_32 +^ 16ul)) in
                            let _ = crypto_box_easy_afternm #pkA #pkB ciphertext' header headersize
                                                             nonce key in
                            let h1 = ST.get() in
                            lemma_reveal_modifies_1 mut_state h0 h1;
                            (match tcp_write_all sb ciphertext' (cipherlen headersize) with
                            | SocketOk -> file_send_fragments sb fb immut_state mut_state seqno ctr rem
                            | SocketError -> opened FileError fh.stat sid ) )
                        | SocketError -> opened FileError fh.stat sid )
                    | SocketError -> opened FileError fh.stat sid )
                | SocketError -> opened FileError fh.stat sid )
            | SocketError -> opened FileError fh.stat sid )


#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 200 --lax"


assume val input_rgn: r:HH.rid{r <> file_rgn /\ r <> socket_rgn}
assume val dummy_ptr: uint8_p


val file_send_2:
  sb:socket_ref ->
  fb:fh_ref ->
  immutable_state:uint8_p{length immutable_state = 1244} ->
  num:U64.t ->
  rem:U64.t{U64.v rem < U64.v blocksize} ->
  Stack open_result
    (requires (fun h -> live h immutable_state /\ live h sb /\ live_file h fb))
    (ensures  (fun h0 s h1 -> true))

let file_send_2 sb fb immut_state num rem =
  push_frame();
  let s = sb.(0ul) in
  let fh = fb.(0ul) in
  let mut_state = Buffer.create zero_8 (U32 (ciphersize_32 +^ 24ul)) in
  let header = Buffer.create zero_8 headersize_32 in
  let res = file_flush_all sb fb immut_state mut_state num rem in
  pop_frame();
  res
  

val file_send:
  fsize:u32 ->
  file:str{length file = U32.v fsize /\ length file < 100 /\ frameOf file = input_rgn} ->
  roundup:u64 ->
  host:str{frameOf host = input_rgn} -> port:u32 ->
  skA:privateKey{frameOf skA = input_rgn} ->
  pkB:publicKey{frameOf pkB = input_rgn /\ disjoint skA pkB} ->
  ST open_result
    (requires (fun h -> live h file /\ live h host /\ live h skA /\ live h pkB /\
    	      	        U32.v fsize <= length file))
    (ensures  (fun h0 s h1 -> match s.r with
      	   	                   | FileOk -> true
				     (* HS.modifies Set.empty h0 h1 *)
				   | _ -> true))

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 200 --lax"

let file_send fsize f r h p skA pkB =
  push_frame();
  let h0 = ST.get() in
  (* Initializing all buffers on the stack *)
  let state = Buffer.create zero_8 1244ul  in
  let pkA   = Buffer.sub state 0ul 32ul in
  let pkB_cpy = Buffer.sub state 32ul 32ul in
  let key   = Buffer.sub state 64ul 32ul in
  let sid   = Buffer.sub state 96ul 16ul in
  let hsbuf   = Buffer.sub state 112ul 8ul in
  let fname   = Buffer.sub state 120ul 100ul in
  let header  = Buffer.sub state 220ul 1024ul in
  let h0' = ST.get() in
  getPublicKey skA pkA;
  makeStreamID sid;
  blit pkB 0ul pkB_cpy 0ul 32ul;
  Buffer.blit f 0ul fname 0ul fsize;
  let keygen_res = U32 (crypto_box_beforenm key pkB skA =^ 0ul) in
  let h1 = ST.get() in
  assert(modifies_0 h0 h1);
  (* Initialization of the file_handle *)
  let fb = Buffer.rcreate file_rgn (init_file_handle(dummy_ptr)) 1ul in
  (* Initialization of the socket *)
  let s = init_socket() in
  let sb = Buffer.rcreate socket_rgn s 1ul in
  let res =
    match (file_open_read_sequential f fb) with
    | FileOk ->
        (* Read file handle value *)
        let fh = fb.(0ul) in
        let file_size = fh.stat.size in
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
        let file_size = fh.stat.size in
        let mtime = fh.stat.mtime in
        let f64: h64 = Hacl.Cast.uint32_to_sint64 fsize in
        store64_le (Buffer.sub header  0ul 8ul) file_size;
        store64_le (Buffer.sub header  8ul 8ul) mtime;
        store64_le (Buffer.sub header 16ul 8ul) f64;
        Buffer.blit f 0ul header 24ul fsize;
        store64_le (hsbuf) hsize;
        (match tcp_connect h p sb with
        | SocketOk -> file_send_2 sb fb state fragments rem
        | SocketError -> opened FileError fh.stat sid )
    | FileError -> opened FileError (fb.(0ul)).stat sid in
  pop_frame();
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
  fb:fh_ref ->
  connb:socket_ref ->
  state: uint8_p{length state = 1244} ->
  mut_state:uint8_p{length mut_state = U64.v ciphersize + 24 /\ frameOf mut_state <> frameOf state} ->  
  seqno:H64.t ->
  len:U64.t ->
  Stack sresult
    (requires (fun _ -> True))
    (ensures  (fun _ _ _ -> True))
let rec file_recv_loop_2 fb connb state mut_state seqno len =
  let key   = Buffer.sub state 64ul 32ul in
  let ciphertext = Buffer.sub mut_state 0ul (ciphersize_32) in
  let nonce      = Buffer.sub mut_state ciphersize_32 24ul in
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
          file_recv_loop_2 fb connb state mut_state seqno rem
        (* JK: not distinguishing between socket error and decryption failure *)
        else (TestLib.perr(20ul); SocketError) )
    | SocketError -> TestLib.perr(21ul); TestLib.perr(Int.Cast.uint64_to_uint32 len); SocketError
  )


val file_recv_enc:
  fb:fh_ref ->
  connb:socket_ref ->
  state: uint8_p{length state = 1244} ->
  hsize: U64.t ->
  Stack sresult
    (requires (fun h -> True))
    (ensures  (fun h0 _ h1 -> True))

let file_recv_enc fb connb state size = 
      let header  = Buffer.sub state 220ul 1024ul in
      let seqno = 0uL in
      let mut_state = Buffer.create zero_8 (U32 (ciphersize_32 +^ 24ul)) in
      let ciphertext = Buffer.sub mut_state 0ul (ciphersize_32) in
      let nonce      = Buffer.sub mut_state ciphersize_32 24ul in
      let key   = Buffer.sub state 64ul 32ul in
      let pkA   = Buffer.sub state 0ul 32ul in
      let pkB   = Buffer.sub state 32ul 32ul in

      (match tcp_read_all connb ciphertext (cipherlen(headersize)) with
      | SocketOk -> (
          store64_le (sub nonce 16ul 8ul) seqno;
          let seqno = H64 (seqno +^ 1uL) in
	  let h = ST.get() in
          if U32 (crypto_box_open_easy_afternm #pkA #pkB header ciphertext (cipherlen(headersize)) nonce key =^ 0ul) then (
             let file_size = load64_le (sub header 0ul  8ul) in
             let nsize     = load64_le (sub header 8ul  8ul) in
             let mtime     = load64_le (sub header 16ul 8ul) in
             let file = sub header 24ul (Int.Cast.uint64_to_uint32 nsize) in
             let fstat = {name = file; mtime = mtime; size = file_size} in
             (match file_open_write_sequential fstat fb with
              | FileOk -> 
                  (match file_recv_loop_2 fb connb state mut_state seqno size with
                   | SocketOk -> (
     		         match file_close fb with
                       | false -> (
                             match tcp_close connb with
                            | SocketOk -> (
                                  SocketOk )
                            | SocketError -> TestLib.perr(13ul); SocketError )
                       | true -> TestLib.perr(12ul); SocketError )
                  | SocketError -> TestLib.perr(10ul); SocketError )
              | FileError -> TestLib.perr(9ul); SocketError )
          ) else (
             TestLib.perr(8ul); SocketError ) )
      | SocketError -> SocketError )

                 
val file_recv_loop:
  fb:fh_ref ->
  lb:socket_ref ->
  connb:socket_ref ->
  state: uint8_p{length state = 1244} ->
  Stack sresult
    (requires (fun h -> True))
    (ensures  (fun h0 _ h1 -> True))
let rec file_recv_loop fb lhb connb state =
  push_frame();
  let sid   = Buffer.sub state 96ul 16ul in
  let hsbuf   = Buffer.sub state 112ul 8ul in
  let fname   = Buffer.sub state 120ul 100ul in
  let header  = Buffer.sub state 220ul 1024ul in
  let pkA   = Buffer.sub state 0ul 32ul in
  let pkB   = Buffer.sub state 32ul 32ul in
  let pk1 = Buffer.create zero_8 32ul in
  let pk2 = Buffer.create zero_8 32ul in
  let res =
  match tcp_accept lhb connb with
  | SocketOk -> (
      let c1 = C.clock() in
      (match tcp_read_all connb sid 16uL with
      | SocketOk -> (
          (* JK: no check on the streamID formatting *)
          match tcp_read_all connb hsbuf 8uL with
          | SocketOk -> (
	      let hsize = load64_le hsbuf in
              match tcp_read_all connb pk1 32uL with
              | SocketOk -> (
                  match tcp_read_all connb pk2 32uL with
                  | SocketOk -> (
                      if U8 (memcmp pk1 pkA 32ul =^ 0xffuy) then (
                         if U8 (memcmp pk2 pkB 32ul =^ 0xffuy) then (
			   let _ = file_recv_enc fb connb state hsize 
			   in SocketOk)
			 else TestLib.perr(7ul); SocketError )
                      else TestLib.perr(6ul); SocketError )
                  | SocketError -> TestLib.perr(5ul); SocketError )
              | SocketError -> TestLib.perr(4ul); SocketError )
          | SocketError -> TestLib.perr(3ul); SocketError )
      | SocketError -> TestLib.perr(2ul); SocketError ))
  | SocketError -> TestLib.perr(1ul); SocketError in
  pop_frame();
  match res with
  | SocketOk -> file_recv_loop  fb lhb connb state
  | SocketError -> TestLib.perr(0ul); SocketError


(* post-condition should be:
			             let fs = s.fs in
				     let sidb = s.sid in
				     let pA = as_seq h0 pkA in
				     let pB = pubKey (as_seq h0 skB) in
				     let sid = as_seq h0 sidb in
				     sent h0 pA pB sid fs (file_content h1 fs)
*)

val file_recv: port:u32 -> 
    	   pkA:publicKey{frameOf pkA = input_rgn} -> 
	   skB:privateKey {frameOf skB = input_rgn /\ disjoint pkA skB} -> 
	   Stack open_result
       	   (requires (fun h -> live h pkA /\ live h skB))
	   (ensures  (fun h0 s h1 -> match s.r with
      	   	                   | FileOk -> true				     
				   | _ -> true))
let file_recv p pkA skB =
  push_frame();
  (* Initialization of the file_handle *)
  let fb = Buffer.rcreate file_rgn (init_file_handle(dummy_ptr)) 1ul in
  let fh = fb.(0ul) in
  let state = Buffer.create zero_8 1244ul  in
  let pkA_cpy  = Buffer.sub state 0ul 32ul in
  let pkB   = Buffer.sub state 32ul 32ul in
  let key   = Buffer.sub state 64ul 32ul in
  let sid   = Buffer.sub state 96ul 16ul in
  let hsbuf   = Buffer.sub state 112ul 8ul in
  let fname   = Buffer.sub state 120ul 100ul in
  let header  = Buffer.sub state 220ul 1024ul in
  blit pkA 0ul pkA_cpy 0ul 32ul;
  getPublicKey skB pkB;
  let keygen_res = U32 (crypto_box_beforenm key pkA skB =^ 0ul) in

  (* Initialization of the two sockets *)
  let s = init_socket() in
  let lb = Buffer.rcreate socket_rgn s 1ul in
  let sb = Buffer.rcreate socket_rgn s 1ul in
  let res = (match tcp_listen p lb sb with
  | SocketOk -> (
      match file_recv_loop fb sb state with
      | SocketOk -> opened FileOk fh.stat sid
      | SocketError -> opened FileError fh.stat sid )
  | SocketError -> opened FileError fh.stat sid ) in
  pop_frame();
  res
