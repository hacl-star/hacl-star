module Hacl.Tube


open FStar.Seq
open FStar.Buffer
open FileIO.Types
open PaddedFileIO
open SocketIO
open Hacl.Constants
open Hacl.Cast
open Box.Ideal

module  U8=FStar.UInt8
module U32=FStar.UInt32
module U64=FStar.UInt64

module  H8=Hacl.UInt8
module H32=Hacl.UInt32
module H64=Hacl.UInt64


#set-options "--lax"

(* JK: Putting here some toplevel constant *)
inline_for_extraction let blocksize_bits = 18ul
inline_for_extraction let blocksize = U64 (256uL *^ 1024uL) //1uL <<^ blocksize_bits) // 256 * 1024
inline_for_extraction let blocksize_32 = U32 (256ul *^ 1024ul) //(1ul <<^ blocksize_bits) // 256 * 1024
inline_for_extraction let cipherlen (x:U64.t)  = U64 (x +^ 16uL)
inline_for_extraction let cipherlen_32 (x:U32.t) = U32 (x +^ 16ul)
inline_for_extraction let ciphersize = cipherlen (blocksize)
inline_for_extraction let ciphersize_32 = cipherlen_32 (blocksize_32)
inline_for_extraction let headersize = 1024uL
inline_for_extraction let headersize_32 = 1024ul

inline_for_extraction let one_64  = Hacl.Cast.uint64_to_sint64 1uL
inline_for_extraction let zero_64 = Hacl.Cast.uint64_to_sint64 0uL
inline_for_extraction let one_8  = Hacl.Cast.uint8_to_sint8 1uy
inline_for_extraction let zero_8 = Hacl.Cast.uint8_to_sint8 0uy


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


(* JK: move to a standard library ? Or use the string library ? *)
val strlen_: s:str -> len:U32.t ->
  Stack U32.t
    (requires (fun h -> live h s)) // Also assumes that the '0uy' will appears somewhere
    (ensures (fun h0 r h1 -> h0==h1 /\ U32.v r <= length s))
let rec strlen_ s len =
  let si = s.(len) in
  if U8 (si =^ 0uy) then len
  else strlen_ s (U32 (len +^ 1ul))

val strlen:
  string:str -> Stack U32.t
    (requires (fun h -> live h string)) // Also assumes that the '0uy' will appears somewhere
    (ensures (fun h0 r h1 -> h0==h1 /\ U32.v r <= length string))
let strlen s = strlen_ s 0ul

type timespec = {
  tv_sec: U64.t;
  tv_nsec: U64.t;
}


assume val clock_gettime: unit -> St timespec


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



val file_send_loop:
  fh:buffer file_handle{length fh = 1} ->
  sb:buffer socket{length sb = 1} ->
  ciphertext:uint8_p{Buffer.length ciphertext = U64.v blocksize} ->
  nonce:uint8_p{Buffer.length nonce = 24} ->
  key:uint8_p{Buffer.length key = 24} ->
  seqno:H64.t ->
  len:U64.t ->
  Stack sresult
    (requires (fun h -> live h fh /\ live h sb /\ live h ciphertext /\ live h nonce
      /\ live h key))
    (ensures  (fun h0 _ h1 -> True))
let rec file_send_loop fh sb ciphertext nonce key seqno len =
  if U64 (len =^ 0uL) then SocketOk
  else (
    let i = U64 (len -^ 1uL) in
    let next = file_next_read_buffer fh blocksize in
    store64_le (sub nonce 16ul 8ul) seqno;
    let seqno = H64 (seqno +^ Hacl.Cast.uint64_to_sint64 1uL) in
    let _ = Hacl.Box.crypto_box_easy_afternm ciphertext next blocksize nonce key in
    match tcp_write_all sb ciphertext ciphersize with
    | SocketOk -> file_send_loop fh sb ciphertext nonce key seqno i
    | SocketError -> SocketError
  )


val file_send_loop_2:
  fh:buffer file_handle{length fh = 1} ->
  sb:buffer socket{length sb = 1} ->
  ciphertext:uint8_p{Buffer.length ciphertext = U64.v blocksize} ->
  plaintext:uint8_p{Buffer.length plaintext = U64.v blocksize} ->
  nonce:uint8_p{Buffer.length nonce = 24} ->
  key:uint8_p{Buffer.length key = 24} ->
  len:U64.t ->
  St sresult
let rec file_send_loop_2 fh sb ciphertext plaintext nonce key len =
  if U64 (len =^ 0uL) then SocketOk
  else (
    let i = U64 (len -^ 1uL) in
    let _ = Hacl.Box.crypto_box_easy_afternm ciphertext plaintext blocksize nonce key in
    match tcp_write_all sb ciphertext ciphersize with
    | SocketOk -> file_send_loop_2 fh sb ciphertext plaintext nonce key i
    | SocketError -> SocketError
  )


val file_send:
  file:str -> roundup:u64 ->
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
  (* Initializing all buffers on the stack *)
  let pkA = Buffer.create (Hacl.Cast.uint8_to_sint8 0uy) 32ul in
  let zero = Hacl.Cast.uint8_to_sint8 0uy in
  let nine = Hacl.Cast.uint8_to_sint8 9uy in
  let basepoint = Buffer.createL [
    nine; zero; zero; zero; zero; zero; zero; zero; zero; zero; zero; zero; zero; zero; zero; zero;
    zero; zero; zero; zero; zero; zero; zero; zero; zero; zero; zero; zero; zero; zero; zero; zero
  ] in
  Hacl.EC.Curve25519.exp pkA basepoint skA;

  (* Initialization of the file_handle *)
  let dummy_ptr = FStar.Buffer.create (Hacl.Cast.uint8_to_sint8 0uy) 1ul in
  let fb = Buffer.create (init_file_handle(dummy_ptr)) 1ul in

  (* Initialization of the sessionID *)
  let sid = makeStreamID() in

  let res =
    match (file_open_read_sequential f fb) with
    | FileOk ->
        (* Read file handle value *)
        let fh = fb.(0ul) in
        (* Initialization of the socket *)
        let s = init_socket() in
        let sb = Buffer.create s 1ul in
        (match tcp_connect h p sb with
        | SocketOk ->
	    let s = sb.(0ul) in
            let ciphertext = Buffer.create zero ciphersize_32 in
            let file_size = fh.stat.size in
            (* JK: I assume that blocksize is a power of 2 *)
            (* let fragments = H64 (file_size >>^ blocksize_bits) in *)
            (* let rem = H64 (file_size &^ (blocksize-^one_64)) in *)
            let fragments = U64 (file_size /^ blocksize) in
            let rem = U64 (file_size %^ blocksize) in
            let roundup = Hacl.Cast.uint64_to_sint64 r in
            (* JK: I assume that roundup is a power of 2, otherwise that is wrong *)
            (* let hsize_mod_roundup = H64 (file_size &^ (roundup-^one_64)) in *)
            (* let hsize_mod_roundup = U64 (file_size %^ roundup) in *)
            (* let mask = H64 (gte_mask roundup one_64 &^ (lognot (eq_mask hsize_mod_roundup zero_64))) in *)
            (* let hrem = H64 ((roundup -^ hsize_mod_roundup) &^ mask) in *)
            let hrem  = U64 (if (roundup >^ zero_64) then
              if not ((file_size %^ roundup) =^ 0uL)  then 
                (roundup -^ (file_size %^ roundup)) else 0uL else 0uL) in
            let hsize = H64 (file_size +^ hrem) in
            let mtime = fh.stat.mtime in
            let nsize = strlen f in
            let header = Buffer.create zero_8 headersize_32 in
            (* JK: Omitting memset to 0 for now *)
            store64_le (Buffer.sub header  0ul 8ul) file_size;
            store64_le (Buffer.sub header  8ul 8ul) mtime;
            store64_le (Buffer.sub header 16ul 8ul) (Int.Cast.uint32_to_uint64 nsize);
            (* JK: Ignoring the test on the file name length for convenience *)
            Buffer.blit f 0ul header 24ul nsize;
            (* A buffer to store uint64 values before flushing them *)
            let buf = Buffer.create zero 8ul in
            (* Flush the streamID *)
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
                            let nonce = Buffer.create zero 24ul in
                            let key   = Buffer.create zero 32ul in
                            if U32 (Hacl.Box.crypto_box_beforenm key pkB skA =^ 0ul) then (
                              (* Populating the nonce *)
                              blit sid 0ul nonce 0ul 16ul;
                              store64_le (sub nonce 16ul 8ul) seqno;
                              let seqno = H64 (seqno +^ one_64) in
                              let _ = Hacl.Box.crypto_box_easy_afternm ciphertext header headersize
                                                               nonce key in
                              (match tcp_write_all sb ciphertext (cipherlen headersize) with
                              | SocketOk -> (
                                  (* JK: need to declassify fragmensts *)
                                  match file_send_loop fb sb ciphertext nonce key seqno fragments with
                                  | SocketOk -> (
                                      let plaintext = Buffer.create zero blocksize_32 in
                                      (* JK: Omitting memset to 0 for now *)
                                      // JK: TODO:hrem and rem are secret, need declassification
                                      let rem_dec = rem in
                                      let hrem_dec = hrem in
                                      if U64 ((rem_dec +^ hrem_dec) >^ zero_64) then (
                                        let next = file_next_read_buffer fb rem in
                                        blit next 0ul plaintext 0ul (Int.Cast.uint64_to_uint32 rem);
                                        // Here seqno is 1 (header) + fragments (loop) + 1 (here)
                                        let seqno = (H64 (fragments +^ 1uL)) in
                                        store64_le (sub nonce 16ul 8ul) seqno;
                                        let seqno = H64 (seqno +^ one_64) in
                                        let cond = U64 ((rem_dec +^ hrem_dec) >^ blocksize) in
                                        let rem = if cond then blocksize else H64 (rem +^ hrem) in
                                        let hrem = if cond then H64 (hrem -^ (blocksize -^ rem)) else zero_64 in
                                        let _ = Hacl.Box.crypto_box_easy_afternm ciphertext plaintext rem nonce key in
                                        (match tcp_write_all sb ciphertext (cipherlen rem) with
                                        | SocketOk -> (
                                            if U64 (hrem >^ 0uL) then (
                                              Buffer.fill plaintext zero blocksize_32;
                                              let fragments = U64 (hrem >>^ blocksize_bits) in
                                              let hrem = U64 (hrem &^ (blocksize -^ one_64)) in
                                              (match file_send_loop_2 fb sb ciphertext plaintext nonce key fragments with
                                              | SocketOk ->
                                                  if U64 (hrem >^ 0uL) then (
                                                    let _ = Hacl.Box.crypto_box_easy_afternm ciphertext plaintext hrem nonce key in
                                                    match tcp_write_all sb ciphertext (cipherlen hrem) with
                                                    | SocketOk -> opened FileOk fh.stat sid
                                                    | SocketError -> opened FileError fh.stat sid
                                                  ) else (
                                                    opened FileOk fh.stat sid
                                                  )
                                               | SocketError -> opened FileError fh.stat sid)
                                            ) else (
                                              opened FileOk fh.stat sid
                                            ) )
                                        | SocketError -> opened FileError fh.stat sid)
                                      ) else (
                                        opened FileOk fh.stat sid
                                      ) )
                                  | SocketError -> opened FileError fh.stat sid )
                              | SocketError -> opened FileError fh.stat sid )
                            ) else (
                              opened FileOk fh.stat sid
                            ) )
                        | SocketError -> opened FileError fh.stat sid )
                    | SocketError -> opened FileError fh.stat sid )
                | SocketError -> opened FileError fh.stat sid )
            | SocketError -> opened FileError fh.stat sid ) )
    | FileError -> opened FileError (fb.(0ul)).stat sid in
  pop_frame();
  res


val memcmp_ct_:
  b:uint8_p ->
  b':uint8_p ->
  len:U32.t ->
  tmp:H8.t ->
  Stack U8.t
    (requires (fun _ -> True))
    (ensures  (fun _ _ _ -> True))
let rec memcmp_ct_ b b' len tmp =
  if U32 (len =^ 0ul) then (
    (* JK: Declassification needed *)
    tmp
  ) else (
    let i = U32 (len -^ 1ul) in
    let bi = b.(i) in let bi' = b'.(i) in
    let tmp = U8 (tmp &^ (eq_mask bi bi')) in
    memcmp_ct_ b b' i tmp
  )

(** Constant time comparison function
    Return 0xff if b == b', 0 otherwise **)
val memcmp_ct:
  b:uint8_p ->
  b':uint8_p ->
  len:U32.t ->
  Stack U8.t
    (requires (fun _ -> True))
    (ensures  (fun _ _ _ -> True))
let memcmp_ct b b' len =
  memcmp_ct_ b b' len (Hacl.Cast.uint8_to_sint8 0xffuy)


val get_fh_stat: file_handle -> Tot file_stat
let get_fh_stat fh = fh.stat

val file_recv_loop_2:
  fb:buffer file_handle ->
  connb:buffer socket ->
  ciphertext:uint8_p ->
  nonce:uint8_p ->
  key:uint8_p ->
  seqno:H64.t ->
  len:U64.t ->
  Stack sresult
    (requires (fun _ -> True))
    (ensures  (fun _ _ _ -> True))
let rec file_recv_loop_2 fb connb ciphertext nonce key seqno len =
  if U64 (len =^ 0uL) then SocketOk
  else (
    let i = U64 (len -^ 1uL) in
    match tcp_read_all connb ciphertext ciphersize with
    | SocketOk -> (
        let next = file_next_write_buffer fb blocksize in
        store64_le nonce seqno;
        let seqno = H64 (seqno +^ one_64) in
        if U32 (Hacl.Box.crypto_box_open_easy_afternm next ciphertext ciphersize nonce key =^ 0ul) then
          file_recv_loop_2 fb connb ciphertext nonce key seqno i
        (* JK: not distinguishing between socket error and decryption failure *)
        else SocketError)
    | SocketError -> SocketError
  )


val file_recv_loop:
  fb:buffer file_handle ->
  connb:buffer socket ->
  lhb:buffer socket ->
  sid:uint8_p ->
  pkA:uint8_p ->
  pkB:uint8_p ->
  skB:uint8_p ->
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
      (match tcp_read_all connb (sub nonce 0ul 16ul) 16uL with
      | SocketOk -> (
          (* JK: no check on the streamID formatting *)
          match tcp_read_all connb (sub nonce 16ul 8ul) 8uL with
          | SocketOk -> (
              (* JK: no check on the size *)
              match tcp_read_all connb pk1 32uL with
              | SocketOk -> (
                  match tcp_read_all connb pk2 32uL with
                  | SocketOk -> (
                      if U8 (memcmp_ct pk1 pkA 32ul =^ 0xffuy) then (
                         if U8 (memcmp_ct pk2 pkB 32ul =^ 0xffuy) then (
                           let key = create zero_8 32ul in
                           (* JK: ignoring check on beforenm *)
                           let _ = Hacl.Box.crypto_box_beforenm key pkA skB in
                           let seqno = 0uL in
                           let header = create zero_8 headersize_32 in
                           fill header zero_8 headersize_32;
                           (match tcp_read_all connb ciphertext (cipherlen(headersize)) with
                           | SocketOk -> (
                               store64_le (sub nonce 16ul 8ul) seqno;
                               let seqno = H64 (seqno +^ 1uL) in
                               if U32 (Hacl.Box.crypto_box_open_easy_afternm header ciphertext (cipherlen(headersize)) nonce key =^ 0ul) then (
                                 let file_size = load64_le (sub header 0ul  8ul) in
                                 let nsize     = load64_le (sub header 8ul  8ul) in
                                 let mtime     = load64_le (sub header 16ul 8ul) in
                                 (* JK: no checking the size of the filename *)
                                 (* JK: need declassification on nsize value *)
                                 let file = sub header 24ul (Int.Cast.uint64_to_uint32 nsize) in
                                 let fstat = {name = file; mtime = mtime; size = nsize} in
                                 (match file_open_write_sequential fstat fb with
                                 | FileOk -> (
                                     let fragments = H64 (file_size >>^ blocksize_bits) in
                                     let rem       = H64 (file_size &^ (blocksize -^ one_64)) in
                                     (match file_recv_loop_2 fb connb ciphertext nonce key seqno fragments with
                                     | SocketOk -> (
                                         let res =
                                           if U64 (rem >^ 0uL) then (
                                             match tcp_read_all connb ciphertext (cipherlen(rem)) with
                                             | SocketOk -> (
                                                 let next = file_next_write_buffer fb rem in
                                                 let seqno = U64 (fragments +^ 1uL) in
                                                 if U32 (Hacl.Box.crypto_box_easy_afternm next ciphertext (cipherlen(rem)) nonce key =^ 0ul) then SocketOk
                                                 else (TestLib.perr(15ul); SocketError) )
                                             | SocketError -> TestLib.perr(14ul); SocketError
                                           ) else SocketOk in
                                         match res with
                                         | SocketOk -> (
                                             match file_close fb with
                                             | false -> (
                                                 match tcp_close connb with
                                                 | SocketOk -> SocketOk
                                                 | SocketError -> TestLib.perr(13ul); SocketError )
                                             | true -> TestLib.perr(12ul); SocketError )
                                         | SocketError -> TestLib.perr(11ul); SocketError )
                                     | SocketError -> TestLib.perr(10ul); SocketError ) )
                                 | FileError -> TestLib.perr(9ul); SocketError )
                               ) else (
                                 TestLib.perr(8ul); SocketError ) )
                           | SocketError -> SocketError )
                         ) else (
                           TestLib.perr(7ul); SocketError
                         )
                       ) else (
                         TestLib.perr(6ul); SocketError ) )
                  | SocketError -> TestLib.perr(5ul); SocketError )
              | SocketError -> TestLib.perr(4ul); SocketError )
          | SocketError -> TestLib.perr(3ul); SocketError )
      | SocketError -> TestLib.perr(2ul); SocketError ) )
  | SocketError -> TestLib.perr(1ul); SocketError in
  pop_frame();
  match res with
  | SocketOk -> file_recv_loop  fb connb lhb sid pkA pkB skB
  | SocketError -> TestLib.perr(0ul); SocketError


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
      let pkB = create zero_8 32ul in
      let zero = zero_8 in
      let nine = Hacl.Cast.uint8_to_sint8 9uy in
      let basepoint = Buffer.createL [
        nine; zero; zero; zero; zero; zero; zero; zero; zero; zero; zero; zero; zero; zero; zero; zero;
        zero; zero; zero; zero; zero; zero; zero; zero; zero; zero; zero; zero; zero; zero; zero; zero
      ] in
      Hacl.EC.Curve25519.exp pkB basepoint skB;
      match file_recv_loop fb connb lhb sid pkA pkB skB with
      | SocketOk -> opened FileOk fh.stat sid
      | SocketError -> opened FileError fh.stat sid )
  | SocketError -> opened FileError fh.stat sid ) in
  pop_frame();
  res
