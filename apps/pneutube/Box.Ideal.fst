module Box.Ideal

open FStar.HyperStack.All

module ST = FStar.HyperStack.ST

open FStar.Seq
open FStar.Buffer
open FStar.ST
open Hacl.Constants
open Libsodium

module U64 = FStar.UInt64
module H64 = Hacl.UInt64


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

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
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"


type publicKey     = l:uint8_p{length l = 32}
type nonce	   = l:uint8_p{length l = 24}

type privateKey    = l:uint8_p{length l = 32}
type symmetricKey  = l:uint8_p{length l = 32}

val cipherlen: nat -> Tot nat
let cipherlen m = m + 16

assume val pubKey: sk:seq h8 -> GTot (pk:seq u8)
assume val agreedKey: pkA: seq u8 -> pkB: seq u8 -> GTot (k: seq u8)
assume val boxed: FStar.HyperStack.mem ->
       	   	  pkA:seq u8 ->
		  pkB:seq u8 ->
		  m:  seq h8 ->
		  n:  seq h8 ->
		  GTot bool

val randombytes_buf:
  b:uint8_p ->
  blen:u64{length b >= U64.v blen} ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b))
let randombytes_buf b l =
    Libsodium.randombytes_buf b l


val genPrivateKey:
    sk:privateKey ->
    Stack unit
    (requires (fun h -> live h sk))
    (ensures  (fun h0 _ h1 -> live h1 sk /\ modifies_1 sk h0 h1))
let genPrivateKey sk =
    Libsodium.randombytes_buf sk 32uL


val getPublicKey:
    sk:privateKey ->
    pk:publicKey{disjoint sk pk} ->
    Stack unit
    (requires (fun h -> live h pk /\ live h sk))
    (ensures  (fun h0 _ h1 -> live h0 sk /\ live h1 pk /\ modifies_1 pk h0 h1
      /\ as_seq h1 pk == pubKey (as_seq h0 sk)))
let getPublicKey sk pk =
  let hinit = ST.get() in
  push_frame();
  let basepoint = create (Hacl.Cast.uint8_to_sint8 0uy) 32ul in
  basepoint.(0ul) <- (Hacl.Cast.uint8_to_sint8 9uy);
  Curve25519.crypto_scalarmult pk sk basepoint;
  pop_frame();
  let hfin = ST.get() in
  assume (as_seq hfin pk == pubKey (as_seq hinit sk))


(* val crypto_box_beforenm: *)
(*   k:symmetricKey -> *)
(*   pk:publicKey{disjoint k pk} -> *)
(*   sk:privateKey{disjoint k sk /\ disjoint sk pk} -> *)
(*   Stack u32 *)
(*     (requires (fun h -> live h k /\ live h pk /\ live h sk)) *)
(*     (ensures  (fun h0 _ h1 -> modifies_1 k h0 h1 /\ live h1 k /\ live h0 sk /\ live h0 pk *)
(*     	      	      	/\ (let pkA = pubKey (as_seq h0 sk) in *)
(* 			 let pkB = as_seq h0 pk in *)
(* 			 as_seq h1 k == agreedKey pkA pkB))) *)
(* let crypto_box_beforenm k pk sk = *)
(*   let h0 = ST.get() in *)
(*   let r = NaCl.crypto_box_beforenm k pk sk in *)
(*   let h1 = ST.get() in *)
(*   assume (let pkA = pubKey (as_seq h0 sk) in *)
(* 			 let pkB = as_seq h0 pk in *)
(* 			 as_seq h1 k == agreedKey pkA pkB); *)
(*   r *)


(* val crypto_box_easy_afternm: *)
(*   #pkA:uint8_p -> *)
(*   #pkB:uint8_p -> *)
(*   c:uint8_p -> *)
(*   m:uint8_p -> *)
(*   mlen:u64 -> *)
(*   n:nonce -> *)
(*   k:symmetricKey -> *)
(*   Stack UInt32.t *)
(*     (requires (fun h -> live h c /\ live h m /\ live h n /\ live h k /\ *)
(*     	                (let len = U64.v mlen in *)
(* 			 let spkA = as_seq h pkA in *)
(* 			 let spkB = as_seq h pkB in *)
(*     	      	        as_seq h k == agreedKey spkA spkB /\ *)
(*            		 len <= length m /\ *)
(* 	   		 cipherlen len = length c))) *)
(*     (ensures  (fun h0 z h1 -> modifies_1 c h0 h1 /\ live h1 c /\ live h0 n /\ live h0 m /\ *)
(*     	      	      	      boxed h1 (as_seq h0 pkA) (as_seq h0 pkB) (as_seq h0 m) (as_seq h0 n))) *)
(* let crypto_box_easy_afternm #pkA #pkB c m l n k = *)
(*   let h0 = ST.get() in *)
(*   let x = NaCl.crypto_box_easy_afternm c m l n k in *)
(*   let h1 = ST.get() in *)
(*   assume (boxed h1 (as_seq h0 pkA) (as_seq h0 pkB) (as_seq h0 m) (as_seq h0 n)); *)
(*   x *)

(* val crypto_box_open_easy_afternm: *)
(*   #pkA:uint8_p -> *)
(*   #pkB:uint8_p -> *)
(*   m:uint8_p -> *)
(*   c:uint8_p -> *)
(*   clen:u64 -> *)
(*   n:nonce -> *)
(*   k:symmetricKey -> *)
(*   Stack UInt32.t *)
(*     (requires (fun h -> live h c /\ live h m /\ live h n /\ live h k /\ *)
(*     	                (let len = U64.v clen in *)
(* 			 let spkA = as_seq h pkA in *)
(* 			 let spkB = as_seq h pkB in *)
(*    			 as_seq h k == agreedKey spkA spkB /\ *)
(*            		 len = length c /\ len = length m + 16))) *)
(*     (ensures  (fun h0 z h1 -> modifies_1 m h0 h1 /\ live h1 m /\ live h0 n *)
(*     	      	      	    /\ U64.v clen = cipherlen (length m) *)
(* 			    /\ boxed h0 (as_seq h0 pkA) (as_seq h0 pkB) (as_seq h1 m) (as_seq h0 n))) *)
(* let crypto_box_open_easy_afternm #pkA #pkB m c l n k = *)
(*   let h0 = ST.get() in *)
(*   let x = NaCl.crypto_box_open_easy_afternm m c l n k in *)
(*   let h1 = ST.get() in *)
(*   assume (boxed h0 (as_seq h0 pkA) (as_seq h0 pkB) (as_seq h1 m) (as_seq h0 n)); *)
(*   x *)
