module Box.Ideal

open FStar.Seq
open FStar.Buffer
open FStar.ST
open Hacl.Constants
open Libsodium
module U64 = FStar.UInt64

type publicKey     = l:uint8_p{length l = 32}
type nonce	   = l:uint8_p{length l = 24}

private type privateKey    = l:uint8_p{length l = 32}
private type symmetricKey  = l:uint8_p{length l = 32}

val cipherlen: nat -> Tot nat
let cipherlen m = m + 16

assume val pubKey: sk:seq h8 -> GTot (pk:seq h8)
assume val agreedKey: pkA: seq h8 -> pkB: seq h8 -> GTot (k: seq h8)
assume val boxed: FStar.HyperStack.mem -> 
       	   	  pkA:seq h8 ->
		  pkB:seq h8 ->
		  m:  seq h8 ->
		  n:  seq h8 ->
		  GTot bool

val randombytes_buf:
  b:uint8_p ->
  blen:u64 ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ 
    	      	      	      live h1 b /\ 
			      length b = U64.v blen))
let randombytes_buf b l = 
    Libsodium.randombytes_buf b l

val genPrivateKey:
    sk:privateKey ->
    Stack unit
    (requires (fun h -> live h sk))
    (ensures  (fun h0 _ h1 -> live h1 sk /\ modifies_1 sk h0 h1))
let genPrivateKey sk = 
    Libsodium.randombytes_buf sk (U64.uint_to_t 32)
  
val getPublicKey: 
    sk:privateKey ->
    pk:publicKey -> 
    Stack unit
    (requires (fun h -> live h pk /\ live h sk /\
    	      	     	disjoint sk pk))
    (ensures  (fun h0 _ h1 -> modifies_1 pk h0 h1 /\	
    	      	        as_seq h1 pk = pubKey (as_seq h0 sk)))
let getPublicKey sk pk = 
    let basepoint = create (Hacl.Cast.uint8_to_sint8 0uy) 32ul in
    basepoint.(0ul) <- (Hacl.Cast.uint8_to_sint8 9uy);
    Hacl.EC.Curve25519.exp pk basepoint sk

val crypto_box_beforenm:
  k:symmetricKey ->
  pk:publicKey -> 
  sk:privateKey ->
  Stack u32
    (requires (fun h -> live h k /\ live h pk /\ live h sk /\
    	      	     	disjoint k pk /\ disjoint k sk))
    (ensures  (fun h0 _ h1 -> modifies_1 k h0 h1 /\
    	      	      	(let pkA = pubKey (as_seq h0 sk) in
			 let pkB = as_seq h0 pk in
			 as_seq h1 k = agreedKey pkA pkB)))
let crypto_box_beforenm k pk sk = 
    Hacl.Box.crypto_box_beforenm k pk sk

val crypto_box_easy_afternm:
  #pkA:seq h8 ->
  #pkB:seq h8 ->
  c:uint8_p ->
  m:uint8_p ->
  mlen:u64 -> 
  n:nonce ->
  k:symmetricKey ->
  Stack unit
    (requires (fun h -> live h c /\ live h m /\ live h n /\ live h k /\
    	      	        as_seq h k = agreedKey pkA pkB /\
    	                (let len = U64.v mlen in 
           		 len <= length m /\ 
	   		 cipherlen len = length c)))
    (ensures  (fun h0 z h1 -> modifies_1 c h0 h1 /\ live h1 c /\
    	      	      	      boxed h1 pkA pkB (as_seq h0 m) (as_seq h0 n)))
let crypto_box_easy_afternm #pkA #pkB c m l n k = 
    let _ = Hacl.Box.crypto_box_easy_afternm c m l n k in
    ()

val crypto_box_open_easy_afternm:
  #pkA:seq h8 ->
  #pkB:seq h8 ->
  m:uint8_p ->
  c:uint8_p ->
  clen:u64 -> 
  n:nonce ->
  k:symmetricKey ->
  Stack unit
    (requires (fun h -> live h c /\ live h m /\ live h n /\ live h k /\
    	      	        as_seq h k = agreedKey pkA pkB /\
    	                (let len = U64.v clen in 
           		 len = length c)))
    (ensures  (fun h0 z h1 -> modifies_1 m h0 h1 /\ live h1 m /\	
    	      	      	      U64.v clen = cipherlen (length m)/\
			      boxed h0 pkA pkB (as_seq h1 m) (as_seq h0 n)))
let crypto_box_open_easy_afternm #pkA #pkB m c l n k = 
    let _ = Libsodium.crypto_box_open_easy_afternm m c l n k in
    ()
