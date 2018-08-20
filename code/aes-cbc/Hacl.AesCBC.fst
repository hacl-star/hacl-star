module Hacl.AesCBC

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.UInt8
open FStar.Int.Cast
open LowStar.Buffer
module B = LowStar.Buffer

(* Module abbreviations *)
module HS = FStar.HyperStack

module U8  = FStar.UInt8
module U32 = FStar.UInt32
module H8  = FStar.UInt8
module H32  = FStar.UInt32

open Hacl.Impl.Aes

val xor_block: out:block -> in1:block -> in2:block -> start:U32.t{U32.v start <= U32.v blocklen} -> Stack unit
    (requires (fun h0 -> live h0 in1 /\ live h0 in2 /\ live h0 out))
    (ensures (fun h0 _ h1 -> True))
let rec xor_block out in1 in2 start = 
    if start = blocklen then ()
    else (out.(start) <- U8.(in1.(start) ^^ in2.(start));
	  xor_block out in1 in2 U32.(start +^ 1ul))
     
    
val cbc_encrypt_blocks: out:bytes -> kex:xkey -> prev:block -> msg:bytes{B.length msg == B.length out} -> len:U32.t{B.length msg == U32.v len}  ->  curr:U32.t{U32.v curr <= U32.v len} -> tmp:block -> Stack unit
    (requires (fun h0 -> live h0 out /\ live h0 prev /\ live h0 msg /\ live h0 tmp))
    (ensures (fun h0 _ h1 -> True))
let rec cbc_encrypt_blocks out kex prev msg len curr tmp = 
  if curr = len then ()
  else (
    let mblock = B.sub msg curr 16ul in
    let oblock = B.sub out curr 16ul in
    xor_block tmp mblock prev 0ul;
    cipher oblock tmp kex;
    cbc_encrypt_blocks out kex oblock msg len U32.(curr +^ 16ul) tmp
  )
  
val padPKCS: tmp:block -> len:U32.t{U32.v len <= U32.v blocklen} -> idx:U32.t{U32.v idx <= U32.v blocklen} -> Stack unit
	 (requires (fun h -> True))
	 (ensures (fun h0 _ h1 -> True))
let rec padPKCS tmp len idx = 
    if idx = blocklen then ()
    else (tmp.(idx) <- uint32_to_uint8 len; padPKCS tmp len U32.(idx +^ 1ul))

val padISO: tmp:block -> len:U32.t{U32.v len <= 16} -> idx:U32.t{U32.v idx <= 16} -> Stack unit
	 (requires (fun h -> live h tmp /\ B.length tmp == 16))
	 (ensures (fun h0 _ h1 -> True))
let padISO tmp b idx = 
    tmp.(idx) <- 0x80uy

inline_for_extraction let pad tmp len idx = padPKCS tmp len idx

let aes256_cbc_encrypt out key iv msg msglen = 
  push_frame();
  assert (U32.v 16ul <> 0);
  let fullblocks = U32.((msglen /^ 16ul) *^ 16ul) in
  let final = U32.(msglen %^ 16ul) in
  let msg1 = B.sub msg 0ul fullblocks in
  let last = B.sub msg fullblocks final in
  let out1 = B.sub out 0ul fullblocks in
  let out2 = B.sub out fullblocks 16ul in
  let kex = B.alloca 0uy xkeylen in
  let tmp = B.alloca 0uy 16ul in
  let otmp = B.alloca 0uy 16ul in
  keyExpansion key kex;
  cbc_encrypt_blocks out1 kex iv msg1 fullblocks 0ul tmp;
  let lastfull = if (fullblocks <> 0ul) then B.sub out1 U32.(fullblocks -^ 16ul) 16ul 
                 else iv in 
  let ltmp = B.alloca 0uy 16ul in
  blit last 0ul ltmp 0ul final;
  pad ltmp U32.(16ul -^ final) final;
  xor_block ltmp ltmp lastfull 0ul;
  cipher otmp ltmp kex;
  blit otmp 0ul out2 0ul 16ul;
  pop_frame()


let aes256_cbc_encrypt_no_pad out key iv msg msglen = 
  push_frame();
  assert (U32.v 16ul <> 0);
  let kex = B.alloca 0uy xkeylen in
  let tmp = B.alloca 0uy 16ul in
  keyExpansion key kex;
  cbc_encrypt_blocks out kex iv msg msglen 0ul tmp;
  pop_frame()

val cbc_decrypt_blocks: out:bytes -> kex:xkey -> prev:block -> cip:bytes{B.length cip == B.length out} -> len:U32.t ->  curr:U32.t{U32.v curr <= U32.v len} -> tmp:block -> Stack unit
    (requires (fun h0 -> True))
    (ensures (fun h0 _ h1 -> True))
let rec cbc_decrypt_blocks out kex prev cip len curr tmp = 
  if curr = len then ()
  else (
    let cblock = B.sub cip curr 16ul in
    let oblock = B.sub out curr 16ul in
    inv_cipher tmp cblock kex;
    xor_block oblock tmp prev 0ul;
    cbc_decrypt_blocks out kex cblock cip len U32.(curr +^ 16ul) tmp
  )


val unpadPKCS: tmp:block -> idx:U32.t{U32.v idx <= U32.v blocklen} -> Stack (len:U32.t{U32.v len <= U32.v blocklen})
	 (requires (fun h -> live h tmp))
	 (ensures (fun h0 _ h1 -> True))
let rec unpadPKCS tmp idx = 
  let pad = tmp.(U32.(blocklen -^ 1ul)) in
  let pad32 = uint8_to_uint32 pad in
  if U32.(pad32 <=^ blocklen) then pad32
  else 0ul

val unpadISO: tmp:block ->  idx:U32.t{U32.v idx < U32.v blocklen} -> Stack (len:U32.t{U32.v len < U32.v blocklen})
	 (requires (fun h -> live h tmp))
	 (ensures (fun h0 _ h1 -> True))
let rec unpadISO tmp idx = 
    let t = tmp.(idx) in
   if t = 0x80uy then idx 
   else if t <> 0x00uy then 0ul
   else if idx = 0x0ul then 0ul
   else unpadISO tmp U32.(idx -^ 1ul)

      

inline_for_extraction let unpad tmp idx = unpadPKCS tmp idx


let aes256_cbc_decrypt out key iv cip ciplen = 
  push_frame();
  let kex = B.alloca 0uy xkeylen in
  let tmp = B.alloca 0uy 16ul in
  keyExpansion key kex;
  cbc_decrypt_blocks out kex iv cip ciplen 0ul tmp;
  let pad = U32.(out.(ciplen -^ 1ul)) in
  let pad32 = uint8_to_uint32 pad in
  let msglen = U32.(ciplen -^ pad32) in
  pop_frame();
  msglen

let aes256_cbc_decrypt_no_pad out key iv cip ciplen = 
  push_frame();
  let kex = B.alloca 0uy xkeylen in
  let tmp = B.alloca 0uy 16ul in
  keyExpansion key kex;
  cbc_decrypt_blocks out kex iv cip ciplen 0ul tmp;
  pop_frame();
  ciplen
