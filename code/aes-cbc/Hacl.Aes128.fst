module Hacl.Aes128

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

// FIPS197 ?
// TODO factor it out in terms of https://en.wikipedia.org/wiki/AES_instruction_set
// see also https://software.intel.com/sites/default/files/article/165683/aes-wp-2012-09-22-v01.pdf

// TODO this is AES256; 
// we also need AES128 (nk=4ul, nr=10) and maybe AES192 (nk=6ul,nr=12).

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

open Hacl.Impl.Aes128

val xor_block: out:block -> in1:block -> in2:block -> start:U32.t{U32.v start <= 16} -> Stack unit
    (requires (fun h0 -> True))
    (ensures (fun h0 _ h1 -> True))
let rec xor_block out in1 in2 start = 
    if start = 16ul then ()
    else (out.(start) <- U8.(in1.(start) ^^ in2.(start));
	  xor_block out in1 in2 U32.(start +^ 1ul))
     
    
val cbc_encrypt_blocks: out:bytes -> kex:xkey -> prev:block -> msg:bytes{B.length msg == B.length out} -> len:U32.t ->  curr:U32.t{U32.v curr <= U32.v len} -> tmp:block -> Stack unit
    (requires (fun h0 -> True))
    (ensures (fun h0 _ h1 -> True))
let rec cbc_encrypt_blocks out kex prev msg len curr tmp = 
  if curr <> len then ()
  else 
    let mblock = B.sub msg curr 16ul in
    let oblock = B.sub out curr 16ul in
    xor_block tmp mblock prev 0ul;
    cipher oblock tmp kex;
    cbc_encrypt_blocks out kex oblock msg len U32.(curr +^ 16ul) tmp

val pad: tmp:block -> b:U8.t -> idx:U32.t{U32.v idx <= 16} -> Stack unit
	 (requires (fun h -> True))
	 (ensures (fun h0 _ h1 -> True))
let rec pad tmp b idx = 
    if idx = 16ul then ()
    else (tmp.(idx) <- b; pad tmp b U32.(idx +^ 1ul))
    
let aes128_cbc_encrypt out key iv msg msglen = 
  push_frame();
  assert (U32.v 16ul <> 0);
  let fullblocks = U32.((msglen /^ 16ul) *^ 16ul) in
  let final = U32.(msglen %^ 16ul) in
  let msg1 = B.sub msg 0ul fullblocks in
  let last = B.sub msg fullblocks final in
  let out1 = B.sub out 0ul fullblocks in
  let out2 = B.sub out fullblocks final in
  let kex = B.alloca 0uy xkeylen in
  let tmp = B.alloca 0uy 16ul in
  let otmp = B.alloca 0uy 16ul in
  keyExpansion key kex;
  cbc_encrypt_blocks out1 kex iv msg1 fullblocks 0ul tmp;
  if (final <> 0ul) then 
     let lastfull = if (fullblocks <> 0ul) then B.sub out1 U32.(fullblocks -^ 16ul) 16ul 
		    else iv in (
     blit last 0ul tmp 0ul final;
     pad tmp (uint32_to_uint8 U32.(16ul -^ final)) U32.(16ul -^ final);
       xor_block tmp tmp lastfull 0ul;
       cipher otmp tmp kex;
       blit otmp 0ul out2 0ul final
       )
  else ();
  pop_frame()

val cbc_decrypt_blocks: out:bytes -> kex:xkey -> prev:block -> cip:bytes{B.length cip == B.length out} -> len:U32.t ->  curr:U32.t{U32.v curr <= U32.v len} -> tmp:block -> Stack unit
    (requires (fun h0 -> True))
    (ensures (fun h0 _ h1 -> True))
let rec cbc_decrypt_blocks out kex prev cip len curr tmp = 
  if curr <> len then ()
  else 
    let cblock = B.sub cip curr 16ul in
    let oblock = B.sub out curr 16ul in
    inv_cipher tmp cblock kex;
    xor_block oblock tmp prev 0ul;
    cbc_decrypt_blocks out kex cblock cip len U32.(curr +^ 16ul) tmp

let aes128_cbc_decrypt out key iv cip ciplen = 
  push_frame();
  assert (U32.v 16ul <> 0);
  let fullblocks = U32.(ciplen -^ 16ul) in
  let final = 16ul in
  let cip1 = B.sub cip 0ul fullblocks in
  let last = B.sub cip fullblocks final in
  let out1 = B.sub out 0ul fullblocks in
  let out2 = B.sub out fullblocks final in
  let kex = B.alloca 0uy xkeylen in
  let tmp = B.alloca 0uy 16ul in
  let otmp = B.alloca 0uy 16ul in
  keyExpansion key kex;
  cbc_decrypt_blocks out1 kex iv cip1 fullblocks 0ul tmp;
  inv_cipher tmp last kex;
  let lastfull = if (fullblocks <> 0ul) then B.sub cip1 U32.(fullblocks -^ 16ul) 16ul 
   	         else iv in 
  xor_block otmp tmp lastfull 0ul;
  let pad = otmp.(15ul) in
  blit otmp 0ul out2 0ul U32.(16ul -^ (uint8_to_uint32 pad));
  pop_frame()
  

