module Hacl.AesCBC

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open LowStar.Buffer
open Hacl.Impl.Aes

val xor_block: out:block -> in1:block -> in2:block -> start:size_t{size_v start <= blocklen} -> Stack unit
    (requires (fun h0 -> live h0 in1 /\ live h0 in2 /\ live h0 out))
    (ensures (fun h0 _ h1 -> True))
let rec xor_block out in1 in2 start = 
    if start = size blocklen then ()
    else (out.(start) <- FStar.UInt8.(in1.(start) ^^ in2.(start));
	  xor_block out in1 in2 (start +. size 1))
     
    
val cbc_encrypt_blocks: out:bytes -> kex:keyex -> prev:block -> msg:bytes{length msg == length out} -> len:size_t{length msg == size_v len}  ->  curr:size_t{size_v curr <= size_v len} -> tmp:block -> Stack unit
    (requires (fun h0 -> live h0 out /\ live h0 prev /\ live h0 msg /\ live h0 tmp))
    (ensures (fun h0 _ h1 -> True))
let rec cbc_encrypt_blocks out kex prev msg len curr tmp = 
  if curr = len then ()
  else (
    let mblock = sub msg curr (size 16) in
    let oblock = sub out curr (size 16) in
    xor_block tmp mblock prev (size 0);
    encipher oblock tmp kex;
    cbc_encrypt_blocks out kex oblock msg len (curr +. size 16) tmp
  )
  
val padPKCS: tmp:block -> len:size_t{size_v len <= blocklen} -> idx:size_t{size_v idx <= blocklen} -> Stack unit
	 (requires (fun h -> True))
	 (ensures (fun h0 _ h1 -> True))
let rec padPKCS tmp len idx = 
    if idx = size blocklen then ()
    else (tmp.(idx) <- Lib.RawIntTypes.u8_to_UInt8 (to_u8 len); padPKCS tmp len (idx +. size 1))

val padISO: tmp:block -> len:size_t{size_v len <= 16} -> idx:size_t{size_v idx <= 16} -> Stack unit
	 (requires (fun h -> live h tmp /\ length tmp == 16))
	 (ensures (fun h0 _ h1 -> True))
let padISO tmp b idx = 
    tmp.(idx) <- 0x80uy

inline_for_extraction let pad tmp len idx = padPKCS tmp len idx

let aes256_cbc_encrypt out key iv msg msglen = 
  push_frame();
  let fullblocks = ((msglen /. size 16) *. size 16) in
  let final = msglen %. size 16 in
  let msg1 = sub msg (size 0) fullblocks in
  let last = sub msg fullblocks final in
  let out1 = sub out (size 0) fullblocks in
  let out2 = sub out fullblocks (size 16) in
  let kex = alloca (u64 0) 88ul in
  let tmp = alloca 0uy 16ul in
  let otmp = alloca 0uy 16ul in
  key_expansion kex key;
  cbc_encrypt_blocks out1 kex iv msg1 fullblocks (size 0) tmp;
  let lastfull = if (fullblocks <> 0ul) then sub out1 (fullblocks -. size 16) (size 16)
                 else iv in 
  let ltmp = alloca 0uy 16ul in
  blit last (size 0) ltmp (size 0) final;
  pad ltmp (size 16 -. final) final;
  xor_block ltmp ltmp lastfull (size 0);
  encipher otmp ltmp kex;
  blit otmp (size 0) out2 (size 0) (size 16);
  pop_frame()


let aes256_cbc_encrypt_no_pad out key iv msg msglen = 
  push_frame();
  let kex = alloca (u64 0) 88ul in
  let tmp = alloca 0uy 16ul in
  key_expansion kex key;
  cbc_encrypt_blocks out kex iv msg msglen (size 0) tmp;
  pop_frame()

val cbc_decrypt_blocks: out:bytes -> kex:keyex -> prev:block -> cip:bytes{length cip == length out} -> len:size_t ->  curr:size_t{size_v curr <= size_v len} -> tmp:block -> Stack unit
    (requires (fun h0 -> True))
    (ensures (fun h0 _ h1 -> True))
let rec cbc_decrypt_blocks out kex prev cip len curr tmp = 
  if curr = len then ()
  else (
    let cblock = sub cip curr (size 16) in
    let oblock = sub out curr (size 16) in
    decipher tmp cblock kex;
    xor_block oblock tmp prev (size 0);
    cbc_decrypt_blocks out kex cblock cip len (curr +. size 16) tmp
  )


val unpadPKCS: tmp:block -> idx:size_t{size_v idx <= blocklen} -> Stack (len:size_t{size_v len <= blocklen})
	 (requires (fun h -> live h tmp))
	 (ensures (fun h0 _ h1 -> True))
let rec unpadPKCS tmp idx = 
  let pad = tmp.(size blocklen -. size 1) in
  let pad32 = Lib.RawIntTypes.size_from_UInt32 (FStar.Int.Cast.uint8_to_uint32 pad) in
  if pad32 <=. size blocklen then pad32
  else size 0

val unpadISO: tmp:block ->  idx:size_t{size_v idx < blocklen} -> Stack (len:size_t{size_v len < blocklen})
	 (requires (fun h -> live h tmp))
	 (ensures (fun h0 _ h1 -> True))
let rec unpadISO tmp idx = 
   let t = tmp.(idx) in
   if t = 0x80uy then idx 
   else if t <> 0x00uy then size 0
   else if idx = size 0 then size 0
   else unpadISO tmp (idx -. size 1)

      

inline_for_extraction let unpad tmp idx = unpadPKCS tmp idx


val aes256_cbc_decrypt: out:bytes -> kex:skey -> iv:block -> cip:bytes{length cip == length out} -> len:size_t -> Stack size_t
    (requires (fun h0 -> True))
    (ensures (fun h0 _ h1 -> True))
let aes256_cbc_decrypt out key iv cip ciplen = 
  push_frame();
  let kex = alloca (u64 0) 88ul in
  let tmp = alloca 0uy 16ul in
  key_expansion kex key;
  cbc_decrypt_blocks out kex iv cip ciplen (size 0) tmp;
  let pad = tmp.(ciplen -. size 1) in
  let pad32 = Lib.RawIntTypes.size_from_UInt32 (FStar.Int.Cast.uint8_to_uint32 pad) in
  let msglen = ciplen -. pad32 in
  pop_frame();
  msglen

let aes256_cbc_decrypt_no_pad out key iv cip ciplen = 
  push_frame();
  let kex = alloca (u64 0) 88ul in
  let tmp = alloca 0uy 16ul in
  key_expansion kex key;
  cbc_decrypt_blocks out kex iv cip ciplen (size 0) tmp;
  pop_frame();
  ciplen
