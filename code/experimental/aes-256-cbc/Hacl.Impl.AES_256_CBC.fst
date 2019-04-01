module Hacl.Impl.AES_256_CBC

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Impl.AES_256

#set-options "--max_fuel 0 --initial_fuel 0 --max_ifuel 0 --initial_ifuel 0"

val xor_block: out:block -> in1:block -> in2:block -> start:size_t{v start <= v blocklen} -> Stack unit
    (requires (fun h0 -> live h0 in1 /\ live h0 in2 /\ live h0 out))
    (ensures (fun h0 _ h1 -> modifies1 out h0 h1))
let rec xor_block out in1 in2 start =
    if start = blocklen then ()
    else (out.(start) <- (in1.(start) ^. in2.(start));
	  xor_block out in1 in2 (start +. size 1))

#set-options "--z3rlimit 20"

val cbc_encrypt_blocks:
  out:buffer uint8 ->
  kex:xkey ->
  prev:block ->
  msg:buffer uint8{length msg == length out} ->
  len:size_t{length msg == v len} ->
  curr:size_t{v curr <= v len /\ v curr % 16 = 0} ->
  tmp:block -> Stack unit
    (requires (fun h0 -> live h0 out /\ live h0 prev /\ live h0 msg /\ live h0 tmp /\ live h0 kex /\
      disjoint out kex /\ disjoint out msg /\ disjoint out tmp
    ))
    (ensures (fun h0 _ h1 -> modifies2 tmp out h0 h1))
    (decreases (v len - v curr))
let rec cbc_encrypt_blocks out kex prev msg len curr tmp =
  if curr = len then ()
  else (
    assert(v curr < v len /\ v curr % 16 = 0);
    assume(v curr <= v len - 16);
    let mblock = sub #MUT #uint8 #len msg curr (size 16) in
    let oblock = sub #MUT #uint8 #len out curr (size 16) in
    xor_block tmp mblock prev 0ul;
    cipher oblock tmp kex;
    cbc_encrypt_blocks out kex oblock msg len (curr +. size 16) tmp
  )

val padPKCS: tmp:block -> len:size_t{v len <= v blocklen} -> idx:size_t{v idx <= v blocklen} -> Stack unit
	 (requires (fun h -> live h tmp))
	 (ensures (fun h0 _ h1 -> modifies1 tmp h0 h1))
	 (decreases (v blocklen - v idx))
let rec padPKCS tmp len idx =
    if idx = blocklen then ()
    else (tmp.(idx) <- cast U8 SEC len; padPKCS tmp len (idx +. size 1))

val padISO: tmp:block -> len:size_t{v len <= 16} -> idx:size_t{v idx < 16} -> Stack unit
	 (requires (fun h -> live h tmp))
	 (ensures (fun h0 _ h1 -> modifies1 tmp h0 h1))
let padISO tmp b idx =
    tmp.(idx) <- u8 0x80

val aes256_cbc_encrypt:
  out:buffer uint8 ->
  key:lbuffer uint8 keylen ->
  iv:block ->
  msg:buffer uint8{length msg + 16 == length out} ->
  msglen:size_t{v msglen = length msg /\ (v msglen / 16) * 16 + 16 <= max_size_t} ->
  Stack unit
    (requires (fun h -> live h out /\ live h key /\ live h iv /\ live h msg /\
      disjoint out key /\ disjoint out iv /\ disjoint out msg
    ))
    (ensures (fun h0 _ h1 -> modifies1 out h0 h1))

#set-options "--admit_smt_queries true"

let aes256_cbc_encrypt out key iv msg msglen =
  push_frame();
  assert (16 <> 0);
  let fullblocks = (msglen /. size 16) *. size 16 in
  let final = msglen %. size 16 in
  let msg1 = sub #MUT #uint8 #msglen msg (size 0) fullblocks in
  let last = sub #MUT #uint8 #msglen msg fullblocks final in
  let out1 = sub #MUT #uint8 #(msglen +. size 16) out (size 0) fullblocks in
  let out2 = sub #MUT #uint8 #(msglen +. size 16) out fullblocks (size 16) in
  assert(disjoint out1 out2);
  let kex = create xkeylen (u8 0) in
  let tmp = create (size 16) (u8 0) in
  let otmp = create (size 16) (u8 0) in
  keyExpansion key kex;
  cbc_encrypt_blocks out1 kex iv msg1 fullblocks 0ul tmp;
  let lastfull = if (fullblocks <> size 0) then sub out1 (fullblocks -. size 16) (size 16)
                 else iv in
  let ltmp = create (size 16) (u8 0) in
  update_sub last (size 0) final (sub ltmp (size 0) final);//blit last 0ul ltmp 0ul final;
  padPKCS ltmp (size 16 -. final) final;
  xor_block ltmp ltmp lastfull (size 0);
  cipher otmp ltmp kex;
  copy out2 otmp;//blit otmp 0ul out2 0ul 16ul;
  pop_frame()

#set-options "--admit_smt_queries false"

val aes256_cbc_encrypt_no_pad:
  out:buffer uint8 ->
  key:lbuffer uint8 keylen ->
  iv:block ->
  msg:buffer uint8{length msg == length out} ->
  msglen:size_t{v msglen = length msg /\ (v msglen / 16) * 16 + 16 <= max_size_t} ->
  Stack unit
    (requires (fun h -> live h out /\ live h key /\ live h iv /\ live h msg /\
      disjoint out key /\ disjoint out iv /\ disjoint out msg
    ))
    (ensures (fun h0 _ h1 -> modifies1 out h0 h1))

#set-options "--z3rlimit 20"

let aes256_cbc_encrypt_no_pad out key iv msg msglen =
  push_frame();
  let kex = create xkeylen (u8 0) in
  let tmp = create (size 16) (u8 0) in
  keyExpansion key kex;
  cbc_encrypt_blocks out kex iv msg msglen 0ul tmp;
  pop_frame()

val cbc_decrypt_blocks:
  out:buffer uint8 ->
  kex:xkey ->
  prev:block ->
  cip:buffer uint8{length cip == length out} ->
  len:size_t{v len = length cip} ->
  curr:size_t{v curr <= v len /\ v curr % 16 = 0} ->
  tmp:block ->
  Stack unit
    (requires (fun h -> live h out /\ live h kex /\ live h prev /\ live h cip /\ live h tmp /\
      disjoint out kex /\ disjoint out prev /\ disjoint out cip /\ disjoint out tmp /\
      disjoint tmp kex /\ disjoint tmp prev /\ disjoint tmp cip
    ))
    (ensures (fun h0 _ h1 -> modifies2 tmp out h0 h1))
    (decreases (v len - v curr))

let rec cbc_decrypt_blocks out kex prev cip len curr tmp =
  if curr = len then ()
  else (
    assert(v curr < v len /\ v curr % 16 = 0);
    assume(v curr <= v len - 16);
    let cblock = sub #MUT #uint8 #len cip curr (size 16) in
    let oblock = sub #MUT #uint8 #len out curr (size 16) in
    inv_cipher tmp cblock kex;
    xor_block oblock tmp prev (size 0);
    cbc_decrypt_blocks out kex cblock cip len (curr +. size 16) tmp
  )


val unpadPKCS:
  tmp:block ->
  idx:size_t{v idx <= v blocklen} ->
  Stack (len:size_t{v len <= v blocklen})
	 (requires (fun h -> live h tmp))
	 (ensures (fun h0 _ h1 -> modifies1 tmp h0 h1))
let rec unpadPKCS tmp idx =
  let pad = tmp.(blocklen -. size 1) in
  (* Reading the padding is inherently non constant *)
  let pad32 = admit(); cast U32 PUB pad in
  if pad32 <=. blocklen then pad32
  else size 0

val unpadISO:
  tmp:block ->
  idx:size_t{v idx < v blocklen} ->
  Stack (len:size_t{v len < v blocklen})
	 (requires (fun h -> live h tmp))
	 (ensures (fun h0 _ h1 -> modifies1 tmp h0 h1))
let rec unpadISO tmp idx =
   let t = tmp.(idx) in
   (* Reading the padding is inherently non constant *)
   if (admit();cast U8 PUB t) = uint #U8 #PUB 0x80 then idx
   else if t <> 0x00uy then 0ul
   else if idx = 0x0ul then 0ul
   else unpadISO tmp (idx -. size 1)

val aes256_cbc_decrypt:
  out:buffer uint8 ->
  key:lbuffer uint8 keylen ->
  iv:block ->
  cip:buffer uint8{length cip == length out} ->
  ciplen:size_t{v ciplen = length cip /\ (v ciplen / 16) * 16 + 16 <= max_size_t /\ v ciplen > 0} ->
  Stack size_t
    (requires (fun h -> live h out /\ live h key /\ live h iv /\ live h cip /\
      disjoint out key /\ disjoint out iv /\ disjoint out cip
    ))
    (ensures (fun h0 _ h1 -> modifies1 out h0 h1))


let aes256_cbc_decrypt out key iv cip ciplen =
  push_frame();
  let kex = create xkeylen (u8 0) in
  let tmp = create (size 16) (u8 0) in
  keyExpansion key kex;
  cbc_decrypt_blocks out kex iv cip ciplen 0ul tmp;
  let pad = index #MUT #uint8 #ciplen out (ciplen -. size 1) in
  let pad32 = (admit(); cast #U8 #SEC U32 PUB pad) in
  let msglen = ciplen -. pad32 in
  pop_frame();
  msglen

val aes256_cbc_decrypt_no_pad:
  out:buffer uint8 ->
  key:lbuffer uint8 keylen ->
  iv:block ->
  cip:buffer uint8{length cip == length out} ->
  ciplen:size_t{v ciplen = length cip /\ (v ciplen / 16) * 16 + 16 <= max_size_t /\ v ciplen > 0} ->
  Stack size_t
    (requires (fun h -> live h out /\ live h key /\ live h iv /\ live h cip /\
      disjoint out key /\ disjoint out iv /\ disjoint out cip
    ))
    (ensures (fun h0 _ h1 -> modifies1 out h0 h1))

let aes256_cbc_decrypt_no_pad out key iv cip ciplen =
  push_frame();
  let kex = create xkeylen (u8 0) in
  let tmp = create (size 16) (u8 0) in
  keyExpansion key kex;
  cbc_decrypt_blocks out kex iv cip ciplen (size 0) tmp;
  pop_frame();
  ciplen
