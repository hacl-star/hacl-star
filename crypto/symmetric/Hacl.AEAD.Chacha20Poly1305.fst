module Hacl.AEAD.Chacha20Poly1305

open FStar.ST
open FStar.Buffer
open FStar.UInt32
open FStar.Ghost
(* open Buffer.Utils *)
open Hacl.Symmetric.Chacha20
open Hacl.Symmetric.Poly1305

let lbuffer (l:nat) = b:FStar.Buffer.buffer Hacl.UInt8.t{length b = l}
let h8 = Hacl.UInt8.t

(* // now hiding the 1-time MAC state & implementation *)
(* module Spec = Crypto.Symmetric.Poly1305.Spec *)
(* module MAC = Crypto.Symmetric.Poly1305.MAC *)
(* module Bytes = Crypto.Symmetric.Bytes *)

#reset-options "--initial_fuel 0 --max_fuel 0"

val fill_bytes:
  b:bytes ->
  v:h8 ->
  len:u32{FStar.UInt32.v len <= length b} ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))
let rec fill_bytes b v len =
  if FStar.UInt32 (len =^ 0ul) then ()
  else (
    let i = FStar.UInt32 (len -^ 1ul) in
    b.(i) <- v;
    fill_bytes b v i
  )

val pad_16:
  b:lbuffer 16 ->
  len:UInt32.t { v len <= 16 } ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))
let pad_16 b len =
  fill_bytes (offset b len) (Hacl.Cast.uint8_to_sint8 0uy) (16ul -^ len)

(* Serializes the length into the appropriate format *)
val length_bytes: b:bytes -> len:UInt32.t -> aad_len:UInt32.t -> STL unit
  (requires (fun h -> live h b /\ length b >= 16))
  (ensures  (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))
let length_bytes b len aad_len =
  let l0  = Hacl.Cast.uint32_to_sint8 len in
  let l1  = Hacl.Cast.uint32_to_sint8 (len >>^ 8ul) in
  let l2  = Hacl.Cast.uint32_to_sint8 (len >>^ 16ul) in
  let l3  = Hacl.Cast.uint32_to_sint8 (len >>^ 24ul) in
  let al0 = Hacl.Cast.uint32_to_sint8 aad_len in
  let al1 = Hacl.Cast.uint32_to_sint8 (aad_len >>^ 8ul) in
  let al2 = Hacl.Cast.uint32_to_sint8 (aad_len >>^ 16ul) in
  let al3 = Hacl.Cast.uint32_to_sint8 (aad_len >>^ 24ul) in
  let zero = Hacl.Cast.uint8_to_sint8 0uy in
  upd b 0ul al0;
  upd b 1ul al1;
  upd b 2ul al2;
  upd b 3ul al3;
  upd b 4ul zero;
  upd b 5ul zero;
  upd b 6ul zero;
  upd b 7ul zero;
  upd b 8ul l0;
  upd b 9ul l1;
  upd b 10ul l2;
  upd b 11ul l3;
  upd b 12ul zero;
  upd b 13ul zero;
  upd b 14ul zero;
  upd b 15ul zero;
  ()

(* AEAD-encrypt for Chacha20-Poly1305. Takes:
   - the additional data (aad)
   - the initial key (key)
   - an initialization vector (iv) and a constant (constant)
   - the plaintext
   - the length of the plaintext (len) and the length of the additional data (len_aad)
   The result is stored in
   - ciphertext for the Chacha20 ciphertext, using the key (key), the iv and the nonce
   - the Poly1305 tag on the ciphertext and the additional data
   *)

val chacha20_aead_encrypt:
  ciphertext:bytes ->
  tag:bytes ->
  aad:bytes ->
  key:bytes ->
  nonce:bytes{length nonce = 12 /\ disjoint ciphertext nonce} ->
  plaintext:bytes ->
  len:UInt32.t ->
  aad_len:UInt32.t ->
  STL unit
    (requires (fun h ->
      live h ciphertext /\ live h tag /\ live h aad /\ live h key /\ live h plaintext
      /\ length ciphertext >= v len
      /\ length tag >= 16
      /\ length aad >= v aad_len
      /\ length key >= 32
      /\ length plaintext >= v len
    ))
    (ensures (fun h0 _ h1 -> live h1 ciphertext /\ live h1 tag /\ modifies_2 ciphertext tag h0 h1 ))
let chacha20_aead_encrypt ciphertext tag aad key nonce plaintext len aad_len =
  push_frame();

  (* Temporary buffers (to be improved) *)
  let zero_byte = Hacl.Cast.uint8_to_sint8 0uy in
  let zero_u32  = Hacl.Cast.uint32_to_sint32 0ul in
  let zero_u64  = Hacl.Cast.uint64_to_sint64 0uL in
  let otk   = create zero_byte 32ul in (* OTK for Poly (to improve) *)
  let state = create zero_u32 32ul in (* Chacha inner state *)
  let acc   = create zero_u64 5ul  in (* Poly's accumulator *)
  let r     = create zero_u64 5ul  in (* First half of poly's key, will be removed (merged with otk) *)

  (* Create OTK, using round '0' of Chacha20 *)
  let counter = Hacl.Cast.uint32_to_sint32 0ul in
  chacha20_block otk state key counter nonce 32ul;
  (* chacha20_init state key counter iv constant; *)
  (* chacha20_update otk state 32ul; *)

  (* Encryption of the plaintext, using Chacha20, counter at 1 *)
  let counter = Hacl.Cast.uint32_to_sint32 1ul in
  chacha20_encrypt ciphertext key counter nonce plaintext len;

  (* MACing of the additional data, the ciphertext and the padding *)
  (* Compute the padding lengths *)
  let max = UInt32.div len 16ul in
  let rem = UInt32.rem len 16ul in
  let max_aad = UInt32.div aad_len 16ul in
  let rem_aad = UInt32.rem aad_len 16ul in
  (* Create padded blocks *)
  let padded_aad = create zero_byte 16ul in
  let padded_ciphertext = create zero_byte 16ul in
  let len_bytes = create zero_byte 16ul in
  blit ciphertext (UInt32.mul max 16ul) padded_ciphertext 0ul rem;
  blit aad (UInt32.mul max_aad 16ul) padded_aad 0ul rem_aad;
  pad_16 padded_ciphertext rem;
  pad_16 padded_aad rem_aad;
  (* Initlialize MAC algorithm with one time key *)
  poly1305_init acc r otk;
  (* Update MAC with
     - padded additional data
     - padded ciphertext
     - formatted length *)
  poly1305_loop aad acc r max_aad;
  if not(UInt32.eq rem_aad 0ul) then poly1305_update padded_aad acc r
  else ();
  poly1305_loop ciphertext acc r max;
  if not(UInt32.eq rem 0ul) then poly1305_update padded_ciphertext acc r
  else ();
  length_bytes len_bytes len aad_len;
  poly1305_update len_bytes acc r;
  (* Finish MAC *)
  poly1305_finish tag acc (Buffer.sub otk 16ul 16ul);
  pop_frame()


(* val chacha20_aead_decrypt: *)
(*   plaintext:bytes -> *)
(*   ciphertext:bytes -> *)
(*   tag:bytes -> *)
(*   aad:bytes -> *)
(*   key:bytes -> *)
(*   nonce:bytes{length nonce = 12 /\ disjoint ciphertext nonce} -> *)
(*   len:UInt32.t -> *)
(*   aad_len:UInt32.t -> *)
(*   STL unit *)
(*     (requires (fun h -> *)
(*       live h ciphertext /\ live h tag /\ live h aad /\ live h key /\ live h plaintext *)
(*       /\ length ciphertext >= v len *)
(*       /\ length tag >= 16 *)
(*       /\ length aad >= v aad_len *)
(*       /\ length key >= 32 *)
(*       /\ length plaintext >= v len *)
(*     )) *)
(*     (ensures (fun h0 _ h1 -> live h1 ciphertext /\ live h1 tag /\ modifies_2 ciphertext tag h0 h1 )) *)
(* let chacha20_aead_decrypt ciphertext tag aad key nonce plaintext len aad_len = *)
(*   push_frame(); *)

(*   (\* Temporary buffers (to be improved) *\) *)
(*   let zero_byte = Hacl.Cast.uint8_to_sint8 0uy in *)
(*   let zero_u32  = Hacl.Cast.uint32_to_sint32 0ul in *)
(*   let zero_u64  = Hacl.Cast.uint64_to_sint64 0uL in *)
(*   let otk   = create zero_byte 32ul in (\* OTK for Poly (to improve) *\) *)
(*   let state = create zero_u32 32ul in (\* Chacha inner state *\) *)
(*   let acc   = create zero_u64 5ul  in (\* Poly's accumulator *\) *)
(*   let r     = create zero_u64 5ul  in *)
(*   let tmp_mac = create zero_byte 16ul in *)

(*   (\* Create OTK, using round '0' of Chacha20 *\) *)
(*   let counter = Hacl.Cast.uint32_to_sint32 0ul in *)
(*   chacha20_block otk state key counter nonce 32ul; *)

(*   (\* MACing of the additional data, the ciphertext and the padding *\) *)
(*   (\* Compute the padding lengths *\) *)
(*   let max = UInt32.div len 16ul in *)
(*   let rem = UInt32.rem len 16ul in *)
(*   let max_aad = UInt32.div aad_len 16ul in *)
(*   let rem_aad = UInt32.rem aad_len 16ul in *)
(*   (\* Create padded blocks *\) *)
(*   (\* let padded_aad = create zero_byte 16ul in *\) *)
(*   (\* let padded_ciphertext = create zero_byte 16ul in *\) *)
(*   (\* let len_bytes = create zero_byte 16ul in *\) *)
(*   (\* blit ciphertext (UInt32.mul max 16ul) padded_ciphertext 0ul rem; *\) *)
(*   (\* blit aad (UInt32.mul max_aad 16ul) padded_aad 0ul rem_aad; *\) *)

(*   (\* pad_16 padded_ciphertext rem; *\) *)
(*   (\* pad_16 padded_aad rem_aad; *\) *)

(*   (\* Initlialize MAC algorithm with one time key *\) *)
(*   poly1305_init acc r otk; *)
(*   poly1305_loop aad acc r max_aad; *)
(*   if not(UInt32.eq rem_aad 0ul) then poly1305_update padded_aad acc r *)
(*   else (); *)
(*   poly1305_loop ciphertext acc r max; *)
(*   if not(UInt32.eq rem 0ul) then poly1305_update padded_ciphertext acc r *)
(*   else (); *)
(*   length_bytes len_bytes len aad_len; *)
(*   poly1305_update len_bytes acc r; *)
(*   (\* Finish MAC *\) *)
(*   poly1305_finish tag acc (Buffer.sub otk 16ul 16ul); *)

(*   (\* Encryption of the plaintext, using Chacha20, counter at 1 *\) *)
(*   let counter = Hacl.Cast.uint32_to_sint32 1ul in *)
(*   chacha20_encrypt ciphertext key counter nonce plaintext len; *)
(*   pop_frame() *)
