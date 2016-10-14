module Hacl.SecretBox

open FStar.Buffer
open FStar.ST
open Hacl.Constants
open Hacl.Policies
open Hacl.Cast

(* Module abbreviations *)
module HS  = FStar.HyperStack
module B   = FStar.Buffer
module U8  = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module H8  = Hacl.UInt8
module H32 = Hacl.UInt32
module H64 = Hacl.UInt64

(* TODO:
   disjointness clauses
*)

private val set_zero_bytes:
  b:uint8_p{length b >= 16} ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))
let set_zero_bytes b =
  let zero = uint8_to_sint8 0uy in
  b.(0ul)  <- zero; b.(1ul)  <- zero; b.(2ul)  <- zero; b.(3ul)  <- zero;
  b.(4ul)  <- zero; b.(5ul)  <- zero; b.(6ul)  <- zero; b.(7ul)  <- zero;
  b.(8ul)  <- zero; b.(9ul)  <- zero; b.(10ul) <- zero; b.(11ul) <- zero;
  b.(12ul) <- zero; b.(13ul) <- zero; b.(14ul) <- zero; b.(15ul) <- zero;
  b.(16ul) <- zero; b.(17ul) <- zero; b.(18ul) <- zero; b.(19ul) <- zero;
  b.(20ul) <- zero; b.(21ul) <- zero; b.(22ul) <- zero; b.(23ul) <- zero;
  b.(24ul) <- zero; b.(25ul) <- zero; b.(26ul) <- zero; b.(27ul) <- zero;
  b.(28ul) <- zero; b.(29ul) <- zero; b.(30ul) <- zero; b.(31ul) <- zero

val crypto_secretbox_detached:
  c:uint8_p ->
  mac:uint8_p{length mac = crypto_secretbox_MACBYTES} ->
  m:uint8_p ->
  mlen:u64{let len = U64.v mlen in len = length m /\ len = length c}  ->
  n:uint8_p{length n = crypto_secretbox_NONCEBYTES} ->
  k:uint8_p{length k = crypto_secretbox_KEYBYTES} ->
  Stack u32
    (requires (fun h -> live h c /\ live h mac /\ live h m /\ live h n /\ live h k))
    (ensures  (fun h0 z h1 -> modifies_2 c mac h0 h1 /\ live h1 c /\ live h1 mac))
let crypto_secretbox_detached c mac m mlen n k =
  push_frame();
  let hsalsa_state = create (uint8_to_sint8 0uy) 160ul in
  let salsa_state = create (uint32_to_sint32 0ul) 32ul in
  let block0 = sub hsalsa_state 0ul 64ul in
  let subkey = sub hsalsa_state 64ul 32ul in
  let block1 = sub hsalsa_state 96ul 64ul in
  set_zero_bytes block0;
  let mlen = Int.Cast.uint64_to_uint32 mlen in
  let zerobytes = 32ul in
  let mlen0 =
    if (U32 (mlen >^ (64ul -^ zerobytes))) then U32 (64ul -^ zerobytes) else mlen in
  blit m 0ul block0 zerobytes mlen0;
  Hacl.Symmetric.XSalsa20.hsalsa_init subkey k (sub n 0ul 16ul);
  Hacl.Symmetric.Salsa20.salsa20_encrypt_body salsa_state
                                              block1
                                              subkey
                                              (uint64_to_sint64 0uL)
                                              (sub n 16ul 8ul)
                                              block0
                                              (U32 (mlen0 +^ zerobytes));
  (* Hacl.Symmetric.Poly1305.poly1305_init acc r block1; *)
  blit block1 zerobytes c 0ul mlen0;

  if (U32 (mlen >^ mlen0)) then Hacl.Symmetric.Salsa20.salsa20_encrypt_body salsa_state
                                                                            (offset c mlen0)
                                                                            subkey
                                                                            (uint64_to_sint64 1uL)
                                                                            (sub n 16ul 8ul)
                                                                            (offset m mlen0)
                                                                            (U32 (mlen -^ mlen0));
  Hacl.Symmetric.Poly1305.poly1305_mac mac c mlen block1;
  pop_frame();
  0ul


val crypto_secretbox_open_detached:
  m:uint8_p ->
  c:uint8_p ->
  mac:uint8_p{length mac = crypto_secretbox_MACBYTES /\ declassifiable mac} ->
  clen:u64{let len = U64.v clen in len = length m /\ len = length c}  ->
  n:uint8_p{length n = crypto_secretbox_NONCEBYTES} ->
  k:uint8_p{length k = crypto_secretbox_KEYBYTES} ->
  Stack u32
    (requires (fun h -> live h m /\ live h c /\ live h mac /\ live h n /\ live h k))
    (ensures  (fun h0 z h1 -> modifies_1 m h0 h1 /\ live h1 m))
let crypto_secretbox_open_detached m c mac clen n k =
  push_frame();
  let hsalsa_state = create (uint8_to_sint8 0uy) 160ul in
  let salsa_state = create (uint32_to_sint32 0ul) 32ul in
  let tmp_mac = create (uint8_to_sint8 0uy) 16ul in
  let block0 = sub hsalsa_state 0ul 64ul in
  let subkey = sub hsalsa_state 64ul 32ul in
  let block1 = sub hsalsa_state 96ul 64ul in
  let clen = Int.Cast.uint64_to_uint32 clen in
  Hacl.Symmetric.XSalsa20.hsalsa_init subkey k (sub n 0ul 16ul);
  Hacl.Symmetric.Salsa20.salsa20_core block0
                                      salsa_state
                                      subkey
                                      (uint64_to_sint64 0uL)
                                      (sub n 16ul 8ul)
                                      64ul;
  Hacl.Symmetric.Poly1305.poly1305_mac tmp_mac c clen block0;
  assume (Hacl.Policies.declassifiable tmp_mac);
  let verify = cmp_bytes mac tmp_mac 16ul in
  let zerobytes = 32ul in
  (* TODO: report kremlin bug *)
  let clen0 =
    if (U32 (clen >^ (64ul -^ zerobytes))) then U32 (64ul -^ zerobytes) else clen in
  let z =
    if U8 (verify =^ 0uy) then (
      blit c 0ul block0 zerobytes clen0;
      Hacl.Symmetric.Salsa20.salsa20_encrypt_body salsa_state
                                                  block1
                                                  subkey
                                                  (uint64_to_sint64 0uL)
                                                  (sub n 16ul 8ul)
                                                  block0
                                                  (U32 (clen0 +^ zerobytes));
      blit block1 zerobytes m 0ul clen0;
      if (U32 (clen >^ clen0)) then Hacl.Symmetric.Salsa20.salsa20_encrypt_body salsa_state
                                                                                (offset m clen0)
                                                                                subkey
                                                                                (uint64_to_sint64 1uL)
                                                                                (sub n 16ul 8ul)
                                                                                (offset c clen0)
                                                                                (U32 (clen -^ clen0));
      0x0ul
    )
    else 0xfffffffful in
  pop_frame();
  z


val crypto_secretbox_easy:
  c:uint8_p ->
  m:uint8_p ->
  mlen:u64{let len = U64.v mlen in len <= length m /\ len + crypto_secretbox_MACBYTES <= length c}  ->
  n:uint8_p{length n = crypto_secretbox_NONCEBYTES} ->
  k:uint8_p{length k = crypto_secretbox_KEYBYTES} ->
  Stack u32
    (requires (fun h -> live h c /\ live h m /\ live h n /\ live h k))
    (ensures  (fun h0 z h1 -> modifies_1 c h0 h1 /\ live h1 c))
let crypto_secretbox_easy c m mlen n k =
  let mlen_ = FStar.Int.Cast.uint64_to_uint32 mlen in
  let c'   = sub c 16ul (U32 (mlen_+^16ul)) in
  let mac  = sub c 0ul 16ul in
  crypto_secretbox_detached c' mac m mlen n k


val crypto_secretbox_open_easy:
  m:uint8_p ->
  c:uint8_p ->
  clen:u64{let len = U64.v clen in len = length m + crypto_secretbox_MACBYTES /\ len = length c}  ->
  n:uint8_p{length n = crypto_secretbox_NONCEBYTES} ->
  k:uint8_p{length k = crypto_secretbox_KEYBYTES} ->
  Stack u32
    (requires (fun h -> live h c /\ live h m /\ live h n /\ live h k))
    (ensures  (fun h0 z h1 -> modifies_1 m h0 h1 /\ live h1 m))
let crypto_secretbox_open_easy m c clen n k =
  let clen_ = FStar.Int.Cast.uint64_to_uint32 clen in
  let c'  = sub c 16ul clen_ in
  let mac = sub c 0ul 16ul in
  crypto_secretbox_open_detached m c' mac (U64 (clen -^ 16uL)) n k
