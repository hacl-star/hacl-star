module Crypto.HKDF

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Buffer
open FStar.UInt32

(* Definition of aliases for modules *)
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module HMAC = Crypto.HMAC

(* Definition of base types *)
let uint8_t   = FStar.UInt8.t
let uint32_t  = FStar.UInt32.t
let uint64_t  = FStar.UInt64.t
let uint32_p = Buffer.buffer uint32_t
let uint8_p  = Buffer.buffer uint8_t

type alg = HMAC.alg

// ADL July 4
#set-options "--lax"
(* Define HKDF Extraction function *)
val hkdf_extract :
  a       : alg ->
  prk     : uint8_p{length prk = v (HMAC.hash_size a)} ->
  salt    : uint8_p ->
  saltlen : uint32_t{v saltlen = length salt} ->
  ikm     : uint8_p ->
  ikmlen  : uint32_t{v ikmlen = length ikm} ->
  Stack unit
        (requires (fun h0 -> live h0 prk /\ live h0 salt /\ live h0 ikm))
        (ensures  (fun h0 r h1 -> live h1 prk /\ modifies_1 prk h0 h1))

let hkdf_extract a prk salt saltlen ikm ikmlen =
  HMAC.hmac a prk salt saltlen ikm ikmlen


[@"c_inline"]
private val hkdf_expand_inner:
  a       : alg ->
  state   : uint8_p ->
  prk     : uint8_p {v (HMAC.hash_size a) <= length prk} ->
  prklen  : uint32_t {v prklen = length prk} ->
  info    : uint8_p ->
  infolen : uint32_t {v infolen = length info} ->
  n       : uint32_t {v n <= pow2 8}->
  i       : uint32_t {v i <= v n} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 prk /\ live h0 info))
        (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1))

[@"c_inline"]
let rec hkdf_expand_inner a state prk prklen info infolen n i =

  (* Push a new memory frame *)
  (**) push_frame();

  (* Recompute the sizes and position of the intermediary objects *)
  (* Note: here we favour readability over efficiency *)
  let size_Ti  = HMAC.hash_size a in
  let size_Til = size_Ti +^ infolen +^ 1ul in

  let pos_Ti = 0ul in
  let pos_Til = size_Ti in
  let pos_T = pos_Til +^ size_Til in

  (* Retreive the memory for local computations. state =  Ti | Til | T *)
  let ti = Buffer.sub state pos_Ti size_Ti in
  let til = Buffer.sub state pos_Til size_Til in
  let t = Buffer.sub state pos_T size_T in

  if (i =^ 1ul) then begin

    (* Concatenate T(i-1) | Info | i *)
    Buffer.blit info 0ul til 0ul infolen;
    Buffer.upd til (size_Til -^ 1ul) (Int.Cast.uint32_to_uint8 i);

    (* Compute the mac of to get block Ti *)
    HMAC.hmac a ti prk prklen til size_Til;

    (* Store the resulting block in T *)
    Buffer.blit ti 0ul t 0ul size_Ti;

    (* Recursive call *)
    hkdf_expand_inner a state prk prklen info infolen n (i +^ 1ul) end

  else if (i <=^ n) then begin

    (* Concatenate T(i-1) | Info | i *)
    Buffer.blit ti 0ul til 0ul size_Ti;
    Buffer.blit info 0ul til size_Ti infolen;
    Buffer.upd til (size_Til -^ 1ul) (Int.Cast.uint32_to_uint8 i);

    (* Compute the mac of to get block Ti *)
    HMAC.hmac a ti prk prklen til size_Til;

    (* Store the resulting block in T *)
    let pos = U32.mul_mod (i -^ 1ul) size_Ti in
    Buffer.blit ti 0ul t pos size_Ti;

    (* Recursive call *)
    hkdf_expand_inner a state prk prklen info infolen n (i +^ 1ul) end
  else ();

  (* Pop the memory frame *)
  (**) pop_frame()

(* Define HKDF Expand function *)
val hkdf_expand :
  a       : alg ->
  okm     : uint8_p ->
  prk     : uint8_p {v (HMAC.hash_size a) <= length prk} ->
  prklen  : uint32_t {v prklen <= length prk} ->
  info    : uint8_p ->
  infolen : uint32_t {v infolen <= length info} ->
  len     : uint32_t {v len <= length okm
                    /\ v len <= (255 * U32.v (HMAC.hash_size a))
                    /\ (U32.v len / U32.v (HMAC.hash_size a) + 1) <= length okm} ->
  Stack unit
        (requires (fun h0 -> live h0 okm /\ live h0 prk /\ live h0 info))
        (ensures  (fun h0 r h1 -> live h1 okm /\ modifies_1 okm h0 h1))

let hkdf_expand a okm prk prklen info infolen len =

  (* Push a new memory frame *)
  (**) push_frame ();

  (* Compute the number of blocks necessary to compute the output *)
  let size_Ti = HMAC.hash_size a in
  let n = U32.(div len size_Ti) +^ 1ul in

  (* Describe the shape of memory used by the inner recursive function *)
  let size_T = U32.mul_mod n size_Ti in
  let size_Til = size_Ti +^ infolen +^ 1ul in

  let pos_Ti = 0ul in
  let pos_Til = size_Ti in
  let pos_T = pos_Til +^ size_Til in

  (* Allocate memory for inner expension: state =  Ti | Til | T *)
  let state = Buffer.create 0uy (size_Ti +^ size_Til +^ size_T) in

  (* Call the inner expension function *)
  hkdf_expand_inner a state prk prklen info infolen n 0ul;

  (* Extract T from the state *)
  let _T = Buffer.sub state pos_T size_T in

  (* Redundant copy the desired part of T *)
  Buffer.blit _T 0ul okm 0ul len;

  (* Pop the memory frame *)
  (**) pop_frame()
