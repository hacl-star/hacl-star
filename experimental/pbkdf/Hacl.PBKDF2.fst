module Hacl.PBKDF2

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.ST
open FStar.UInt32
open Hacl.Cast
open Hacl.UInt8
open Hacl.UInt32
open Hacl.SBuffer

open HMAC.Sha256

module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module U8 = Hacl.UInt8
module U32 = Hacl.UInt32

let u32 = FStar.UInt32.t
let u64 = FStar.UInt64.t
let s64 = Hacl.UInt64.t
let s32 = Hacl.UInt32.t
let s8 = Hacl.UInt8.t
let uint32s = Hacl.SBuffer.u32s
let bytes = Hacl.SBuffer.u8s


#set-options "--lax"

let maxU32 = 4294967296ul
assume MaxU32: pow2 32 = 4294967296


let op_At_At_Amp = UInt32.logand

val be_bytes_of_uint32: bytes -> u32 -> St unit
let be_bytes_of_uint32 output x =
 let b3 = uint32_to_sint8 ((UInt32.shift_right x 24ul) @@& 255ul) in
 let b2 = uint32_to_sint8 ((UInt32.shift_right x 16ul) @@& 255ul) in
 let b1 = uint32_to_sint8 ((UInt32.shift_right x 8ul)  @@& 255ul) in
 let b0 = uint32_to_sint8 ((x)                         @@& 255ul) in
 upd output 0ul b0; 
 upd output (1ul) b1;
 upd output (2ul) b2;
 upd output (3ul) b3


(* Operators *)
let op_At_Plus_Percent (a:u32) (b:u32) : Tot u32 = UInt32.add_mod a b
let op_At_Subtraction_Percent (a:u32) (b:u32) : Tot u32 = UInt32.sub_mod a b
let op_At_Slash_Percent (a:u32) (b:u32) : Tot u32 = UInt32.div a b
let op_At_Star_Percent (a:u32) (b:u32) : Tot u32 = UInt32.mul_mod a b
let op_At_Percent_Percent (a:u32) (b:u32) : Tot u32 = UInt32.rem a b


(* Define algorithm parameters *)
let mac = hmac_sha256
let hl = 32ul


val pbkdf2_inner_F : (f        :bytes) ->
                     (ti       :bytes { length ti = v hl /\ disjoint f ti }) ->
                     (i        :u32) ->
                     (password :bytes { disjoint password f /\ disjoint password ti }) ->
                     (passwdlen :u32  { length password = v passwdlen }) ->
                     (salt     :bytes { disjoint salt f /\ disjoint salt ti /\ disjoint salt password }) ->
                     (saltlen  :u32   { length salt = v saltlen }) ->
                     (c        :u32)
                     -> STL unit
                          (requires (fun h -> live h f /\ live h ti /\ live h password /\ live h salt))
                          (ensures  (fun h0 r h1 -> live h1 f /\ live h1 ti /\ live h1 password /\ live h1 salt))
                          
let rec pbkdf2_inner_F f ti i password passwdlen salt saltlen c =
  if i = 1ul then begin
    let _pos = i in
    let _wlen = saltlen @+% (hl @/% 8ul) in
    let _i = create 0uy 4ul in
    be_bytes_of_uint32 _i i;
    let _w = create 0uy _wlen in
    blit salt 0ul _w 0ul saltlen;
    blit _i 0ul _w saltlen 4ul;
    mac ti _w _wlen password passwdlen;
    blit ti 0ul f _pos hl;
    pbkdf2_inner_F f ti (i @+% 1ul) password passwdlen salt saltlen c end
  else if lt i c then begin
    let _tmp = create 0uy hl in
    blit ti 0ul _tmp 0ul hl;
    mac ti _tmp hl password passwdlen;
    xor_bytes f _tmp ti hl;
    pbkdf2_inner_F f ti (i @+% 1ul) password passwdlen salt saltlen c end
  else ()


val pbkdf2_inner_T : (dk        :bytes) ->
                     (f         :bytes { length f = v hl /\ disjoint f dk }) ->
                     (ti        :bytes { length ti = v hl /\ disjoint ti dk /\ disjoint ti f }) ->
                     (i         :u32) ->
                     (l         :u32) ->
                     (password  :bytes { disjoint password dk /\ disjoint password f /\ disjoint password ti }) ->
                     (passwdlen :u32   { length password = v passwdlen } ) ->
                     (salt      :bytes { disjoint salt dk /\ disjoint salt f /\ disjoint salt ti /\ disjoint salt password }) ->
                     (saltlen   :u32   { length salt = v saltlen }) ->
                     (c         :u32)
                     -> STL unit
                          (requires (fun h -> live h dk /\ live h f /\ live h ti /\ live h password /\ live h salt))
                          (ensures  (fun h0 r h1 -> live h1 dk /\ live h1 f /\ live h1 ti /\ live h1 password /\ live h1 salt))

let rec pbkdf2_inner_T dk f ti i l password passwdlen salt saltlen c =
  if lte i l then begin
    let pos = (i @-% 1ul) @*% hl in
    pbkdf2_inner_F f ti i password passwdlen salt saltlen c;
    blit f 0ul dk pos hl;
    pbkdf2_inner_T dk f ti (i @+% 1ul) l password passwdlen salt saltlen c end
  else ()


val pbkdf2 : dk:bytes -> dklen:u32 -> password:bytes -> passwdlen:u32 -> salt:bytes -> saltlen:u32 -> c:u32
  -> STL (retcode:u32)
        (requires (fun h -> live h dk /\ live h password /\ live h salt))
        (ensures  (fun h0 _ h1 -> live h1 dk /\ live h1 password /\ live h1 salt /\ modifies_1 dk h0 h1))
        
let pbkdf2 dk dklen password passwdlen salt saltlen c =
  (* Step 1: check for length of the derived key *)
  if gt dklen (maxU32 @-% 1ul) then
    1ul
  else

  (* Step 2: compute l and r parameters *)
  let l =
    let rest = dklen @%% hl in
    if rest <> 0ul then (dklen @-% rest) @/% hl @+% 1ul else (dklen @-% rest) @/% hl
  in
  let r = dklen @-% (l @-% 1ul) @*% hl in

  (* Step 3 & 4: define function F and apply it; concatenate ti blocks into dk *)
  let i = 0ul in
  let f = create 0uy hl in
  let ti = create 0uy hl in
  pbkdf2_inner_T dk f ti i l password passwdlen salt saltlen c;
  0ul
