module Hacl.HKDF.fst

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.ST
open FStar.Buffer
open FStar.UInt32
open Hacl.Cast
open Hacl.UInt8
open Hacl.UInt32
open Hacl.SBuffer

open Hacl.Hash.SHA2.L256
open Hacl.HMAC.SHA2.L256

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



val xor_bytes: output:bytes -> in1:bytes -> in2:bytes{disjoint in1 in2 /\ disjoint in1 output /\ disjoint in2 output} -> len:u32{v len <= length output /\ v len <= length in1 /\ v len <= length in2} -> STL unit
  (requires (fun h -> live h output /\ live h in1 /\ live h in2))
  (ensures  (fun h0 _ h1 -> live h0 output /\ live h0 in1 /\ live h0 in2 
    /\ live h1 output /\ live h1 in1 /\ live h1 in2
    /\ modifies_1 output h0 h1
    (* /\ (forall (i:nat). i < v len ==> get h1 output i = (UInt8.logxor (get h0 in1 i) (get h0 in2 i))) *)
   ))
let rec xor_bytes output in1 in2 len =
  let h0 = ST.get() in
  if len =^ 0ul then ()
  else
    begin
      let i = UInt32.sub len 1ul in 
      let in1i = index in1 i in
      let in2i = index in2 i in
      let oi = Hacl.UInt8.logxor in1i in2i in
      upd output i oi; 
      let h1 = ST.get() in
      no_upd_lemma_1 h0 h1 output in1;
      no_upd_lemma_1 h0 h1 output in2;
      xor_bytes output in1 in2 i
    end

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
let op_At_Plus (a:u32) (b:u32) : Tot u32 = UInt32.add_mod a b
let op_At_Minus (a:u32) (b:u32) : Tot u32 = UInt32.sub_mod a b


(* Define the hash length used *)
let hl = 32ul
let hmac = hmac_sha256


(* Define HKDF Extraction function *)
val hkdf_extract : (prk     :bytes { length prk = v hl }) ->
                   (salt    :bytes { disjoint prk salt }) ->
                   (saltlen :u32 { length salt = v saltlen } ) ->
                   (ikm     :bytes { disjoint prk ikm /\ disjoint salt ikm }) ->
                   (ikmlen  :u32 { length ikm = v ikmlen })
                   -> STL unit
                        (requires (fun h -> live h prk /\ live h salt /\ live h ikm))
                        (ensures  (fun h0 r h1 -> live h1 prk /\ live h1 salt /\ live h1 ikm /\ modifies_1 prk h0 h1))

let hkdf_extract prk salt saltlen ikm ikmlen = hmac prk salt saltlen ikm ikmlen


// We could simplify the memory safety clause by reducing to modifies_1 _T h0 h1
val hkdf_expand_inner : (t       :bytes) ->
                        (prk     :bytes { length prk >= v hl /\ disjoint t prk }) ->
                        (prklen  :u32   { length prk = v prklen }) ->
                        (info    :bytes { disjoint t info /\ disjoint prk info }) ->
                        (infolen :u32   { length info = v infolen }) ->
                        (n       :u32) ->
                        (i       :stackref u32) ->
                        (ti      :bytes { length ti = (v hl) + (v infolen) + 1
                                           /\ disjoint ti t /\ disjoint ti prk /\ disjoint ti info }) ->
                        (til     :bytes { length til = v hl
                                           /\ disjoint til t /\ disjoint til prk
                                           /\ disjoint til info /\ disjoint til ti})
                        -> STL unit
                             (requires (fun h -> live h t /\ live h prk /\ live h info /\ live h ti /\ live h til))
                             (ensures  (fun h0 r h1 -> live h1 t /\ live h1 prk /\ live h1 info /\ live h1 ti /\ live h1 til))

let rec hkdf_expand_inner t prk prklen info infolen n i ti til =
  let _i = create (uint8_to_sint8 0uy) 4ul in
  be_bytes_of_uint32 _i !i;
  if !i = 1ul then begin
    let _til = create (uint8_to_sint8 0uy) (infolen @+ 1ul) in
    blit info 0ul _til 0ul infolen;
    blit _i 0ul _til infolen 1ul;
    hmac ti prk prklen _til (infolen @+ 1ul);
    blit ti 0ul t 0ul hl;
    i := !i @+ 1ul;
    hkdf_expand_inner t prk prklen info infolen n i ti til end
  else if lte !i n then begin
    blit ti 0ul til 0ul hl;
    blit info 0ul til hl infolen;
    blit _i 0ul til (hl @+ infolen) 1ul;
    hmac ti prk prklen til (hl @+ infolen @+ 1ul);
    let pos = UInt32.mul_mod (!i @- 1ul) hl in
    blit ti 0ul t pos hl;
    i := !i @+ 1ul;
    hkdf_expand_inner t prk prklen info infolen n i ti til end
  else ()


(* Define HKDF Expand function *)
val hkdf_expand : (okm     :bytes) ->
                  (prk     :bytes { length prk >= v hl /\ disjoint prk okm }) ->
                  (prklen  :u32 { length prk = v prklen }) ->
                  (info    :bytes { disjoint info okm /\ disjoint info prk}) ->
                  (infolen :u32 { length info = v infolen }) ->
                  (l       :u32 { length okm = v l })
                  -> STL unit
                       (requires (fun h -> live h okm /\ live h prk /\ live h info))
                       (ensures  (fun h0 r h1 -> live h1 okm /\ live h1 prk /\ live h1 info /\ modifies_1 okm h0 h1))

let hkdf_expand okm prk prklen info infolen l =
  let n =
    let r = UInt32.rem l hl in
    (UInt32.div (l @- r) hl) @+ 1ul
  in
  let i = ST.salloc 1ul in
  let _Til = create (uint8_to_sint8 0uy) (hl @+ infolen @+ 1ul) in
  let _Ti = create (uint8_to_sint8 0uy) hl in
  let _T = create (uint8_to_sint8 0uy) (UInt32.mul_mod n hl) in
  hkdf_expand_inner _T prk prklen info infolen n i _Ti _Til;
  blit _T 0ul okm 0ul l
