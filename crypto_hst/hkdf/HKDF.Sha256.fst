module HKDF.Sha256

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HST
open FStar.UInt32
open Hacl.Cast
open Hacl.UInt8
open Hacl.UInt32
open Hacl.SBuffer

open Hash.Sha256
open HMAC.Sha256

module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module U8 = Hacl.UInt8
module U32 = Hacl.UInt32

let u32 = FStar.UInt32.t
let u64 = FStar.UInt64.t
let s32 = Hacl.UInt32.t
let s8 = Hacl.UInt8.t
let uint32s = u32s
let bytes = u8s


#set-options "--lax"


// Define missing function
assume val xor_bytes: bytes -> bytes -> bytes -> u32 -> St unit 
assume val be_bytes_of_uint32: bytes -> u32 -> St unit

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


// BB.TODO: memory safety clause is missing for now
// We could simplify the memory safety clause by reducing to modifies_1 _T h0 h1
val hkdf_expand_inner : (t       :bytes) ->
                        (prk     :bytes { length prk >= v hl /\ disjoint t prk }) ->
                        (prklen  :u32   { length prk = v prklen }) ->
                        (info    :bytes { disjoint t info /\ disjoint prk info }) ->
                        (infolen :u32   { length info = v infolen }) ->
                        (n       :u32) ->
                        (i       :u32) ->
                        (ti      :bytes { length ti = (v hl) + (v infolen) + 1
                                           /\ disjoint ti t /\ disjoint ti prk /\ disjoint ti info }) ->
                        (til     :bytes { length til = v hl
                                           /\ disjoint til t /\ disjoint til prk
                                           /\ disjoint til info /\ disjoint til ti})
                        -> STL unit
                             (requires (fun h -> live h t /\ live h prk /\ live h info /\ live h ti /\ live h til))
                             (ensures  (fun h0 r h1 -> live h1 t /\ live h1 prk /\ live h1 info /\ live h1 ti /\ live h1 til))

let rec hkdf_expand_inner t prk prklen info infolen n i ti til =
  let _i = create 0uy 4ul in
  if i = 1ul then begin
    let _til = create 0uy (infolen +^ 1ul) in
    be_bytes_of_uint32 _i i;
    blit info 0ul _til 0ul infolen;
    blit _i 0ul _til infolen 1ul;
    hmac ti prk prklen _til (infolen +^ 1ul);
    blit ti 0ul t 0ul hl;
    hkdf_expand_inner t prk prklen info infolen n (i +^ 1ul) ti til end
  else if lte i n then begin
    be_bytes_of_uint32 _i i;
    blit ti 0ul til 0ul hl;
    blit info 0ul til hl infolen;
    blit _i 0ul til (hl +^ infolen) 1ul;
    hmac ti prk prklen til (hl +^ infolen +^ 1ul);
    let pos = mul_mod (i -^ 1ul) hl in
    blit ti 0ul t pos hl;
    hkdf_expand_inner t prk prklen info infolen n (i +^ 1ul) ti til end
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
    let r = rem l hl in
    (div (l -^ r) hl) +^ 1ul
  in
  let _Til = create 0uy (hl +^ infolen +^ 1ul) in
  let _Ti = create 0uy hl in
  let _T = create 0uy (mul_mod n hl) in
  hkdf_expand_inner _T prk prklen info infolen n 1ul _Ti _Til;
  blit _T 0ul okm 0ul l
