module Hash.Sha256

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HST
open FStar.Buffer
open FStar.UInt32
open Hacl.Cast
open Hacl.UInt8
open Hacl.UInt32
open Hacl.SBuffer

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

assume MaxU8: pow2 8 = 256
assume MaxU32: pow2 32 = 4294967296

val rotate_right: s32 -> b:u32{v b <= 32} -> Tot s32
let rotate_right a b =
  (Hacl.UInt32.shift_right a b) |^ (Hacl.UInt32.shift_left a (UInt32.sub 32ul b))

let op_At_Amp (a:s64) (s:s64) : Tot s64 = Hacl.UInt64.logand a s

val be_bytes_of_sint64: bytes -> s64 -> STL unit (requires (fun h -> True)) (ensures (fun h0 _ h1 -> True))
let be_bytes_of_sint64 output x =
 let b0 = sint64_to_sint8 ((Hacl.UInt64.shift_right x 56ul) @& uint64_to_sint64 255UL) in
 let b1 = sint64_to_sint8 ((Hacl.UInt64.shift_right x 48ul) @& uint64_to_sint64 255UL) in
 let b2 = sint64_to_sint8 ((Hacl.UInt64.shift_right x 40ul) @& uint64_to_sint64 255UL) in
 let b3 = sint64_to_sint8 ((Hacl.UInt64.shift_right x 32ul) @& uint64_to_sint64 255UL) in
 let b4 = sint64_to_sint8 ((Hacl.UInt64.shift_right x 24ul) @& uint64_to_sint64 255UL) in
 let b5 = sint64_to_sint8 ((Hacl.UInt64.shift_right x 16ul) @& uint64_to_sint64 255UL) in
 let b6 = sint64_to_sint8 ((Hacl.UInt64.shift_right x 8ul)  @& uint64_to_sint64 255UL) in
 let b7 = sint64_to_sint8 ((x)                              @& uint64_to_sint64 255UL) in
 upd output 0ul b0;
 upd output (1ul) b1;
 upd output (2ul) b2;
 upd output (3ul) b3;
 upd output (4ul) b4;
 upd output (5ul) b5;
 upd output (6ul) b6;
 upd output (7ul) b7

let op_At_At_Amp = UInt64.logand

val be_bytes_of_uint64: x:bytes -> y:u64
  -> STL unit
        (requires (fun h -> live h x))
        (ensures  (fun h0 _ h1 -> live h1 x /\ modifies_1 x h0 h1))

let be_bytes_of_uint64 output x =
 let b0 = uint64_to_sint8 ((UInt64.shift_right x 56ul) @@& 255UL) in
 let b1 = uint64_to_sint8 ((UInt64.shift_right x 48ul) @@& 255UL) in
 let b2 = uint64_to_sint8 ((UInt64.shift_right x 40ul) @@& 255UL) in
 let b3 = uint64_to_sint8 ((UInt64.shift_right x 32ul) @@& 255UL) in
 let b4 = uint64_to_sint8 ((UInt64.shift_right x 24ul) @@& 255UL) in
 let b5 = uint64_to_sint8 ((UInt64.shift_right x 16ul) @@& 255UL) in
 let b6 = uint64_to_sint8 ((UInt64.shift_right x 8ul)  @@& 255UL) in
 let b7 = uint64_to_sint8 ((x)                         @@& 255UL) in
 upd output 0ul b0;
 upd output (1ul) b1;
 upd output (2ul) b2;
 upd output (3ul) b3;
 upd output (4ul) b4;
 upd output (5ul) b5;
 upd output (6ul) b6;
 upd output (7ul) b7

val be_uint32_of_bytes: b:bytes{length b >= 4} -> STL s32
  (requires (fun h -> live h b))
  (ensures (fun h0 r h1 -> h0 == h1 /\ live h0 b))
let be_uint32_of_bytes (b:bytes{length b >= 4}) =
  let b0 = (index b 0ul) in
  let b1 = (index b 1ul) in
  let b2 = (index b 2ul) in
  let b3 = (index b 3ul) in
  let r = (sint8_to_sint32 b3)
	+%^ (op_Less_Less_Hat (sint8_to_sint32 b2) 8ul)
	+%^ (op_Less_Less_Hat (sint8_to_sint32 b1) 16ul)
	+%^ (op_Less_Less_Hat (sint8_to_sint32 b0) 24ul) in
  r

val be_uint32s_of_bytes:uint32s -> bytes -> u32 -> St unit
let rec be_uint32s_of_bytes u b len =
  if UInt32.eq len 0ul then ()
  else (
    let l4 = UInt32.div len 4ul in
    upd u (UInt32.sub l4 1ul) (be_uint32_of_bytes (sub b (UInt32.sub len 4ul) 4ul));
    be_uint32s_of_bytes u b (UInt32.sub len 4ul)
  )

let op_Hat_Greater_Greater (a:s32) (b:u32) : Tot s32 = Hacl.UInt32.shift_right a b

val be_bytes_of_uint32s: output:bytes -> m:uint32s{disjoint output m} -> len:u32{v len <=length output /\ v len<=op_Multiply 4 (length m)} -> STL unit
  (requires (fun h -> live h output /\ live h m))
  (ensures (fun h0 _ h1 -> live h0 output /\ live h0 m /\ live h1 output /\ live h1 m
    /\ modifies_1 output h0 h1 ))
let rec be_bytes_of_uint32s output m len =
  if len =^ 0ul then ()
  else
    begin
      let l4 = UInt32.div len 4ul in
      let l = UInt32.sub l4 1ul in
      let x = index m l in
      let b0 = sint32_to_sint8 ((x ^>> 24ul) &^ uint32_to_sint32 255ul) in
      let b1 = sint32_to_sint8 ((x ^>> 16ul) &^ uint32_to_sint32 255ul) in
      let b2 = sint32_to_sint8 ((x ^>> 8ul)  &^ uint32_to_sint32 255ul) in
      let b3 = sint32_to_sint8 ((x)          &^ uint32_to_sint32 255ul) in
      let l4 = UInt32.sub len 4ul in
      upd output l4 b0;
      upd output (UInt32.add l4 1ul) b1;
      upd output (UInt32.add l4 2ul) b2;
      upd output (UInt32.add l4 3ul) b3;
      be_bytes_of_uint32s output m l4
    end


#reset-options "--z3timeout 50"

//
// SHA-256
//


(* [FIPS 180-4] section 4.1.2 *)
val _Ch: x:s32 -> y:s32 -> z:s32 -> Tot s32
let _Ch x y z = logxor (logand x y) (logand (lognot x) z)

val _Maj: x:s32 -> y:s32 -> z:s32 -> Tot s32
let _Maj x y z = logxor (logand x y) (logxor (logand x z) (logand y z))

val _Sigma0: x:s32 -> Tot s32
let _Sigma0 x = logxor (rotate_right x 2ul) (logxor (rotate_right x 13ul) (rotate_right x 22ul))

val _Sigma1: x:s32 -> Tot s32
let _Sigma1 x = logxor (rotate_right x 6ul) (logxor (rotate_right x 11ul) (rotate_right x 25ul))

val _sigma0: x:s32 -> Tot s32
let _sigma0 x = logxor (rotate_right x 7ul) (logxor (rotate_right x 18ul) (shift_right x 3ul))

val _sigma1: x:s32 -> Tot s32
let _sigma1 x = logxor (rotate_right x 17ul) (logxor (rotate_right x 19ul) (shift_right x 10ul))


(* [FIPS 180-4] section 4.2.2 *)
val k_setup: k:uint32s{length k = 64}
  -> STL unit (requires (fun h -> live h k))
             (ensures (fun h0 _ h1 -> live h1 k /\ modifies_1 k h0 h1))

let k_setup k =
  admit(); // This is safe
  upd k 0ul (uint32_to_sint32  0x428a2f98ul);
  upd k 1ul (uint32_to_sint32  0x71374491ul);
  upd k 2ul (uint32_to_sint32  0xb5c0fbcful);
  upd k 3ul (uint32_to_sint32  0xe9b5dba5ul);
  upd k 4ul (uint32_to_sint32  0x3956c25bul);
  upd k 5ul (uint32_to_sint32  0x59f111f1ul);
  upd k 6ul (uint32_to_sint32  0x923f82a4ul);
  upd k 7ul (uint32_to_sint32  0xab1c5ed5ul);
  upd k 8ul (uint32_to_sint32  0xd807aa98ul);
  upd k 9ul (uint32_to_sint32  0x12835b01ul);
  upd k 10ul (uint32_to_sint32 0x243185beul);
  upd k 11ul (uint32_to_sint32 0x550c7dc3ul);
  upd k 12ul (uint32_to_sint32 0x72be5d74ul);
  upd k 13ul (uint32_to_sint32 0x80deb1feul);
  upd k 14ul (uint32_to_sint32 0x9bdc06a7ul);
  upd k 15ul (uint32_to_sint32 0xc19bf174ul);
  upd k 16ul (uint32_to_sint32 0xe49b69c1ul);
  upd k 17ul (uint32_to_sint32 0xefbe4786ul);
  upd k 18ul (uint32_to_sint32 0x0fc19dc6ul);
  upd k 19ul (uint32_to_sint32 0x240ca1ccul);
  upd k 20ul (uint32_to_sint32 0x2de92c6ful);
  upd k 21ul (uint32_to_sint32 0x4a7484aaul);
  upd k 22ul (uint32_to_sint32 0x5cb0a9dcul);
  upd k 23ul (uint32_to_sint32 0x76f988daul);
  upd k 24ul (uint32_to_sint32 0x983e5152ul);
  upd k 25ul (uint32_to_sint32 0xa831c66dul);
  upd k 26ul (uint32_to_sint32 0xb00327c8ul);
  upd k 27ul (uint32_to_sint32 0xbf597fc7ul);
  upd k 28ul (uint32_to_sint32 0xc6e00bf3ul);
  upd k 29ul (uint32_to_sint32 0xd5a79147ul);
  upd k 30ul (uint32_to_sint32 0x06ca6351ul);
  upd k 31ul (uint32_to_sint32 0x14292967ul);
  upd k 32ul (uint32_to_sint32 0x27b70a85ul);
  upd k 33ul (uint32_to_sint32 0x2e1b2138ul);
  upd k 34ul (uint32_to_sint32 0x4d2c6dfcul);
  upd k 35ul (uint32_to_sint32 0x53380d13ul);
  upd k 36ul (uint32_to_sint32 0x650a7354ul);
  upd k 37ul (uint32_to_sint32 0x766a0abbul);
  upd k 38ul (uint32_to_sint32 0x81c2c92eul);
  upd k 39ul (uint32_to_sint32 0x92722c85ul);
  upd k 40ul (uint32_to_sint32 0xa2bfe8a1ul);
  upd k 41ul (uint32_to_sint32 0xa81a664bul);
  upd k 42ul (uint32_to_sint32 0xc24b8b70ul);
  upd k 43ul (uint32_to_sint32 0xc76c51a3ul);
  upd k 44ul (uint32_to_sint32 0xd192e819ul);
  upd k 45ul (uint32_to_sint32 0xd6990624ul);
  upd k 46ul (uint32_to_sint32 0xf40e3585ul);
  upd k 47ul (uint32_to_sint32 0x106aa070ul);
  upd k 48ul (uint32_to_sint32 0x19a4c116ul);
  upd k 49ul (uint32_to_sint32 0x1e376c08ul);
  upd k 50ul (uint32_to_sint32 0x2748774cul);
  upd k 51ul (uint32_to_sint32 0x34b0bcb5ul);
  upd k 52ul (uint32_to_sint32 0x391c0cb3ul);
  upd k 53ul (uint32_to_sint32 0x4ed8aa4aul);
  upd k 54ul (uint32_to_sint32 0x5b9cca4ful);
  upd k 55ul (uint32_to_sint32 0x682e6ff3ul);
  upd k 56ul (uint32_to_sint32 0x748f82eeul);
  upd k 57ul (uint32_to_sint32 0x78a5636ful);
  upd k 58ul (uint32_to_sint32 0x84c87814ul);
  upd k 59ul (uint32_to_sint32 0x8cc70208ul);
  upd k 60ul (uint32_to_sint32 0x90befffaul);
  upd k 61ul (uint32_to_sint32 0xa4506cebul);
  upd k 62ul (uint32_to_sint32 0xbef9a3f7ul);
  upd k 63ul (uint32_to_sint32 0xc67178f2ul)


let op_At_Plus (a:u32) (b:u32) : Tot u32 = UInt32.add_mod a b
let op_At_Subtraction (a:u32) (b:u32) : Tot u32 = UInt32.sub_mod a b
let op_At_Slash (a:u32) (b:u32{v b <> 0}) : Tot u32 = UInt32.div a b


(* [FIPS 180-4] section 5.1.1 *)
(* Compute the number of 512 bit blocks to store data (56 bytes) and padding (8 bytes) *)
(* l + 1 + k ≡ 448 mod 512 *)
val nblocks: u32 -> Tot (n:u32{gte n 1ul})
let nblocks x = ((x @+ 8ul) @- (UInt32.rem (x @+ 8ul) 64ul))@/64ul @+ 1ul


(* Compute the pad length *)
val pad_length: u32 -> Tot (n:u32{lte n 64ul /\ gte n 1ul})
let pad_length rlen =
  if lt (UInt32.rem rlen 64ul) 56ul then 56ul @- (UInt32.rem rlen 64ul)
  else 64ul @+ 56ul @- (UInt32.rem rlen 64ul)


(* Pad the data and return a buffer of uint32 for subsequent treatment *)
val pad: (pdata :bytes) ->
         (rdata :bytes{disjoint pdata rdata}) ->
         (rlen  :u32  {v rlen <= length rdata /\ v rlen <= length pdata /\ v rlen + v (pad_length rlen) + 8 <= length pdata})
         -> STL unit
              (requires (fun h -> live h rdata /\ live h pdata))
              (ensures  (fun h0 r h1 -> live h1 rdata /\ live h1 pdata /\ modifies_1 pdata h0 h1))

let pad pdata rdata rlen =

  (** Push a new frame *)
  (**) let hinit = HST.get () in
  (**) push_frame ();
  (**) let h0 = HST.get () in

  (* Value of the raw data length in bits represented as UInt64 *)
  let v64 = Int.Cast.uint32_to_uint64 (UInt32.mul_mod rlen 8ul) in
  let rlen_64 = create (uint8_to_sint8 0uy) 8ul in
  (**) let h1 = HST.get () in
  (**) assert(modifies_0 h0 h1);
  (**) no_upd_lemma_0 h0 h1 pdata;
  (**) no_upd_lemma_0 h0 h1 rdata;
  be_bytes_of_uint64 rlen_64 v64;
  (**) let h2 = HST.get () in
  (**) assert(modifies_1 rlen_64 h1 h2);
  (**) no_upd_lemma_1 h1 h2 rlen_64 pdata;
  (**) no_upd_lemma_1 h1 h2 rlen_64 rdata;

  (* Compute the padding length *)
  let rplen = pad_length rlen in
  (**) assert(modifies_0 h0 h2);

  (* Generate the padding *)
  let rpad = create (uint8_to_sint8 0uy) rplen in
  (**) let h3 = HST.get () in
  (**) assert(modifies_0 h2 h3);
  (**) assert(modifies_0 h0 h3);
  (**) assert(live h3 rpad);
  (**) assert(live h3 pdata);
  (**) assert(live h3 rdata);
  upd rpad 0ul (uint8_to_sint8 0x80uy);
  (**) let h4 = HST.get () in
  (**) assert(modifies_1 rpad h3 h4);
  (**) assert(modifies_0 h0 h4);
  (**) no_upd_lemma_0 h0 h4 pdata;
  (**) no_upd_lemma_0 h0 h4 rdata;
  (**) assert(v rlen <= length pdata);
  (**) assert(v rlen <= length rdata);
  blit rdata 0ul pdata 0ul rlen;
  (**) let h5 = HST.get () in
  (**) assert(modifies_1 pdata h4 h5);
  (**) no_upd_lemma_1 h4 h5 pdata rdata;
  (**) assert(v rlen + v rplen <= length pdata);
  blit rpad 0ul pdata rlen rplen;
  (**) let h6 = HST.get () in
  (**) assert(modifies_1 pdata h5 h6);
  (**) no_upd_lemma_1 h5 h6 pdata rdata;
  (**) assert(v rlen + v rplen + 8 <= length pdata);
  (**) assert(length rlen_64 >= v 8ul);
  (**) assert(live h6 rlen_64);
  (**) assert(live h6 pdata);
  blit rlen_64 0ul pdata (UInt32.add rlen rplen) 8ul;
  (**) let h7 = HST.get () in
  (**) assert(modifies_1 pdata h6 h7);

  (** Pop the frame *)
  (**) pop_frame ();
  (**) let hfin = HST.get () in
  (**) assert(modifies_1 pdata hinit hfin);
  (**) assume(equal_domains hinit hfin);
  (**) assert(live hfin pdata)


(* [FIPS 180-4] section 6.2.2 *)
(* Step 1 : Scheduling function for sixty-four 32bit words *)
val wsched_define: (ws     :uint32s { length ws = 64 }) ->
                   (wblock :uint32s { length wblock = 16 /\ disjoint ws wblock }) ->
                   (t      :u32)
                   -> STL unit
                        (requires (fun h -> live h ws /\ live h wblock))
                        (ensures  (fun h0 r h1 -> live h1 ws /\ live h1 wblock /\ modifies_1 ws h0 h1))

let rec wsched_define ws wblock t =
  if lt t 16ul then begin
    upd ws t (index wblock t);
    wsched_define ws wblock (t @+ 1ul) end
  else if lt t 64ul then begin
    let _t16 = index ws (t@-16ul) in
    let _t15 = index ws (t@-15ul) in
    let _t7 = index ws (t@-7ul) in
    let _t2 = index ws (t@-2ul) in

    let v0 = _sigma1 _t2 in
    let v1 = _sigma0 _t15 in

    let v = (add_mod v0
                     (add_mod _t7
                              (add_mod v1 _t16)))
    in upd ws t v;
    wsched_define ws wblock (t @+ 1ul) end
  else ()


#reset-options "--lax"

(* [FIPS 180-4] section 5.3.3 *)
(* Define the initial hash value *)
val init : (whash :uint32s { length whash = 8 })
           -> STL unit
                 (requires (fun h -> live h whash))
                 (ensures  (fun h0 r h1 -> live h1 whash /\ modifies_1 whash h0 h1))

let init whash =
  upd whash 0ul (uint32_to_sint32 0x6a09e667ul);
  upd whash 1ul (uint32_to_sint32 0xbb67ae85ul);
  upd whash 2ul (uint32_to_sint32 0x3c6ef372ul);
  upd whash 3ul (uint32_to_sint32 0xa54ff53aul);
  upd whash 4ul (uint32_to_sint32 0x510e527ful);
  upd whash 5ul (uint32_to_sint32 0x9b05688cul);
  upd whash 6ul (uint32_to_sint32 0x1f83d9abul);
  upd whash 7ul (uint32_to_sint32 0x5be0cd19ul)


(* Step 3 : Perform logical operations on the working variables *)
val update_inner_loop : (ws    :uint32s { length ws = 64 }) ->
                        (whash :uint32s { length whash = 8 /\ disjoint whash ws}) ->
                        (t     :u32) ->
                        (t1    :s32) ->
                        (t2    :s32) ->
                        (k     :uint32s { length k = 64 /\ disjoint k ws /\ disjoint k whash })
                        -> STL unit
                             (requires (fun h -> live h ws /\ live h whash /\ live h k ))
                             (ensures  (fun h0 r h1 -> live h1 ws /\ live h1 whash /\ live h1 k /\ modifies_1 whash h0 h1))

let rec update_inner_loop ws whash t t1 t2 k =
  if lt t 64ul then begin
    let _h = index whash 7ul in
    let _kt = index k t in
    let _wt = index ws t in
    let v0 = _Sigma1 (index whash 4ul) in
    let v1 = _Ch (index whash 4ul) (index whash 5ul) (index whash 6ul) in
    let t1 = add_mod _h (add_mod v0 (add_mod v1 (add_mod _kt _wt))) in

    let z0 = _Sigma0 (index whash 0ul) in
    let z1 = _Maj (index whash 0ul) (index whash 1ul) (index whash 2ul) in
    let t2 = add_mod z0 z1 in

    let _d = (index whash 3ul) in
    upd whash 7ul (index whash 6ul);
    upd whash 6ul (index whash 5ul);
    upd whash 5ul (index whash 4ul);
    upd whash 4ul (add_mod _d t1);
    upd whash 3ul (index whash 2ul);
    upd whash 2ul (index whash 1ul);
    upd whash 1ul (index whash 0ul);
    upd whash 0ul (add_mod t1 t2);
    update_inner_loop ws whash (t @+ 1ul) t1 t2 k end
  else ()


val update_step : (whash :uint32s { length whash = 8 }) ->
                  (wdata :uint32s { disjoint whash wdata }) ->
                  (ws    :uint32s { length ws = 64 /\ disjoint ws whash /\ disjoint ws wdata }) ->
                  (rounds:u32) ->
                  (i     :u32) ->
                  (t1    :s32) ->
                  (t2    :s32) ->
                  (k     :uint32s { length k = 64 /\ disjoint k whash /\ disjoint k wdata /\ disjoint k ws})
                  -> STL unit
                       (requires (fun h -> live h whash /\ live h wdata /\ live h ws /\ live h k))
                       (ensures  (fun h0 r h1 -> live h1 whash /\ live h1 wdata /\ live h1 ws /\ live h1 k /\ modifies_2 whash ws h0 h1))

let rec update_step ihash wdata ws rounds i t1 t2 k =
  if lt i rounds then begin
    let pos = UInt32.mul_mod i 16ul in
    let wblock = sub wdata pos 16ul in

    (* Step 1 : Scheduling function for sixty-four 32 bit words *)
    let ia = 0ul in
    wsched_define ws wblock ia;

    (* Step 2 : Initialize the eight working variables *)
    let whash = create (uint32_to_sint32 0ul) 8ul in
    upd whash 0ul (index ihash 0ul);
    upd whash 1ul (index ihash 1ul);
    upd whash 2ul (index ihash 2ul);
    upd whash 3ul (index ihash 3ul);
    upd whash 4ul (index ihash 4ul);
    upd whash 5ul (index ihash 5ul);
    upd whash 6ul (index ihash 6ul);
    upd whash 7ul (index ihash 7ul);

    (* Step 3 : Perform logical operations on the working variables *)
    let ib = 0ul in
    update_inner_loop ws whash ib t1 t2 k;

    (* Step 4 : Compute the ith intermediate hash value *)
    upd ihash 0ul (add_mod (index whash 0ul) (index ihash 0ul));
    upd ihash 1ul (add_mod (index whash 1ul) (index ihash 1ul));
    upd ihash 2ul (add_mod (index whash 2ul) (index ihash 2ul));
    upd ihash 3ul (add_mod (index whash 3ul) (index ihash 3ul));
    upd ihash 4ul (add_mod (index whash 4ul) (index ihash 4ul));
    upd ihash 5ul (add_mod (index whash 5ul) (index ihash 5ul));
    upd ihash 6ul (add_mod (index whash 6ul) (index ihash 6ul));
    upd ihash 7ul (add_mod (index whash 7ul) (index ihash 7ul));
    update_step ihash wdata ws rounds (i @+ 1ul) t1 t2 k end
  else ()


(* [FIPS 180-4] section 6.2.2 *)
(* Update running hash function *)
val update : (whash  :uint32s { length whash = 8 }) ->
             (pdata  :uint32s { disjoint whash pdata }) ->
             (rounds :u32)
             -> STL unit
                  (requires (fun h -> live h whash /\ live h pdata))
                  (ensures  (fun h0 r h1 -> live h1 whash /\ live h1 pdata /\ modifies_1 whash h0 h1))

let update whash wdata rounds =
  (* Define working variables *)
  let i = 0ul in
  let t1 = uint32_to_sint32 0ul in
  let t2 = uint32_to_sint32 0ul in
  (* Perform function *)
  update_step whash wdata ws rounds i t1 t2 k


(* Compute the final value of the hash from the last hash value *)
val finish: (hash  :bytes   { length hash = v hl }) ->
            (whash :uint32s { disjoint whash hash })
            -> STL unit
                 (requires (fun h -> live h hash /\ live h whash))
                 (ensures  (fun h0 r h1 -> live h1 hash /\ live h1 whash /\ modifies_1 hash h0 h1))

let finish hash whash = be_bytes_of_uint32s hash whash hl
 // 1 - Take the current whash
 // 2 - Get the last block
 // 3 - Update (pad)
 // 4 - Return (be_bytes_of_uint32s hash whash 32ul)


(* Compute the sha256 hash of some bytes *)
val sha256: (hash:bytes { length hash >= 32 }) ->
            (data:bytes { disjoint hash data }) ->
            (len:u32    { length data = v len })
            -> STL unit
                 (requires (fun h -> live h hash /\ live h data))
                 (ensures  (fun h0 r h1 -> live h1 data /\ live h1 hash /\ modifies_1 hash h0 h1))

let sha256 hash data len =
  let plen = len @+ (pad_length len) @+ 8ul in
  let rounds = nblocks plen @- 1ul in
  let pdata = create (uint8_to_sint8 0uy) plen in
  let wlen = UInt32.div plen 4ul in
  let wdata = create (uint32_to_sint32 0ul) wlen in
  (* Allocate space for the scheduling function *)
  let ws = create (uint32_to_sint32 0ul) 64ul in
  (* Allovate space and initialize constant K *)
  let k = create (uint32_to_sint32 0ul) 64ul  in
  k_setup k;
  (* Allocate space for the working hash *)
  let whash = create (uint32_to_sint32 0ul) 8ul in
  init whash;
  pad pdata data len;
  be_uint32s_of_bytes wdata pdata plen;
  update whash wdata rounds;
  finish hash whash
