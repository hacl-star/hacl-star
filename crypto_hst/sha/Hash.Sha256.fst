module Hash.Sha256

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HST
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
let s32 = Hacl.UInt32.t
let s8 = Hacl.UInt8.t
let uint32s = u32s
let bytes = u8s


#set-options "--lax"


// Missing functions
assume val rotate_right: u32 -> u32 -> Tot u32
assume val be_bytes_of_uint64: bytes -> u64 -> St unit
assume val uint64_of_uint32: u32 -> Tot u64
assume val be_uint32s_of_bytes:uint32s -> bytes -> u32 -> St unit
assume val be_bytes_of_uint32s:bytes -> uint32s -> u32 -> St unit


(* [FIPS 180-4] section 4.1.2 *)
val _Ch: x:u32 -> y:u32 -> z:u32 -> Tot u32
let _Ch x y z = logxor (logand x y) (logand (lognot x) z)

val _Maj: x:u32 -> y:u32 -> z:u32 -> Tot u32
let _Maj x y z = logxor (logand x y) (logxor (logand x z) (logand y z))

val _Sigma0: x:u32 -> Tot u32
let _Sigma0 x = logxor (rotate_right x 2ul) (logxor (rotate_right x 13ul) (rotate_right x 22ul))

val _Sigma1: x:u32 -> Tot u32
let _Sigma1 x = logxor (rotate_right x 6ul) (logxor (rotate_right x 11ul) (rotate_right x 25ul))

val _sigma0: x:u32 -> Tot u32
let _sigma0 x = logxor (rotate_right x 7ul) (logxor (rotate_right x 18ul) (shift_right x 3ul))

val _sigma1: x:u32 -> Tot u32
let _sigma1 x = logxor (rotate_right x 17ul) (logxor (rotate_right x 19ul) (shift_right x 10ul))


(* [FIPS 180-4] section 4.2.2 *)

val k_init: unit -> St (uint32s)
let k_init () =
  let k = create 0ul 64ul  in
  upd k 0ul  0x428a2f98ul;
  upd k 1ul  0x71374491ul;
  upd k 2ul  0xb5c0fbcful;
  upd k 3ul  0xe9b5dba5ul;
  upd k 4ul  0x3956c25bul;
  upd k 5ul  0x59f111f1ul;
  upd k 6ul  0x923f82a4ul;
  upd k 7ul  0xab1c5ed5ul;
  upd k 8ul  0xd807aa98ul;
  upd k 9ul  0x12835b01ul;
  upd k 10ul 0x243185beul;
  upd k 11ul 0x550c7dc3ul;
  upd k 12ul 0x72be5d74ul;
  upd k 13ul 0x80deb1feul;
  upd k 14ul 0x9bdc06a7ul;
  upd k 15ul 0xc19bf174ul;
  upd k 16ul 0xe49b69c1ul;
  upd k 17ul 0xefbe4786ul;
  upd k 18ul 0x0fc19dc6ul;
  upd k 19ul 0x240ca1ccul;
  upd k 20ul 0x2de92c6ful;
  upd k 21ul 0x4a7484aaul;
  upd k 22ul 0x5cb0a9dcul;
  upd k 23ul 0x76f988daul;
  upd k 24ul 0x983e5152ul;
  upd k 25ul 0xa831c66dul;
  upd k 26ul 0xb00327c8ul;
  upd k 27ul 0xbf597fc7ul;
  upd k 28ul 0xc6e00bf3ul;
  upd k 29ul 0xd5a79147ul;
  upd k 30ul 0x06ca6351ul;
  upd k 31ul 0x14292967ul;
  upd k 32ul 0x27b70a85ul;
  upd k 33ul 0x2e1b2138ul;
  upd k 34ul 0x4d2c6dfcul;
  upd k 35ul 0x53380d13ul;
  upd k 36ul 0x650a7354ul;
  upd k 37ul 0x766a0abbul;
  upd k 38ul 0x81c2c92eul;
  upd k 39ul 0x92722c85ul;
  upd k 40ul 0xa2bfe8a1ul;
  upd k 41ul 0xa81a664bul;
  upd k 42ul 0xc24b8b70ul;
  upd k 43ul 0xc76c51a3ul;
  upd k 44ul 0xd192e819ul;
  upd k 45ul 0xd6990624ul;
  upd k 46ul 0xf40e3585ul;
  upd k 47ul 0x106aa070ul;
  upd k 48ul 0x19a4c116ul;
  upd k 49ul 0x1e376c08ul;
  upd k 50ul 0x2748774cul;
  upd k 51ul 0x34b0bcb5ul;
  upd k 52ul 0x391c0cb3ul;
  upd k 53ul 0x4ed8aa4aul;
  upd k 54ul 0x5b9cca4ful;
  upd k 55ul 0x682e6ff3ul;
  upd k 56ul 0x748f82eeul;
  upd k 57ul 0x78a5636ful;
  upd k 58ul 0x84c87814ul;
  upd k 59ul 0x8cc70208ul;
  upd k 60ul 0x90befffaul;
  upd k 61ul 0xa4506cebul;
  upd k 62ul 0xbef9a3f7ul;
  upd k 63ul 0xc67178f2ul;
  k


(* [FIPS 180-4] section 5.1.1 *)

(* Compute the number of 512 bit blocks to store data (56 bytes) and padding (8 bytes) *)
(* l + 1 + k ≡ 448 mod 512 *)
val nblocks: u32 -> Tot (n:u32{gte n 1ul})
let nblocks x = ((x +^ 8ul) -^ (rem (x +^ 8ul) 64ul))/^64ul +^ 1ul


(* Compute the pad length *)
val pad_length: u32 -> Tot (n:u32{lte n 64ul})
let pad_length rlen =
  if lt (rem rlen 64ul) 56ul then 56ul -^ (rem rlen 64ul)
  else 64ul +^ 56ul -^ (rem rlen 64ul)


(* Pad the data and return a buffer of uint32 for subsequent treatment *)
val pad: (pdata :bytes) ->
         (rdata :bytes{disjoint pdata rdata}) ->
         (rlen  :u32{ v rlen = length rdata})
         -> STL unit
              (requires (fun h -> live h rdata /\ live h pdata))
              (ensures  (fun h0 r h1 -> live h1 rdata /\ live h1 pdata /\ modifies_1 pdata h0 h1))
let pad pdata rdata rlen =
  // Value of the raw data length in bits represented as UInt64
  let rlen_64 =
    let v = create 0uy 8ul in
    let v64 = uint64_of_uint32 (mul_mod rlen 8ul) in
    be_bytes_of_uint64 v v64;
    v
  in
  // Compute the padding length
  let rplen = pad_length rlen in
  // Generate the padding
  let rpad = create 0uy rplen in
  upd rpad 0ul 80uy;
  blit rdata 0ul pdata 0ul rlen;
  blit rpad 0ul pdata rlen rplen;
  blit rlen_64 0ul pdata (rlen +^ rplen) 8ul


(* Store function to handle pdata as a sequence of words *)
val store : (wdata :uint32s) ->
            (pdata :bytes {length pdata = (Prims.op_Multiply 4 (length wdata)) /\ disjoint wdata pdata }) ->
            (plen  :u32   {length pdata = v plen /\ v plen = (Prims.op_Multiply 4 (length wdata)) })
            -> STL unit
                 (requires (fun h -> live h wdata /\ live h pdata))
                 (ensures  (fun h0 r h1 -> live h1 wdata /\ live h1 pdata /\ modifies_1 wdata h0 h1))

let store wdata pdata plen = be_uint32s_of_bytes wdata pdata plen


(* [FIPS 180-4] section 6.2.2 *)

(* Step 1 : Scheduling function for sixty-four 32bit words *)
val wsched_define: (ws     :uint32s { length ws = 64 }) ->
                   (wblock :uint32s { length wblock = 16 /\ disjoint ws wblock }) ->
                   (t      :u32 {v t <= 64})
                   -> STL unit
                        (requires (fun h -> live h ws /\ live h wblock))
                        (ensures  (fun h0 r h1 -> live h1 ws /\ live h1 wblock /\ modifies_1 ws h0 h1))

let rec wsched_define ws wblock t =
  if lt t 16ul then begin
    upd ws t (index wblock t);
    wsched_define ws wblock (t +^ 1ul) end
  else if lt t 64ul then begin
    let _t16 = index ws (t-^16ul) in
    let _t15 = index ws (t-^15ul) in
    let _t7 = index ws (t-^7ul) in
    let _t2 = index ws (t-^2ul) in

    let v0 = _sigma1 _t2 in
    let v1 = _sigma0 _t15 in

    let v = (add_mod v0
                     (add_mod _t7
                              (add_mod v1 _t16)))
    in upd ws t v;
    wsched_define ws wblock (t +^ 1ul) end
  else ()


(* [FIPS 180-4] section 5.3.3 *)

(* Define the initial hash value *)
val init : (whash :uint32s { length whash = 8 })
           -> STL unit
                 (requires (fun h -> live h whash))
                 (ensures  (fun h0 r h1 -> live h1 whash /\ modifies_1 whash h0 h1))

let init whash =
  upd whash 0ul 0x6a09e667ul;
  upd whash 1ul 0xbb67ae85ul;
  upd whash 2ul 0x3c6ef372ul;
  upd whash 3ul 0xa54ff53aul;
  upd whash 4ul 0x510e527ful;
  upd whash 5ul 0x9b05688cul;
  upd whash 6ul 0x1f83d9abul;
  upd whash 7ul 0x5be0cd19ul


(* Step 3 : Perform logical operations on the working variables *)
// BB.TODO: Modifies_3 clause
// BB.TODO: Seems that t1 and t2 are only uint32
val update_inner_loop : (ws    :uint32s { length ws = 64 }) ->
                        (whash :uint32s { length whash = 8 /\ disjoint whash ws}) ->
                        (t     :u32{v t <= 64}) ->
                        (t1    :uint32s { length t1 = 1 /\ disjoint t1 ws /\ disjoint t1 whash}) ->
                        (t2    :uint32s { length t2 = 1 /\ disjoint t2 ws /\ disjoint t2 whash /\ disjoint t2 t1}) ->
                        (k     :uint32s { length k = 64 /\ disjoint k ws /\ disjoint k whash /\ disjoint k t1 /\ disjoint k t2})
                        -> STL unit
                             (requires (fun h -> live h ws /\ live h whash /\ live h t1 /\ live h t2 /\ live h k ))
                             (ensures  (fun h0 r h1 -> live h1 ws /\ live h1 whash /\ live h1 t1 /\ live h1 t2 /\ live h1 k))

let rec update_inner_loop ws whash t t1 t2 k =
  if lt t 64ul then begin
    let _h = index whash 7ul in
    let _kt = index k t in
    let _wt = index ws t in
    let v0 = _Sigma1 (index whash 4ul) in
    let v1 = _Ch (index whash 4ul) (index whash 5ul) (index whash 6ul) in
    let _t1 = add_mod _h (add_mod v0 (add_mod v1 (add_mod _kt _wt))) in
    upd t1 0ul _t1;
    let z0 = _Sigma0 (index whash 0ul) in
    let z1 = _Maj (index whash 0ul) (index whash 1ul) (index whash 2ul) in
    let _t2 = add_mod z0 z1 in
    upd t2 0ul _t2;

    let _d = (index whash 3ul) in
    upd whash 7ul (index whash 6ul);
    upd whash 6ul (index whash 5ul);
    upd whash 5ul (index whash 4ul);
    upd whash 4ul (add_mod _d _t1);
    upd whash 3ul (index whash 2ul);
    upd whash 2ul (index whash 1ul);
    upd whash 1ul (index whash 0ul);
    upd whash 0ul (add_mod _t1 _t2);
    update_inner_loop ws whash (t +^ 1ul) t1 t2 k end
  else ()

// BB.TODO: Add modifies_4 clause
// BB.TODO: Looks like t1 and t2 are u32
val update_step : (whash :uint32s { length whash = 8 }) ->
                  (wdata :uint32s { disjoint whash wdata }) ->
                  (ws    :uint32s { length ws = 64 /\ disjoint ws whash /\ disjoint ws wdata }) ->
                  (rounds:u32) ->
                  (i     :u32) ->
                  (t1    :uint32s { length t1 = 1 /\ disjoint t1 whash /\ disjoint t1 wdata /\ disjoint t1 ws}) ->
                  (t2    :uint32s { length t2 = 1 /\ disjoint t2 whash /\ disjoint t2 wdata /\ disjoint t2 ws /\ disjoint t2 t1}) ->
                  (k     :uint32s { length k = 64 /\ disjoint k whash /\ disjoint k wdata /\ disjoint k ws /\ disjoint k t1 /\ disjoint k t2})
                  -> STL unit
                       (requires (fun h -> live h whash /\ live h wdata /\ live h ws /\ live h t1 /\ live h t2 /\ live h k))
                       (ensures  (fun h0 r h1 -> live h1 whash /\ live h1 wdata /\ live h1 ws /\ live h1 t1 /\ live h1 t2 /\ live h1 k))

let rec update_step ihash wdata ws rounds i t1 t2 k =
  if lt i rounds then begin
    let pos = mul_mod i 16ul in
    let wblock = sub wdata pos 16ul in

    (* Step 1 : Scheduling function for sixty-four 32 bit words *)
    let ia = 0ul in
    wsched_define ws wblock ia;

    (* Step 2 : Initialize the eight working variables *)
    let whash = create 0ul 8ul in
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
    let x01 = index whash 0ul in
    let x02 = index ihash 0ul in
    let x11 = index whash 1ul in
    let x12 = index ihash 1ul in
    let x21 = index whash 2ul in
    let x22 = index ihash 2ul in
    let x31 = index whash 3ul in
    let x32 = index ihash 3ul in
    let x41 = index whash 4ul in
    let x42 = index ihash 4ul in
    let x51 = index whash 5ul in
    let x52 = index ihash 5ul in
    let x61 = index whash 6ul in
    let x62 = index ihash 6ul in
    let x71 = index whash 7ul in
    let x72 = index ihash 7ul in
    upd ihash 0ul (add_mod x01 x02);
    upd ihash 1ul (add_mod x11 x12);
    upd ihash 2ul (add_mod x21 x22);
    upd ihash 3ul (add_mod x31 x32);
    upd ihash 4ul (add_mod x41 x42);
    upd ihash 5ul (add_mod x51 x52);
    upd ihash 6ul (add_mod x61 x62);
    upd ihash 7ul (add_mod x71 x72);
    update_step ihash wdata ws rounds (i +^ 1ul) t1 t2 k end
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
  let t1 = create 0ul 1ul in
  let t2 = create 0ul 1ul in
  (* Scheduling function *)
  let ws = create 0ul 64ul in
  (* Initialize constant *)
  let k = k_init () in
  (* Perform function *)
  update_step whash wdata ws rounds i t1 t2 k


(* Compute the final value of the hash from the last hash value *)
val finish: (hash  :bytes   { length hash = 32 }) ->
            (whash :uint32s { disjoint whash hash })
            -> STL unit
                 (requires (fun h -> live h hash /\ live h whash))
                 (ensures  (fun h0 r h1 -> live h1 hash /\ live h1 whash /\ modifies_1 hash h0 h1))

let finish hash whash = be_bytes_of_uint32s hash whash 8ul


(* Compute the sha256 hash of some bytes *)
val sha265: (hash:bytes { length hash = 32 }) ->
            (data:bytes { disjoint hash data }) ->
            (len:u32    { length data = v len })
            -> STL unit
                 (requires (fun h -> live h hash /\ live h data))
                 (ensures  (fun h0 r h1 -> live h1 data /\ live h1 hash /\ modifies_1 hash h0 h1))

let sha256 hash data len =
  let whash = create 0ul 8ul in
  let plen = len +^ (pad_length len) +^ 8ul in
  let rounds = nblocks plen -^ 1ul in
  let pdata = create 0uy plen in
  let wlen = div plen 4ul in
  let wdata = create 0ul wlen in
  init whash;
  pad pdata data len;
  store wdata pdata plen;
  update whash wdata rounds;
  finish hash whash
