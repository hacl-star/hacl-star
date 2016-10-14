module Hash.Sha256.Pure

open FStar.Ghost
open FStar.Heap
open FStar.Seq


(* Define base types *)
let u32 = FStar.UInt32.t
let u64 = FStar.UInt64.t
let s64 = Hacl.UInt64.t
let s32 = Hacl.UInt32.t
let s8 = Hacl.UInt8.t
let uint32s = Hacl.SBuffer.u32s
let bytes = Seq.seq Hacl.UInt8.t


(* Define operators *)
let op_At_Amp (a:s64) (s:s64) : Tot s64 = Hacl.UInt64.logand a s
let op_At_At_Amp = UInt64.logand
let op_Hat_Greater_Greater (a:s32) (b:u32) : Tot s32 = Hacl.UInt32.shift_right a b
let op_At_Plus (a:u32) (b:u32) : Tot u32 = FStar.UInt32.add_mod a b
let op_At_Subtraction (a:u32) (b:u32) : Tot u32 = FStar.UInt32.sub_mod a b
let op_At_Slash (a:u32) (b:u32{v b <> 0}) : Tot u32 = FStar.UInt32.div a b


(* Byte operations *)
assume val uint8_of_string: string -> Tot uint8

(* Infix operators *)
let op_Hat_Less_Less = uint32_shift_left
let op_Hat_Greater_Greater = uint32_shift_right
let op_Hat_Plus = uint32_add
let op_Hat_Plus_Percent = uint32_add_mod
let op_Hat_Subtraction = uint32_sub
let op_Hat_Subtraction_Percent = uint32_sub_mod
let op_Hat_Star = uint32_mul
let op_Hat_Star_Percent = uint32_mul_mod
let op_Hat_Star_Hat = uint32_mul_wide
let op_Hat_Bang = uint32_lognot
let op_Hat_Hat = uint32_logxor
let op_Hat_Amp = uint32_logand
let op_Hat_Bar = uint32_logor
let op_Hat_Less_Less_Less = uint32_rotate_left
let op_Hat_Greater_Greater_Greater = uint32_rotate_right


(*( 
 * Casting functions 
)*)

(* Encode an integer into a uint64 *)
assume val cast_uint64_of_int: x:int -> Tot uint64

(* Convert big endian bytes to uint32 *)
assume val cast_uint32_of_uint8s: s:uint8s{Seq.length s = 4} -> Tot uint32

(* Convert an uint32 into big endian bytes *)
assume val cast_uint8s_of_uint32: s:uint32 -> Tot (res:uint8s{Seq.length res = 4})

(* Convert an uint8 into big endian bytes *)
assume val cast_uint8s_of_uint8: x:uint8 -> Tot (res:uint8s {Seq.length res = 1})

(* Convert an uint64 into big endian bytes *)
assume val cast_uint8s_of_uint64: x:uint64 -> Tot (res:uint8s {Seq.length res = 8})

(* Convert bytes to sequence of uint32 *)
assume val cast_uint32s_of_uint8s: s:uint8s -> l:nat{l % 4 = 0} -> Tot (res:uint32s{((Prims.op_Multiply (Seq.length res) 4) = l)})

(* Convert a sequence of uint32 into bytes *)
assume val cast_uint8s_of_uint32s: x:uint32s -> Tot (res:uint8s)



(*( 
 * Hash function constants 
)*)

// Define the hash length (in bytes)
let hl = 32ul
// Define the hash number of 32bit words
let hw = 8ul
// Define the blocksize (in bytes)
let bs = 64ul
// Define the size of the encoded length (in bytes)
let sl = 8ul
// Define the block iteration count
let ic = 16ul


(* [FIPS 180-4] section 4.1.2 *)
private val _Ch: x:uint32 -> y:uint32 -> z:uint32 -> Tot (res:uint32 { res = ((x ^& y) ^^ ((uint32_lognot x) ^& z)) })
private val _Maj: x:uint32 -> y:uint32 -> z:uint32 -> Tot (res:uint32 { res = ((x ^& y) ^^ ((x ^& z) ^^ (y ^& z))) })
private val _Sigma0: x:uint32 -> Tot (res:uint32 { res = ((x ^>>> 2) ^^ ((x ^>>> 13) ^^ (x ^>>> 22)))})
private val _Sigma1: x:uint32 -> Tot (res:uint32 { res = ((x ^>>> 6) ^^ ((x ^>>> 11) ^^ (x ^>>> 25)))})
private val _sigma0: x:uint32 -> Tot (res:uint32 { res = ((x ^>>> 7) ^^ ((x ^>>> 18) ^^ (x ^>> 3)))})
private val _sigma1: x:uint32 -> Tot (res:uint32 { res = ((x ^>>> 17) ^^ ((x ^>>> 19) ^^ (x ^>> 10)))})


(* [FIPS 180-4] section 4.2.2 *)
private val k_init: unit
  -> Tot (k:(seq uint32) { Seq.length k = 64
        /\ Seq.index k 0 = (uint32_of_string "0x428a2f98")
        /\ Seq.index k 0  = (uint32_of_string "0x428a2f98")
        /\ Seq.index k 1  = (uint32_of_string "0x71374491")
        /\ Seq.index k 2  = (uint32_of_string "0xb5c0fbcf")
        /\ Seq.index k 3  = (uint32_of_string "0xe9b5dba5")
        /\ Seq.index k 4  = (uint32_of_string "0x3956c25b")
        /\ Seq.index k 5  = (uint32_of_string "0x59f111f1")
        /\ Seq.index k 6  = (uint32_of_string "0x923f82a4")
        /\ Seq.index k 7  = (uint32_of_string "0xab1c5ed5")
        /\ Seq.index k 8  = (uint32_of_string "0xd807aa98")
        /\ Seq.index k 9  = (uint32_of_string "0x12835b01")
        /\ Seq.index k 10 = (uint32_of_string "0x243185be")
        /\ Seq.index k 11 = (uint32_of_string "0x550c7dc3")
        /\ Seq.index k 12 = (uint32_of_string "0x72be5d74")
        /\ Seq.index k 13 = (uint32_of_string "0x80deb1fe")
        /\ Seq.index k 14 = (uint32_of_string "0x9bdc06a7")
        /\ Seq.index k 15 = (uint32_of_string "0xc19bf174")
        /\ Seq.index k 16 = (uint32_of_string "0xe49b69c1")
        /\ Seq.index k 17 = (uint32_of_string "0xefbe4786")
        /\ Seq.index k 18 = (uint32_of_string "0x0fc19dc6")
        /\ Seq.index k 19 = (uint32_of_string "0x240ca1cc")
        /\ Seq.index k 20 = (uint32_of_string "0x2de92c6f")
        /\ Seq.index k 21 = (uint32_of_string "0x4a7484aa")
        /\ Seq.index k 22 = (uint32_of_string "0x5cb0a9dc")
        /\ Seq.index k 23 = (uint32_of_string "0x76f988da")
        /\ Seq.index k 24 = (uint32_of_string "0x983e5152")
        /\ Seq.index k 25 = (uint32_of_string "0xa831c66d")
        /\ Seq.index k 26 = (uint32_of_string "0xb00327c8")
        /\ Seq.index k 27 = (uint32_of_string "0xbf597fc7")
        /\ Seq.index k 28 = (uint32_of_string "0xc6e00bf3")
        /\ Seq.index k 29 = (uint32_of_string "0xd5a79147")
        /\ Seq.index k 30 = (uint32_of_string "0x06ca6351")
        /\ Seq.index k 31 = (uint32_of_string "0x14292967")
        /\ Seq.index k 32 = (uint32_of_string "0x27b70a85")
        /\ Seq.index k 33 = (uint32_of_string "0x2e1b2138")
        /\ Seq.index k 34 = (uint32_of_string "0x4d2c6dfc")
        /\ Seq.index k 35 = (uint32_of_string "0x53380d13")
        /\ Seq.index k 36 = (uint32_of_string "0x650a7354")
        /\ Seq.index k 37 = (uint32_of_string "0x766a0abb")
        /\ Seq.index k 38 = (uint32_of_string "0x81c2c92e")
        /\ Seq.index k 39 = (uint32_of_string "0x92722c85")
        /\ Seq.index k 40 = (uint32_of_string "0xa2bfe8a1")
        /\ Seq.index k 41 = (uint32_of_string "0xa81a664b")
        /\ Seq.index k 42 = (uint32_of_string "0xc24b8b70")
        /\ Seq.index k 43 = (uint32_of_string "0xc76c51a3")
        /\ Seq.index k 44 = (uint32_of_string "0xd192e819")
        /\ Seq.index k 45 = (uint32_of_string "0xd6990624")
        /\ Seq.index k 46 = (uint32_of_string "0xf40e3585")
        /\ Seq.index k 47 = (uint32_of_string "0x106aa070")
        /\ Seq.index k 48 = (uint32_of_string "0x19a4c116")
        /\ Seq.index k 49 = (uint32_of_string "0x1e376c08")
        /\ Seq.index k 50 = (uint32_of_string "0x2748774c")
        /\ Seq.index k 51 = (uint32_of_string "0x34b0bcb5")
        /\ Seq.index k 52 = (uint32_of_string "0x391c0cb3")
        /\ Seq.index k 53 = (uint32_of_string "0x4ed8aa4a")
        /\ Seq.index k 54 = (uint32_of_string "0x5b9cca4f")
        /\ Seq.index k 55 = (uint32_of_string "0x682e6ff3")
        /\ Seq.index k 56 = (uint32_of_string "0x748f82ee")
        /\ Seq.index k 57 = (uint32_of_string "0x78a5636f")
        /\ Seq.index k 58 = (uint32_of_string "0x84c87814")
        /\ Seq.index k 59 = (uint32_of_string "0x8cc70208")
        /\ Seq.index k 60 = (uint32_of_string "0x90befffa")
        /\ Seq.index k 61 = (uint32_of_string "0xa4506ceb")
        /\ Seq.index k 62 = (uint32_of_string "0xbef9a3f7")
        /\ Seq.index k 63 = (uint32_of_string "0xc67178f2")
        })

(* [FIPS 180-4] section 5.1.1 *)
(* Compute the number of 512 bit blocks to store data (56 bytes) and padding (8 bytes) *)
(* l + 1 + k ≡ 448 mod 512 *)
private val nblocks: l:nat
  -> Tot (n:nat {n >= 1 /\ (Prims.op_Multiply (n - 1) bs) + 56 = l})

(* Get the last block of the working structure *)
private val get_partial_block: (wdata:uint32s {length wdata = hw})
  -> Tot (block:bytes {Seq.length block <= bs})
  
(* Compute the length [pl] of the padding according to the length [rl] of the data in the last block *)
private val pad_length: rl:nat
  -> Tot (pl:nat { pl <= bs /\ (rl % 64) + pl = 64})

(* Encode length of the raw data [rlen] into [sl] bytes *)
private val pad_encode_data_length: rlen:nat
  -> Tot (b:bytes {length b = sl /\ b = cast_uint8s_of_uint64 (cast_uint64_of_int rlen)})

(* Compute the length [ppl] of the non-encoding padding prefix from the total length [pl] of the padding *)
private val pad_prefix_length: pl:nat
  -> Tot (ppl:nat { ppl = pl - sl /\ ppl >= 1 })

(* Set the non-encoding part of the padding to a one followed by zeros *)
private val pad_prefix: l:nat {l >= 1}
  -> Tot (b:bytes {length b = l /\ b = ((cast_uint8s_of_uint8 (uint8_of_string "0x80")) ^@ (l_create_zeros (l - 1))) })

(* Predicates for the Merkle Damgard padding *)
let is_MD_pad (rlen:nat) (b:bytes) : Tot bool =
  b = ((pad_prefix (pad_length rlen)) ^@ (pad_encode_data_length rlen))
let is_MD_pad_t (rlen:nat) (b:bytes) : Tot Type0 =
  b2t (is_MD_pad rlen b)

(* The padding has length (pad_length [rlen]) and encodes properly the length (pad_length_encode [rdata]) *)
private val pad_compute: rlen:nat
  -> Tot (pad:bytes { length pad = (pad_length rlen) 
        /\ is_MD_pad_t rlen pad 
        /\ pad = ((pad_prefix (pad_length rlen)) ^@ (pad_encode_data_length rlen))})

(* Predicates for conservation of the Merkle Damgard padding property *)
let has_MD_pad (prefix:bytes) (rlen:nat) (b:bytes) : Tot bool =
  b = (prefix ^@ pad_compute rlen)
let has_MD_pad_t (prefix:bytes) (rlen:nat) (b:bytes) : Tot Type0 =
  b2t (has_MD_pad prefix rlen b)

(* Compute the padding and concatenate it to the raw data [rdata] to get the result [pdata] *)
val pad: (rdata:bytes) -> (rlen :nat { length rdata = rlen })
  -> Tot (pdata:bytes {pdata = (rdata ^@ (pad_compute rlen)) /\ has_MD_pad_t rdata rlen pdata})

(* Store function to change the finalized data representation from bytes [pdata] to an array of words [wdata] *)
// BB.TODO: Introduce some lemma to show semantic equivalence of the two representations
private val store: (pdata:bytes) -> (plen:nat {Seq.length pdata = plen /\ plen % 4 = 0})
  -> Tot (wdata:uint32s { wdata = ( cast_uint32s_of_uint8s pdata plen) })


(* [FIPS 180-4] section 6.2.2 *)
(* Step 1 : Scheduling function for sixty-four 32bit words *)
let rec wsched (wblock:uint32s{Seq.length wblock = bs}) (t:nat{t<bs}) : Tot uint32 =
  if t < 16 then
    Seq.index wblock t
  else
    let _t16 = wsched wblock (t-16) in
    let _t15 = wsched wblock (t-15) in
    let _t7 = wsched wblock (t-7) in
    let _t2 = wsched wblock (t-2) in
    
    let _s2 = _sigma1 _t2 in
    let _s15 = _sigma0 _t15 in

    let _a1 = uint32_add_mod _s15 _t16 in
    let _a2 = uint32_add_mod _t7 _a1 in
    uint32_add_mod _s2 _a2


(* [FIPS 180-4] section 5.3.3 *)
(* Define the initial hash value [whash] of the scheduling function *)
private val init: unit
  -> Tot (whash:uint32s { Seq.length whash = 8
        /\ Seq.index whash 0 = (uint32_of_string "0x428a2f98")
        /\ Seq.index whash 0 = (uint32_of_string "0x6a09e667")
        /\ Seq.index whash 1 = (uint32_of_string "0xbb67ae85")
        /\ Seq.index whash 2 = (uint32_of_string "0x3c6ef372")
        /\ Seq.index whash 3 = (uint32_of_string "0xa54ff53a")
        /\ Seq.index whash 4 = (uint32_of_string "0x510e527f")
        /\ Seq.index whash 5 = (uint32_of_string "0x9b05688c")
        /\ Seq.index whash 6 = (uint32_of_string "0x1f83d9ab")
        /\ Seq.index whash 7 = (uint32_of_string "0x5be0cd19")
        })


(* Step 3 : Perform logical operations on the working variables *)
let rec update_inner (whash:uint32s{Seq.length whash = hw}) (wblock:uint32s{Seq.length wblock = bs}) (k:uint32s{Seq.length k = bs}) (t:nat{t>= 1 /\ t <= bs}) : Tot (owhash:uint32s) =
  admit ();
  if t = bs then
    whash
  else
    let _a = index whash 0 in
    let _b = index whash 1 in
    let _c = index whash 2 in
    let _d = index whash 3 in
    let _e = index whash 4 in
    let _f = index whash 5 in
    let _g = index whash 6 in
    let _h = index whash 7 in

    let _t1 = uint32_add_mod _h
                             (uint32_add_mod (_Sigma1 _e)
                                             (uint32_add_mod (_Ch _e _f _g)
                                                             (uint32_add_mod (index k t) (wsched wblock t)))) in
    let _t2 = uint32_add_mod (_Sigma0 _a) (_Maj _a _b _c) in
    
    let whash = upd whash 7 _g in
    let whash = upd whash 6 _f in
    let whash = upd whash 5 _e in
    let whash = upd whash 4 (uint32_add_mod _d _t1) in
    let whash = upd whash 3 _c in
    let whash = upd whash 2 _b in
    let whash = upd whash 1 _a in
    let whash = upd whash 0 (uint32_add_mod _t1 _t2) in
    update_inner whash wblock k (t-1)



(* [FIPS 180-4] section 6.2.2 *)
(* Update running hash function *)
// BB.TODO: Predicate to describe the fact that this happens after init
val update: (whash:uint32s{Seq.length whash = 8 }) -> (data:bytes) -> (rounds:nat) 
  -> Tot (whash:uint32s {Seq.length whash = 8 })


(* Compute the final value of the hash from the last hash value *)
// BB.TODO: Predicate to describe the fact that the data has been updated at least one
val finalize: (whash:uint32s {Seq.length whash = hw})
  -> Tot (hash:bytes {Seq.length hash = hl})


(* Merkle Damgard *)
let is_Merkle_Damgard_scheme (data:bytes) (hash:bytes) : Tot bool =
  hash = (finalize (update (init ()) data (nblocks (Seq.length data))))
let is_Merkle_Damgard_scheme_t (data:bytes) (hash:bytes) : Tot Type0 =
  b2t (hash = (finalize (update (init ()) data (nblocks (Seq.length data)))))

(* Compute the sha256 hash of some bytes *)
val sha265: (data:bytes) -> (len:nat { Seq.length data = len })
  -> Tot (hash:bytes {Seq.length hash = hl 
        /\ is_Merkle_Damgard_scheme_t data hash
        /\ hash = (finalize (update (init ()) data (nblocks (Seq.length data))))})
