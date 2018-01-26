module Spec.Lib.IntTypes

open FStar.Math.Lemmas


type inttype =
 | U8 | U16 | U32 | U64 | U128 | SIZE

inline_for_extraction
unfold
let bits (n:inttype) =
  match n with
  | U8 -> 8
  | U16 -> 16
  | U32 -> 32
  | U64 -> 64
  | U128 -> 128
  | SIZE -> 32

inline_for_extraction
unfold
let numbytes (n:inttype) =
  match n with
  | U8 -> 1
  | U16 -> 2
  | U32 -> 4
  | U64 -> 8
  | U128 -> 16
  | SIZE -> 4

val pow2_values: n:nat ->  Lemma (
    pow2 0 == 1 /\
    pow2 8 == 0x100 /\
    pow2 16 == 0x10000 /\
    pow2 32 == 0x100000000 /\
    pow2 64 == 0x10000000000000000 /\
    pow2 128 == 0x100000000000000000000000000000000
    )
    [SMTPat (pow2 n)]

inline_for_extraction
unfold
let maxint (t:inttype) = pow2 (bits t) - 1
(*
  match t with
  | U8 -> 0xff
  | U16 -> 0xffff
  | U32 -> 0xffffffff
  | U64 -> 0xffffffffffffffff
  | U128 -> 0xffffffffffffffffffffffffffffffff
*)


inline_for_extraction
val uint_t: t:inttype -> Type0
inline_for_extraction
val uint_v: #t:inttype -> u:uint_t t -> GTot (n:nat{n <= maxint t})

inline_for_extraction
type uint8 = uint_t U8
inline_for_extraction
type uint16 = uint_t U16
inline_for_extraction
type uint32 = uint_t U32
inline_for_extraction
type uint64 = uint_t U64
inline_for_extraction
type uint128 = uint_t U128

inline_for_extraction
val u8: (n:nat{n <= maxint U8}) -> u:uint8{uint_v #U8 u == n}
inline_for_extraction
val u16: (n:nat{n <= maxint U16}) -> u:uint16{uint_v #U16 u == n}

inline_for_extraction
val u32: (n:nat{n <= maxint U32}) -> u:uint32{uint_v #U32 u == n}

inline_for_extraction
val u64: (n:nat{n <= maxint U64}) -> u:uint64{uint_v #U64 u == n}

inline_for_extraction
val u128: (n:nat{n <= maxint U128}) -> u:uint128{uint_v #U128 u == n}

inline_for_extraction
val nat_to_uint: #t:inttype -> (n:nat{n <= maxint t}) -> u:uint_t t{uint_v u == n}

inline_for_extraction
val cast: #t:inttype{t <> SIZE} -> t':inttype{t' <> SIZE} -> u1:uint_t t -> u2:uint_t t'{uint_v u2 == uint_v u1 % pow2 (bits t')}

inline_for_extraction
let to_u8 #t u : uint8 = cast #t U8 u
inline_for_extraction
let to_u16 #t u : uint16 = cast #t U16 u
inline_for_extraction
let to_u32 #t u : uint32 = cast #t U32 u
inline_for_extraction
let to_u64 #t u : uint64 = cast #t U64 u
inline_for_extraction
let to_u128 #t u : uint128 = cast #t U128 u

inline_for_extraction
val add_mod: #t:inttype -> a:uint_t t -> b:uint_t t -> c:uint_t t {uint_v c == (uint_v a + uint_v b) % pow2 (bits t)}


inline_for_extraction
val add: #t:inttype -> a:uint_t t -> b:uint_t t -> Pure (uint_t t)
  (requires (uint_v a + uint_v b < pow2 (bits t)))
  (ensures (fun c -> uint_v c == uint_v a + uint_v b))

inline_for_extraction
val incr: #t:inttype -> a:uint_t t -> Pure (uint_t t)
  (requires (uint_v a < pow2 (bits t) - 1))
  (ensures (fun c -> uint_v c == uint_v a + 1))

inline_for_extraction
val mul_mod: #t:inttype{t <> U128} -> a:uint_t t -> b:uint_t t -> c:uint_t t {uint_v c == (uint_v a `op_Multiply` uint_v b) % pow2 (bits t)}

inline_for_extraction
val mul: #t:inttype{t <> U128} -> a:uint_t t -> b:uint_t t -> Pure (uint_t t)
  (requires (uint_v a `op_Multiply` uint_v b < pow2 (bits t)))
  (ensures (fun c -> uint_v c == uint_v a `op_Multiply` uint_v b))

inline_for_extraction
val mul_wide: a:uint64 -> b:uint64 -> Pure (uint128)
  (requires (True))
  (ensures (fun c -> uint_v #U128 c == uint_v #U64 a `op_Multiply` uint_v #U64 b))

(* I would prefer the post-condition to say: uint_v c = (pow2 (bits t) + uint_v a - uint_v b) % pow2 (bits t) *)
inline_for_extraction
val sub_mod: #t:inttype -> a:uint_t t -> b:uint_t t -> c:uint_t t{uint_v c == (uint_v a - uint_v b) % pow2 (bits t)}
inline_for_extraction
val sub: #t:inttype -> a:uint_t t -> b:uint_t t -> Pure (uint_t t)
  (requires (uint_v a >= uint_v b ))
  (ensures (fun c -> uint_v c == uint_v a - uint_v b))

inline_for_extraction
val decr: #t:inttype -> a:uint_t t -> Pure (uint_t t)
  (requires (uint_v a > 0))
  (ensures (fun c -> uint_v c == uint_v a - 1))

inline_for_extraction
val logxor: #t:inttype -> a:uint_t t  -> b:uint_t t -> uint_t t
inline_for_extraction
val logand: #t:inttype -> a:uint_t t  ->
b:uint_t t -> uint_t t
inline_for_extraction
val logor: #t:inttype -> a:uint_t t  ->
b:uint_t t -> uint_t t
inline_for_extraction
val lognot: #t:inttype -> a:uint_t t -> uint_t t

inline_for_extraction
type shiftval (t:inttype) = u:uint32{uint_v #U32 u < bits t}
inline_for_extraction
type rotval  (t:inttype) = u:uint32{uint_v #U32 u > 0 /\ uint_v #U32 u < bits t}

inline_for_extraction
val shift_right: #t:inttype -> a:uint_t t -> b:shiftval t ->
    c:uint_t t{uint_v #t c ==  uint_v #t a / pow2 (uint_v #U32 b)}

inline_for_extraction
val shift_left: #t:inttype -> a:uint_t t -> b:shiftval t ->
    c:uint_t t{uint_v #t c == (uint_v #t a `op_Multiply` pow2 (uint_v #U32 b)) % pow2 (bits t)}

inline_for_extraction
val rotate_right: #t:inttype -> a:uint_t t -> b:rotval t -> uint_t t

inline_for_extraction
val rotate_left: #t:inttype -> a:uint_t t -> b:rotval t -> uint_t t

inline_for_extraction
val eq_mask: #t:inttype -> a:uint_t t  -> b:uint_t t -> uint_t t

inline_for_extraction
val neq_mask: #t:inttype -> a:uint_t t  -> b:uint_t t -> uint_t t

inline_for_extraction
val gt_mask:  #t:inttype -> a:uint_t t  -> b:uint_t t -> uint_t t

inline_for_extraction
val gte_mask:  #t:inttype -> a:uint_t t  -> b:uint_t t -> uint_t t

inline_for_extraction
val lt_mask:  #t:inttype -> a:uint_t t  -> b:uint_t t -> c:uint_t t

inline_for_extraction
val lte_mask:  #t:inttype -> a:uint_t t  -> b:uint_t t -> uint_t t

val eq_mask_lemma: #t:inttype -> a:uint_t t -> b:uint_t t -> d:uint_t t -> Lemma 
    (requires (True))
    (ensures  ((eq_mask #t a b) `logand` d == (if uint_v a = uint_v b then d else nat_to_uint 0)))
    [SMTPat (eq_mask #t a b `logand` d)]

val neq_mask_lemma: #t:inttype -> a:uint_t t -> b:uint_t t -> d:uint_t t -> Lemma 
    (requires (True))
    (ensures  ((neq_mask #t a b) `logand` d == (if uint_v a <> uint_v b then d else nat_to_uint 0)))
    [SMTPat (neq_mask #t a b `logand` d)]

val gt_mask_lemma: #t:inttype -> a:uint_t t -> b:uint_t t -> d:uint_t t -> Lemma 
    (requires (True))
    (ensures  ((gt_mask #t a b) `logand` d == (if uint_v a > uint_v b then d else nat_to_uint 0)))
    [SMTPat (gt_mask #t a b `logand` d)]

val gte_mask_lemma: #t:inttype -> a:uint_t t -> b:uint_t t -> d:uint_t t -> Lemma 
    (requires (True))
    (ensures  ((gte_mask #t a b) `logand` d == (if uint_v a >= uint_v b then d else nat_to_uint 0)))
    [SMTPat (gte_mask #t a b `logand` d)]

val lt_mask_lemma: #t:inttype -> a:uint_t t -> b:uint_t t -> d:uint_t t -> Lemma 
    (requires (True))
    (ensures  ((lt_mask #t a b) `logand` d == (if uint_v a  < uint_v b then d else nat_to_uint 0)))
    [SMTPat (lt_mask #t a b `logand` d)]

val lte_mask_lemma: #t:inttype -> a:uint_t t -> b:uint_t t -> d:uint_t t -> Lemma 
    (requires (True))
    (ensures  ((lte_mask #t a b) `logand` d == (if uint_v a  <= uint_v b then d else nat_to_uint 0)))
    [SMTPat (lte_mask #t a b `logand` d)]


inline_for_extraction
let (+!) #t = add #t
inline_for_extraction
let (+.) #t = add_mod #t
inline_for_extraction
let ( *! ) #t = mul #t
inline_for_extraction
let ( *. ) #t = mul_mod #t
inline_for_extraction
let ( -! ) #t = sub #t
inline_for_extraction
let ( -. ) #t = sub_mod #t
inline_for_extraction
let ( >>. ) #t = shift_right #t
inline_for_extraction
let ( <<. ) #t = shift_left #t
inline_for_extraction
let ( >>>. ) #t = rotate_right #t
inline_for_extraction
let ( <<<. ) #t = rotate_left #t
inline_for_extraction
let ( ^. ) #t = logxor #t
inline_for_extraction
let ( |. ) #t = logor #t
inline_for_extraction
let ( &. ) #t = logand #t
inline_for_extraction
let ( ~. ) #t = lognot #t

unfold inline_for_extraction
let max_size_t = maxint SIZE

inline_for_extraction
type size_t = uint_t SIZE

inline_for_extraction
type size_nat = n:nat{n <= max_size_t}

inline_for_extraction
val size: n:size_nat -> u:size_t{uint_v #SIZE u == n}

inline_for_extraction
val size_v: s:size_t -> n:size_nat{uint_v #SIZE s == n}

inline_for_extraction
val size_to_uint32: s:size_t -> u:uint32{uint_v #U32 u == size_v s}

inline_for_extraction
val size_incr: s:size_t{size_v s < max_size_t} -> s':size_t{size_v s' == size_v s + 1}

inline_for_extraction
val size_decr: s:size_t{size_v s > 0} -> s':size_t{size_v s' == size_v s - 1}


inline_for_extraction
val size_div: s1:size_t -> s2:size_t{size_v s2 > 0} -> s3:size_t{size_v s3 == size_v s1 / size_v s2}

inline_for_extraction
val size_mod: s1:size_t -> s2:size_t{size_v s2 > 0} -> s3:size_t{size_v s3 == size_v s1 % size_v s2}

inline_for_extraction
val size_eq: s1:size_t -> s2:size_t -> b:bool{b == (size_v s1 = size_v s2)}

inline_for_extraction
val size_lt: s1:size_t -> s2:size_t -> b:bool{b == (size_v s1 < size_v s2)}

inline_for_extraction
val size_le: s1:size_t -> s2:size_t -> b:bool{b == (size_v s1 <= size_v s2)}

inline_for_extraction
val size_gt: s1:size_t -> s2:size_t -> b:bool{b == (size_v s1 > size_v s2)}

inline_for_extraction
val size_ge: s1:size_t -> s2:size_t -> b:bool{b == (size_v s1 >= size_v s2)}

inline_for_extraction
let (/.) = size_div

inline_for_extraction
let (%.) = size_mod

inline_for_extraction
let (=.) = size_eq

inline_for_extraction
let (<.) = size_lt

inline_for_extraction
let (<=.) = size_le

inline_for_extraction
let (>.) = size_gt

inline_for_extraction
let (>=.) = size_ge


inline_for_extraction
val bignum: Type0
inline_for_extraction
val bn_v: bignum -> GTot nat
inline_for_extraction
val bn: nat -> bignum
inline_for_extraction
val bn_add: bignum -> bignum -> bignum
inline_for_extraction
val bn_mul: bignum -> bignum -> bignum
inline_for_extraction
val bn_sub: a:bignum -> b:bignum{bn_v a >= bn_v b} -> bignum
inline_for_extraction
val bn_mod: bignum -> b:bignum{bn_v b <> 0} -> bignum
inline_for_extraction
val bn_div: bignum -> b:bignum{bn_v b <> 0} -> bignum

(*
val uint_v_lemma: #t:inttype -> a:uint_t t -> b:uint_t t -> Lemma 
    (requires (uint_v #t a == uint_v #t b))
    (ensures (a == b))
    [SMTPat (uint_v #t a); SMTPat (uint_v #t b)]
*)
