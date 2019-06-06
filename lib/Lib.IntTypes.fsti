module Lib.IntTypes

open FStar.Mul
open FStar.Math.Lemmas

///
/// Definition of machine integer base types
///

type inttype =
  | U1 | U8 | U16 | U32 | U64 | U128 | S8 | S16 | S32 | S64 | S128

let unsigned (i:inttype) =
  i = U1 ||
  i = U8 ||
  i = U16 ||
  i = U32 ||
  i = U64 ||
  i = U128
let signed (i:inttype) =
  i = S8 ||
  i = S16 ||
  i = S32 ||
  i = S64 ||
  i = S128


///
/// Operations on the underlying machine integer base types
///

inline_for_extraction
let bits (n:inttype) =
  match n with
  | U1 -> 1
  | U8 -> 8
  | S8 -> 8
  | U16 -> 16
  | S16 -> 16
  | U32 -> 32
  | S32 -> 32
  | U64 -> 64
  | S64 -> 64
  | U128 -> 128
  | S128 -> 128


val pow2_values: n:nat ->  Lemma (
    pow2 0 == 1 /\
    pow2 1 == 2 /\
    pow2 2 == 4 /\
    pow2 3 == 8 /\
    pow2 4 == 16 /\
    pow2 8 == 0x100 /\
    pow2 16 == 0x10000 /\
    pow2 32 == 0x100000000 /\
    pow2 64 == 0x10000000000000000 /\
    pow2 128 == 0x100000000000000000000000000000000
    )
    [SMTPat (pow2 n)]

inline_for_extraction
unfold let modulus (t:inttype) = pow2 (bits t)

inline_for_extraction
unfold let maxint (t:inttype) =
  match t with
  | U1 | U8 | U16 | U32 | U64 | U128 -> pow2 (bits t) - 1
  | S8 | S16 | S32 | S64 | S128 -> (pow2 (bits t) / 2) - 1

inline_for_extraction
unfold let minint (t:inttype) =
  match t with
  | U1 | U8 | U16 | U32 | U64 | U128 -> 0
  | S8 | S16 | S32 | S64 | S128 -> - (pow2 (bits t) / 2)

inline_for_extraction
let range (x:int) (n:inttype) : Type0 =
  minint n <= x /\ x <= maxint n

inline_for_extraction
type range_t (n:inttype) = x:int{range x n}

inline_for_extraction
let numbytes (n:inttype) =
  match n with
  | U1 -> 1
  | U8 -> 1
  | S8 -> 1
  | U16 -> 2
  | S16 -> 2
  | U32 -> 4
  | S32 -> 4
  | U64 -> 8
  | S64 -> 8
  | U128 -> 16
  | S128 -> 16


(* PUBLIC Machine Integers *)

inline_for_extraction
let pub_int_t (t:inttype) =
  match t with
  | U1 -> u:UInt8.t{UInt8.v u < 2}
  | U8 -> UInt8.t
  | U16 -> UInt16.t
  | U32 -> UInt32.t
  | U64 -> UInt64.t
  | U128 -> UInt128.t
  | S8 -> Int8.t
  | S16 -> Int16.t
  | S32 -> Int32.t
  | S64 -> Int64.t
  | S128 -> Int128.t

inline_for_extraction
let pub_int_v #t (x:pub_int_t t) : (n:range_t t) =
  match t with
  | U1 -> UInt8.v x
  | U8 -> UInt8.v x
  | U16 -> UInt16.v x
  | U32 -> UInt32.v x
  | U64 -> UInt64.v x
  | U128 -> UInt128.v x
  | S8 -> Int8.v x
  | S16 -> Int16.v x
  | S32 -> Int32.v x
  | S64 -> Int64.v x
  | S128 -> Int128.v x

(* SECRET Machine Integers *)

type secrecy_level =
  | SEC
  | PUB

inline_for_extraction
val sec_int_t: t:inttype -> Type0

inline_for_extraction
val sec_int_v: #t:inttype -> u:sec_int_t t -> n:range_t t

(* GENERIC (unsigned) Machine Integers *)

inline_for_extraction
let int_t (t:inttype) (l:secrecy_level) =
  match l with
  | PUB -> pub_int_t t
  | SEC -> sec_int_t t

let int_v #t #l (u:int_t t l) : n:range_t t =
  match l with
  | PUB -> pub_int_v #t u
  | SEC -> sec_int_v #t u

inline_for_extraction
let uint_t (t:inttype{unsigned t}) (l:secrecy_level) = int_t t l

inline_for_extraction
let sint_t (t:inttype{signed t}) (l:secrecy_level) = int_t t l


let uint_v #t #l (u:uint_t t l) = int_v u
let sint_v #t #l (u:sint_t t l) = int_v u

///
/// Definition of machine integers
///

inline_for_extraction
type uint1 = uint_t U1 SEC

inline_for_extraction
type uint8 = uint_t U8 SEC

inline_for_extraction
type int8 = sint_t S8 SEC

inline_for_extraction
type uint16 = uint_t U16 SEC

inline_for_extraction
type int16 = sint_t S16 SEC

inline_for_extraction
type uint32 = uint_t U32 SEC

inline_for_extraction
type int32 = sint_t S32 SEC

inline_for_extraction
type uint64 = uint_t U64 SEC

inline_for_extraction
type int64 = sint_t S64 SEC

inline_for_extraction
type uint128 = uint_t U128 SEC

inline_for_extraction
type int128 = sint_t S128 SEC

inline_for_extraction
unfold type bit_t = uint_t U1 PUB

inline_for_extraction
unfold type byte_t = uint_t U8 PUB

inline_for_extraction
unfold type size_t = uint_t U32 PUB

inline_for_extraction
unfold type pub_int8 = sint_t S8 PUB

inline_for_extraction
unfold type pub_uint16 = uint_t U16 PUB

inline_for_extraction
unfold type pub_int16 = sint_t S16 PUB

inline_for_extraction
unfold type pub_uint32 = uint_t U32 PUB

inline_for_extraction
unfold type pub_int32 = sint_t S32 PUB

inline_for_extraction
unfold type pub_uint64 = uint_t U64 PUB

inline_for_extraction
unfold type pub_int64 = sint_t S64 PUB

inline_for_extraction
unfold type pub_uint128 = uint_t U128 PUB

inline_for_extraction
unfold type pub_int128 = sint_t S128 PUB
///
/// Casts between natural numbers and machine integers
///

inline_for_extraction
val secret: #t:inttype -> u:int_t t PUB -> v:int_t t SEC{int_v v == int_v u}

inline_for_extraction
val mk_int: #t:inttype -> #l:secrecy_level -> (n:range_t t) -> u:int_t t l{int_v u == n}

inline_for_extraction
let uint (#t:inttype{unsigned t}) (#l:secrecy_level) (n:range_t t) = mk_int #t #l n

inline_for_extraction
let sint (#t:inttype{signed t}) (#l:secrecy_level) (n:range_t t) = mk_int #t #l n

val intv_injective:
   #t:inttype
 -> #l:secrecy_level
 -> a:int_t t l
 -> Lemma (ensures mk_int (int_v #t #l a) == a)
 [SMTPat (int_v #t #l a)]

inline_for_extraction
let u1 (n:range_t U1) : u:uint1{uint_v #U1 u == n} = uint #U1 #SEC n

inline_for_extraction
let u8 (n:range_t U8) : u:uint8{uint_v #U8 u == n} = uint #U8 #SEC n

inline_for_extraction
let i8 (n:range_t S8) : u:int8{sint_v #S8 u == n} = sint #S8 #SEC n

inline_for_extraction
let u16 (n:range_t U16) : u:uint16{uint_v #U16 u == n} = uint #U16 #SEC n

inline_for_extraction
let i16 (n:range_t S16) : u:int16{sint_v #S16 u == n} = sint #S16 #SEC n

inline_for_extraction
let u32 (n:range_t U32) : u:uint32{uint_v #U32 u == n} = uint #U32 #SEC n

inline_for_extraction
let i32 (n:range_t S32) : u:int32{sint_v #S32 u == n} = sint #S32 #SEC n

inline_for_extraction
let u64 (n:range_t U64) : u:uint64{uint_v #U64 u == n} = uint #U64 #SEC n

inline_for_extraction
let i64 (n:range_t S64) : u:int64{sint_v #S64 u == n} = sint #S64 #SEC n

(* We only support 64-bit literals, hence the unexpected upper limit in the following functions *)
inline_for_extraction
let u128 (n:range_t U64) : u:uint128{uint_v #U128 u == n} = uint #U128 #SEC n

inline_for_extraction
let i128 (n:range_t S64) : u:int128{sint_v #S128 u == n} = sint #S128 #SEC n

unfold noextract
let max_size_t = maxint U32

unfold inline_for_extraction
type size_nat = n:nat{n <= max_size_t}

unfold inline_for_extraction
type size_pos = n:pos{n <= max_size_t}

inline_for_extraction
let size (n:size_nat) : size_t = uint #U32 #PUB n

unfold inline_for_extraction
let size_v (s:size_t) = uint_v #U32 #PUB s

unfold inline_for_extraction noextract
let v #t #l x = int_v #t #l x

val size_v_size_lemma: s:size_nat ->
  Lemma
  (ensures (size_v (size s) == s))
  [SMTPat (size_v (size s))]

val uint_v_size_lemma: s:size_nat ->
  Lemma
  (ensures (uint_v (size s) == s))
  [SMTPat (uint_v (size s))]

inline_for_extraction
let byte (n:nat{n < 256}) : b:byte_t{uint_v b == n} = uint #U8 #PUB n

inline_for_extraction
let byte_v (s:byte_t) : n:size_nat{uint_v s == n} = pub_int_v (s <: pub_int_t U8)

inline_for_extraction
val size_to_uint32: s:size_t -> u:uint32{u == u32 (uint_v s)}

inline_for_extraction
val size_to_uint64: s:size_t -> u:uint64{u == u64 (uint_v s)}

inline_for_extraction
val byte_to_uint8: s:byte_t -> u:uint8{u == u8 (byte_v s)}

let op_At_Percent = Int.op_At_Percent

#reset-options
inline_for_extraction
val byte_to_int8: s:byte_t -> u:int8{u == i8 ((byte_v s) @% 256)}

inline_for_extraction
val nat_to_int: #t:inttype -> #l:secrecy_level -> (n:range_t t) -> u:int_t t l{int_v u == n}

inline_for_extraction
let nat_to_uint (#t:inttype{unsigned t}) (#l:secrecy_level) (n:range_t t) = nat_to_int #t #l n

inline_for_extraction
let op_At_Percent_Dot x t =
  match t with
  | U1 | U8 | U16 | U32 | U64 | U128 -> x % modulus t
  | S8 | S16 | S32 | S64 | S128 -> x @% modulus t

inline_for_extraction
val cast: #t:inttype -> #l:secrecy_level
          -> t':inttype{(~(U128? t')) \/ (U1? t) \/ (U8? t) \/ (U16? t) \/ (U32? t) \/ (U64? t) \/ (U128? t)} -> l':secrecy_level {PUB? l \/ SEC? l'}
          -> u1:int_t t l -> u2:int_t t' l'{int_v u2 == int_v u1 @%. t'}

inline_for_extraction
let to_u1 #t #l u : uint1 = cast #t #l U1 SEC u

inline_for_extraction
let to_u8 #t #l u : uint8 = cast #t #l U8 SEC u

inline_for_extraction
let to_i8 #t #l u : int8 = cast #t #l S8 SEC u

inline_for_extraction
let to_u16 #t #l u : uint16 = cast #t #l U16 SEC u

inline_for_extraction
let to_i16 #t #l u : int16 = cast #t #l S16 SEC u

inline_for_extraction
let to_u32 #t #l u : uint32 = cast #t #l U32 SEC u

inline_for_extraction
let to_i32 #t #l u : int32 = cast #t #l S32 SEC u

inline_for_extraction
let to_u64 #t #l u : uint64 = cast #t #l U64 SEC u

inline_for_extraction
let to_i64 #t #l u : int64 = cast #t #l S64 SEC u

inline_for_extraction
let to_u128 (#t:inttype{(U1? t) \/ (U8? t) \/ (U16? t) \/ (U32? t) \/ (U64? t) \/ (U128? t)}) #l u : uint128 = cast #t #l U128 SEC u

inline_for_extraction
let to_i128 #t #l u : int128 = cast #t #l S128 SEC u

///
/// Bitwise operators for all machine integers
///

inline_for_extraction
val add_mod: #t:inttype -> #l:secrecy_level ->
             a:int_t t l ->
             b:int_t t l ->
             c:int_t t l

inline_for_extraction
val add_mod_lemma: #t:inttype -> #l:secrecy_level ->
             a:int_t t l ->
             b:int_t t l ->
	     Lemma
	     (ensures (int_v #t #l (add_mod #t #l a b) == (int_v a + int_v b) @%. t))
	     [SMTPat (int_v #t #l (add_mod #t #l a b))]

inline_for_extraction
val add: #t:inttype -> #l:secrecy_level
  -> a:int_t t l
  -> b:int_t t l{range (int_v a + int_v b) t}
  -> int_t t l

inline_for_extraction
val add_lemma: #t:inttype -> #l:secrecy_level
  -> a:int_t t l
  -> b:int_t t l{range (int_v a + int_v b) t}
  -> Lemma
    (ensures (int_v #t #l (add #t #l a b) == int_v a + int_v b))
    [SMTPat (int_v #t #l (add #t #l a b))]

inline_for_extraction
val incr: #t:inttype -> #l:secrecy_level
  -> a:int_t t l{int_v a < maxint t}
  -> int_t t l

inline_for_extraction
val incr_lemma: #t:inttype -> #l:secrecy_level
  -> a:int_t t l{int_v a < maxint t}
  -> Lemma
  (ensures (int_v #t #l (incr a) == int_v a + 1))

inline_for_extraction
val mul_mod: #t:inttype{t <> U128} -> #l:secrecy_level
  -> a:int_t t l
  -> b:int_t t l
  -> int_t t l

inline_for_extraction
val mul_mod_lemma: #t:inttype{t <> U128} -> #l:secrecy_level
  -> a:int_t t l
  -> b:int_t t l
  -> Lemma
  (ensures (int_v #t #l (mul_mod #t #l a b) == (int_v a `op_Multiply` int_v b) @%. t))
  [SMTPat (int_v #t #l (mul_mod #t #l a b))]

inline_for_extraction
val mul: #t:inttype{t <> U128} -> #l:secrecy_level
  -> a:int_t t l
  -> b:int_t t l{range (int_v a `op_Multiply` int_v b) t}
  -> int_t t l


inline_for_extraction
val mul_lemma: #t:inttype{t <> U128} -> #l:secrecy_level
  -> a:int_t t l
  -> b:int_t t l{range (int_v a `op_Multiply` int_v b) t}
  -> Lemma
  (ensures (int_v #t #l (mul #t #l a b) == int_v a `op_Multiply` int_v b))
  [SMTPat (int_v #t #l (mul #t #l a b))]


inline_for_extraction
val mul64_wide: a:uint64 -> b:uint64 -> uint128

inline_for_extraction
val mul64_wide_lemma: a:uint64 -> b:uint64
  -> Lemma
  (ensures (uint_v (mul64_wide a b) == uint_v a `op_Multiply` uint_v b))
  [SMTPat (uint_v (mul64_wide a b))]

//inline_for_extraction
//val mulsigned64_wide: a:int64 -> b:int64 -> int128

//inline_for_extraction
//val mulsigned64_wide_lemma: a:int64 -> b:int64
  //-> Lemma
  //(ensures (uint_v (mulsigned64_wide a b) == uint_v a `op_Multiply` uint_v b))
  //[SMTPat (uint_v (mulsigned64_wide a b))]
(* KB: I would prefer the post-condition to say:
       uint_v c = (pow2 (bits t) + uint_v a - uint_v b) % pow2 (bits t)
*)
inline_for_extraction
val sub_mod: #t:inttype -> #l:secrecy_level
  -> a:int_t t l
  -> b:int_t t l
  -> c:int_t t l

inline_for_extraction
val sub_mod_lemma: #t:inttype -> #l:secrecy_level ->
             a:int_t t l ->
             b:int_t t l ->
	     Lemma
	     (ensures (int_v #t #l (sub_mod #t #l a b) == (int_v a - int_v b) @%. t))
	     [SMTPat (int_v #t #l (sub_mod #t #l a b))]

inline_for_extraction
val sub: #t:inttype -> #l:secrecy_level
  -> a:int_t t l
  -> b:int_t t l{range (int_v a - int_v b) t}
  -> int_t t l

inline_for_extraction
val sub_lemma: #t:inttype -> #l:secrecy_level ->
             a:int_t t l ->
             b:int_t t l{range (int_v a - int_v b) t} ->
	     Lemma
	     (ensures (int_v #t #l (sub #t #l a b) == int_v a - int_v b))
	     [SMTPat (int_v #t #l (sub #t #l a b))]

inline_for_extraction
val decr: #t:inttype -> #l:secrecy_level
  -> a:int_t t l{int_v a > minint t}
  -> int_t t l

inline_for_extraction
val decr_lemma: #t:inttype -> #l:secrecy_level
  -> a:int_t t l{int_v a > minint t}
  -> Lemma
  (ensures (int_v #t #l (decr a) == int_v a - 1))

inline_for_extraction
let zero (t:inttype) = 0

inline_for_extraction
let one (t:inttype) = 1

#reset-options
inline_for_extraction
let ones_v (t:inttype) =
  match t with
  | U1 | U8 | U16 | U32 | U64 | U128 -> maxint t
  | S8 | S16 | S32 | S64 | S128 -> -1


inline_for_extraction
val logxor: #t:inttype -> #l:secrecy_level
  -> a:int_t t l
  -> b:int_t t l
  -> int_t t l

val logxor_lemma: #t:inttype -> #l:secrecy_level -> a:int_t t l -> b:int_t t l -> Lemma
  (a `logxor` (a `logxor` b) == b /\
   a `logxor` (b `logxor` a) == b /\
   a `logxor` (mk_int #t #l 0) == a)

val logxor_lemma1: #t:inttype -> #l:secrecy_level -> a:int_t t l -> b:int_t t l -> Lemma
  (requires range (v a) U1 /\ range (v b) U1)
  (ensures range (v (a `logxor` b)) U1)

inline_for_extraction
val logand: #t:inttype -> #l:secrecy_level
  -> a:int_t t l
  -> b:int_t t l
  -> int_t t l

val logand_lemma: #t:inttype{~(U1? t)} -> a:int_t t SEC -> b:int_t t SEC -> Lemma
  (requires v a = zero t \/ v a = ones_v t)
  (ensures (if v a = zero t then v (a `logand` b) == zero t else v (a `logand` b) == v b))

let logand_v (#t:inttype{~(U1? t)}) (a: range_t t) (b:range_t t) : range_t t=
match t with
  |S8 | S16 | S32 | S64 | S128 -> Int.logand #(8*numbytes t) a b
  |_ -> UInt.logand #(8*numbytes t) a b

val logand_spec: #t:inttype{~(U1? t)} -> #l:secrecy_level
  -> a:int_t t l -> b:int_t t l
  -> Lemma (ensures (v (a `logand` b) == (v a `logand_v` v b)))
  //[SMTPat (v (a `logand` b))]

inline_for_extraction
val logor: #t:inttype -> #l:secrecy_level
  -> a:int_t t l
  -> b:int_t t l
  -> int_t t l

val logor_disjoint: #t:inttype{(U1? t) \/ (U8? t) \/ (U16? t) \/ (U32? t) \/ (U64? t) \/ (U128? t)} -> a:int_t t SEC -> b:int_t t SEC -> m:nat{m < bits t} -> Lemma
  (requires 0 <= v a /\ v a < pow2 m /\ v b % pow2 m == 0)
  (ensures v (a `logor` b) == v a + v b)

inline_for_extraction
val lognot: #t:inttype -> #l:secrecy_level
  -> a:int_t t l
  -> int_t t l

inline_for_extraction
type shiftval (t:inttype) = u:size_t{int_v u < bits t}

inline_for_extraction
type rotval  (t:inttype) = u:size_t{int_v u > 0 /\ int_v u < bits t}

inline_for_extraction
val shift_right: #t:inttype -> #l:secrecy_level
  -> a:int_t t l
  -> b:shiftval t
  -> c:int_t t l

val shift_right_lemma: #t:inttype -> #l:secrecy_level
  -> a:int_t t l
  -> b:shiftval t
  -> Lemma
    (ensures int_v #t #l (shift_right #t #l a b) ==  int_v #t #l a / pow2 (int_v #U32 #PUB b))
    [SMTPat (int_v #t #l (shift_right #t #l a b))]

inline_for_extraction
val shift_left: #t:inttype -> #l:secrecy_level
  -> a:int_t t l
  -> b:shiftval t
  -> c:int_t t l

val shift_left_lemma: #t:inttype -> #l:secrecy_level
  -> a:int_t t l
  -> b:shiftval t
  -> Lemma
    (int_v #t #l (shift_left #t #l a b) == (int_v #t #l a `op_Multiply` pow2 (int_v #U32 #PUB b)) @%. t)
    [SMTPat (int_v #t #l (shift_left #t #l a b))]

inline_for_extraction
val rotate_right: #t:inttype -> #l:secrecy_level
  -> a:int_t t l
  -> b:rotval t
  -> int_t t l

inline_for_extraction
val rotate_left: #t:inttype -> #l:secrecy_level
  -> a:int_t t l
  -> b:rotval t
  -> int_t t l

///
/// Masking operators for all machine integers
///

inline_for_extraction
val zeroes: t:inttype -> l:secrecy_level -> v:int_t t l{int_v v = zero t}

inline_for_extraction
val ones: t:inttype -> l:secrecy_level -> v:int_t t l{int_v v = ones_v t}

inline_for_extraction
val eq_mask: #t:inttype{unsigned t} -> int_t t SEC -> int_t t SEC -> int_t t SEC

val eq_mask_lemma: #t:inttype{unsigned t} -> a:int_t t SEC -> b:int_t t SEC -> Lemma
  (requires True)
  (ensures  (v a = v b ==> v (eq_mask a b) == ones_v t) /\
            (v a <> v b ==> v (eq_mask a b) == 0))
  [SMTPat (eq_mask #t a b)]

val eq_mask_logand_lemma: #t:inttype{unsigned t /\ ~(U1? t)} -> a:int_t t SEC -> b:int_t t SEC -> c:int_t t SEC -> Lemma
  (ensures (if v a = v b then v (c `logand` (eq_mask a b)) == v c else v (c `logand` (eq_mask a b)) == 0))
  [SMTPat (c `logand` (eq_mask a b))]

inline_for_extraction
val neq_mask: #t:inttype{unsigned t} -> a:int_t t SEC -> b:int_t t SEC -> int_t t SEC

inline_for_extraction
val gte_mask: #t:inttype{~(S8? t) /\ ~(S16? t) /\ ~(S32? t) /\ ~(S64? t)} -> int_t t SEC -> b:int_t t SEC -> int_t t SEC

val gte_mask_lemma: #t:inttype{~(S8? t) /\ ~(S16? t) /\ ~(S32? t) /\ ~(S64? t)} -> a:int_t t SEC -> b:int_t t SEC -> Lemma
  (requires True)
  (ensures  (v a >= v b ==> v (gte_mask a b) == maxint t) /\
            (v a < v b ==> v (gte_mask a b) == 0))
  [SMTPat (gte_mask #t a b)]

val gte_mask_logand_lemma: #t:inttype{~(U1? t) /\ ~(S8? t) /\ ~(S16? t) /\ ~(S32? t) /\ ~(S64? t)} -> a:int_t t SEC -> b:int_t t SEC -> c:int_t t SEC -> Lemma
  (ensures (if v a >= v b then v (c `logand` (gte_mask a b)) == v c else v (c `logand` (gte_mask a b)) == 0))
  [SMTPat (c `logand` (gte_mask a b))]

inline_for_extraction
val lt_mask: #t:inttype{~(S8? t) /\ ~(S16? t) /\ ~(S32? t) /\ ~(S64? t)} -> int_t t SEC -> int_t t SEC -> int_t t SEC

inline_for_extraction
val gt_mask: #t:inttype{~(S8? t) /\ ~(S16? t) /\ ~(S32? t) /\ ~(S64? t)} -> int_t t SEC -> b:int_t t SEC -> int_t t SEC

inline_for_extraction
val lte_mask: #t:inttype{~(S8? t) /\ ~(S16? t) /\ ~(S32? t) /\ ~(S64? t)} -> int_t t SEC -> int_t t SEC -> int_t t SEC

inline_for_extraction
let mod_mask (#t:inttype) (#l:secrecy_level) (m:shiftval t) : int_t t l =
  (nat_to_int 1 `shift_left` m) `sub_mod` nat_to_int 1

val mod_mask_lemma: #t:inttype -> #l:secrecy_level -> a:int_t t l -> m:shiftval t ->
  Lemma
    (requires True)
    (ensures  int_v (a `logand` (mod_mask #t m)) == int_v a % pow2 (int_v m))
    [SMTPat (a `logand` (mod_mask #t m))]

///
/// Operators available for all machine integers
///

inline_for_extraction
let (+!) #t #l = add #t #l

inline_for_extraction
let (+.) #t #l = add_mod #t #l

inline_for_extraction
let ( *! ) #t #l = mul #t #l

inline_for_extraction
let ( *. ) #t #l = mul_mod #t #l

inline_for_extraction
let ( -! ) #t #l = sub #t #l

inline_for_extraction
let ( -. ) #t #l = sub_mod #t #l

inline_for_extraction
let ( >>. ) #t #l = shift_right #t #l

inline_for_extraction
let ( <<. ) #t #l = shift_left #t #l

inline_for_extraction
let ( >>>. ) #t #l = rotate_right #t #l

inline_for_extraction
let ( <<<. ) #t #l = rotate_left #t #l

inline_for_extraction
let ( ^. ) #t #l = logxor #t #l

inline_for_extraction
let ( |. ) #t #l = logor #t #l

inline_for_extraction
let ( &. ) #t #l = logand #t #l

inline_for_extraction
let ( ~. ) #t #l = lognot #t #l

///
/// Operations reserved to public integers
///

inline_for_extraction
val div: #t:inttype{t <> U128 /\ ~(S8? t) /\ ~(S16? t) /\ ~(S32? t) /\ ~(S64? t)}
  -> a:int_t t PUB
  -> b:int_t t PUB{int_v b > 0}
  -> int_t t PUB

inline_for_extraction
val div_lemma: #t:inttype{t <> U128 /\ ~(S8? t) /\ ~(S16? t) /\ ~(S32? t) /\ ~(S64? t)}
  -> a:int_t t PUB
  -> b:int_t t PUB{int_v b > 0}
  -> Lemma
  (ensures (int_v #t (div #t a b) == int_v a / int_v b))
  [SMTPat (int_v #t (div #t a b))]


inline_for_extraction
val mod: #t:inttype{t <> U128 /\ ~(S8? t) /\ ~(S16? t) /\ ~(S32? t) /\ ~(S64? t)} -> a:int_t t PUB -> b:int_t t PUB{int_v b > 0} -> int_t t PUB

inline_for_extraction
val mod_lemma: #t:inttype{t <> U128 /\ ~(S8? t) /\ ~(S16? t) /\ ~(S32? t) /\ ~(S64? t)}
  -> a:int_t t PUB
  -> b:int_t t PUB{int_v b > 0}
  -> Lemma
  (ensures (int_v #t (mod #t a b) == int_v a % int_v b))
  [SMTPat (int_v #t (mod #t a b))]


inline_for_extraction
val eq: #t:inttype -> int_t t PUB -> int_t t PUB -> bool

inline_for_extraction
val eq_lemma: #t:inttype
  -> a:int_t t PUB
  -> b:int_t t PUB
  -> Lemma
  (ensures (eq #t a b == (int_v a = int_v b)))
  [SMTPat (eq #t a b)]

inline_for_extraction
val ne: #t:inttype -> int_t t PUB -> int_t t PUB -> bool

inline_for_extraction
val ne_lemma: #t:inttype
  -> a:int_t t PUB
  -> b:int_t t PUB
  -> Lemma
  (ensures (ne #t a b == (int_v a <> int_v b)))
  [SMTPat (ne #t a b)]

inline_for_extraction
val lt: #t:inttype -> int_t t PUB -> int_t t PUB -> bool

inline_for_extraction
val lt_lemma: #t:inttype
  -> a:int_t t PUB
  -> b:int_t t PUB
  -> Lemma
  (ensures (lt #t a b == (int_v a < int_v b)))
  [SMTPat (lt #t a b)]

inline_for_extraction
val lte: #t:inttype -> int_t t PUB -> int_t t PUB -> bool

inline_for_extraction
val lte_lemma: #t:inttype
  -> a:int_t t PUB
  -> b:int_t t PUB
  -> Lemma
  (ensures (lte #t a b == (int_v a <= int_v b)))
  [SMTPat (lte #t a b)]


inline_for_extraction
val gt: #t:inttype -> int_t t PUB -> int_t t PUB -> bool

inline_for_extraction
val gt_lemma: #t:inttype
  -> a:int_t t PUB
  -> b:int_t t PUB
  -> Lemma
  (ensures (gt #t a b == (int_v a > int_v b)))
  [SMTPat (gt #t a b)]


inline_for_extraction
val gte: #t:inttype -> int_t t PUB -> int_t t PUB -> bool

inline_for_extraction
val gte_lemma: #t:inttype
  -> a:int_t t PUB
  -> b:int_t t PUB
  -> Lemma
  (ensures (gte #t a b == (int_v a >= int_v b)))
  [SMTPat (gte #t a b)]

inline_for_extraction
let (/.) #t = div #t

inline_for_extraction
let (%.) #t = mod #t

inline_for_extraction
let (=.) #t = eq #t

inline_for_extraction
let (<>.) #t = ne #t

inline_for_extraction
let (<.) #t = lt #t

inline_for_extraction
let (<=.) #t = lte #t

inline_for_extraction
let (>.) #t = gt #t

inline_for_extraction
let (>=.) #t = gte #t

inline_for_extraction
let p_t (t:inttype) =
  match t with
  | U32 -> UInt32.t
  | _ -> UInt64.t
