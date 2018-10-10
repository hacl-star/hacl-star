module Lib.IntTypes

open FStar.Integers
open FStar.ConstantTime.Integers
open FStar.Math.Lemmas

///
/// Definition of machine integer base types
///

type inttype =
 | U8 | U16 | U32 | U64 | U128 | SIZE | BYTE

///
/// Operations on the underlying machine integer base types
///

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
  | BYTE -> 8

let is_public (n:inttype) =
  match n with
  | U8
  | U16
  | U32
  | U64
  | U128 -> False
  | SIZE
  | BYTE -> True


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
  | BYTE -> 1

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
  modulus t - 1

unfold let secret (w:fixed_width{w <> W128}) = 
  ConstantTime.Integers.t (Secret hacl_label (Unsigned w))

unfold let public sw = ConstantTime.Integers.t (Public sw)

inline_for_extraction unfold
let uint_t (t:inttype) = 
  match t with
  | U8   -> secret W8
  | U16  -> secret W16
  | U32  -> secret W32
  | U64  -> secret W64
  | U128 -> public (Unsigned W128) // We don't have constant-time operations on UInt128
  | SIZE -> public (Unsigned W32)
  | BYTE -> public (Unsigned W8)

inline_for_extraction
val uint_v: #t:inttype -> u:uint_t t -> GTot (n:nat{n <= maxint t})

val uintv_extensionality:
  #t:inttype -> a:uint_t t -> b:uint_t t -> Lemma
  (requires uint_v a == uint_v b)
  (ensures  a == b)

///
/// Definition of machine integers
///

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
unfold type size_t = uint_t SIZE

inline_for_extraction
unfold type byte_t = uint_t BYTE


///
/// Casts between natural numbers and machine integers
///

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

unfold inline_for_extraction
let max_size_t = maxint SIZE

inline_for_extraction
unfold type size_nat = n:nat{n <= max_size_t}

inline_for_extraction
val size: n:size_nat -> u:size_t{uint_v #SIZE u == n}

inline_for_extraction
val size_v: s:size_t -> n:size_nat{uint_v #SIZE s == n}

inline_for_extraction
val byte: n:nat{n < 256} -> u:byte_t{uint_v #BYTE u == n}

inline_for_extraction
val byte_v: s:byte_t -> n:nat{uint_v #BYTE s == n}


inline_for_extraction
val size_to_uint32: s:size_t -> u:uint32{u == u32 (size_v s)}

inline_for_extraction
val byte_to_uint8: s:byte_t -> u:uint8{u == u8 (byte_v s)}

inline_for_extraction
val nat_to_uint: #t:inttype -> (n:nat{n <= maxint t}) -> u:uint_t t{uint_v u == n}

inline_for_extraction
val cast: #t:inttype{~ (is_public t)}
	  -> t':inttype{~ (is_public t)}
	  -> u1:uint_t t -> u2:uint_t t'{uint_v u2 == uint_v u1 % modulus t'}


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

///
/// Bitwise operators for all machine integers
///

inline_for_extraction
val add_mod: #t:inttype -> a:uint_t t -> b:uint_t t -> c:uint_t t {uint_v c == (uint_v a + uint_v b) % modulus t}

inline_for_extraction
val add: #t:inttype -> a:uint_t t -> b:uint_t t -> Pure (uint_t t)
  (requires (uint_v a + uint_v b < modulus t))
  (ensures (fun c -> uint_v c == uint_v a + uint_v b))

inline_for_extraction
val incr: #t:inttype -> a:uint_t t -> Pure (uint_t t)
  (requires (uint_v a < maxint t))
  (ensures (fun c -> uint_v c == uint_v a + 1))

inline_for_extraction
val mul_mod: #t:inttype -> a:uint_t t -> b:uint_t t -> Pure (uint_t t)
  (requires (t <> U128))
  (ensures (fun c -> uint_v c == (uint_v a `op_Multiply` uint_v b) % modulus t))


inline_for_extraction
val mul: #t:inttype{t <> U128} -> a:uint_t t -> b:uint_t t -> Pure (uint_t t)
  (requires (uint_v a `op_Multiply` uint_v b < modulus t))
  (ensures (fun c -> uint_v c == uint_v a `op_Multiply` uint_v b))

inline_for_extraction
val mul_wide: a:uint64 -> b:uint64 -> Pure uint128
  (requires True)
  (ensures fun c -> (uint_v #U128 c <: nat) == uint_v #U64 a `op_Multiply` uint_v #U64 b)

(* KB: I would prefer the post-condition to say:
       uint_v c = (pow2 (bits t) + uint_v a - uint_v b) % pow2 (bits t)
*)
inline_for_extraction
val sub_mod: #t:inttype -> a:uint_t t -> b:uint_t t -> c:uint_t t{uint_v c == (uint_v a - uint_v b) % modulus t}

inline_for_extraction
val sub: #t:inttype -> a:uint_t t -> b:uint_t t -> Pure (uint_t t)
  (requires (uint_v a >= uint_v b ))
  (ensures (fun c -> uint_v c == uint_v a - uint_v b))

inline_for_extraction
val decr: #t:inttype -> a:uint_t t -> Pure (uint_t t)
  (requires (uint_v a > 0))
  (ensures (fun c -> uint_v c == uint_v a - 1))

inline_for_extraction
val logxor: #t:inttype -> a:uint_t t -> b:uint_t t -> uint_t t

inline_for_extraction
val logand: #t:inttype -> a:uint_t t -> b:uint_t t -> uint_t t

inline_for_extraction
val logor: #t:inttype -> a:uint_t t -> b:uint_t t -> uint_t t

inline_for_extraction
val lognot: #t:inttype -> a:uint_t t -> uint_t t

inline_for_extraction
type shiftval (t:inttype) = u:size_t{uint_v #SIZE u < bits t}

inline_for_extraction
type rotval  (t:inttype) = u:size_t{uint_v #SIZE u > 0 /\ uint_v #SIZE u < bits t}

inline_for_extraction
val shift_right: #t:inttype -> a:uint_t t -> b:shiftval t ->
    c:uint_t t//{uint_v #t c ==  uint_v #t a / pow2 (uint_v #U32 b)}

inline_for_extraction
val shift_left: #t:inttype -> a:uint_t t -> b:shiftval t ->
    c:uint_t t//{uint_v #t c == (uint_v #t a `op_Multiply` pow2 (uint_v #U32 b)) % modulus t}

inline_for_extraction
val rotate_right: #t:inttype -> a:uint_t t -> b:rotval t -> uint_t t

inline_for_extraction
val rotate_left: #t:inttype -> a:uint_t t -> b:rotval t -> uint_t t

///
/// Masking operators for all machine integers
///

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
let mod_mask (#t:inttype) (m:shiftval t) : uint_t t =
  (nat_to_uint 1 `shift_left` m) `sub_mod` nat_to_uint 1

val mod_mask_lemma: #t:inttype -> a:uint_t t -> m:shiftval t -> Lemma
  (requires True)
  (ensures  uint_v (a `logand` (mod_mask #t m)) == uint_v a % pow2 (uint_v m))
  [SMTPat (uint_v (a `logand` (mod_mask #t m)))]

///
/// Operators available for all machine integers
///

inline_for_extraction
let (+!) #t a = add #t a

inline_for_extraction
let (+.) #t a = add_mod #t a

inline_for_extraction
let ( *! ) #t a = mul #t a

inline_for_extraction
let ( *. ) #t a = mul_mod #t a

inline_for_extraction
let ( -! ) #t a = sub #t a

inline_for_extraction
let ( -. ) #t a = sub_mod #t a

inline_for_extraction
let ( >>. ) #t a = shift_right #t a

inline_for_extraction
let ( <<. ) #t a = shift_left #t a

inline_for_extraction
let ( >>>. ) #t a = rotate_right #t a

inline_for_extraction
let ( <<<. ) #t a b = rotate_left #t a b

inline_for_extraction
let ( ^. ) #t a b = logxor #t a b

inline_for_extraction
let ( |. ) #t a b = logor #t a b

inline_for_extraction
let ( &. ) #t a = logand #t a

inline_for_extraction
let ( ~. ) #t a = lognot #t a

///
/// Operations reserved to public integers
///


inline_for_extraction
val div: #t:inttype{is_public t} -> a:uint_t t -> b:uint_t t -> Pure (uint_t t)
  (requires (uint_v #t b > 0))
  (ensures (fun c -> uint_v c == uint_v a / uint_v b))

inline_for_extraction
val mod: #t:inttype{is_public t} -> a:uint_t t -> b:uint_t t -> Pure (uint_t t)
  (requires (uint_v #t b > 0))
  (ensures (fun c -> uint_v c == uint_v a % uint_v b))

inline_for_extraction
val eq: #t:inttype{is_public t} -> a:uint_t t -> b:uint_t t -> Pure bool
  (requires (True))
  (ensures (fun c -> c == (uint_v a = uint_v b)))

inline_for_extraction
val ne: #t:inttype{is_public t} -> a:uint_t t -> b:uint_t t -> Pure bool
  (requires (True))
  (ensures (fun c -> c == (uint_v a <> uint_v b)))

inline_for_extraction
val lt: #t:inttype{is_public t} -> a:uint_t t -> b:uint_t t -> Pure bool
  (requires (True))
  (ensures (fun c -> c == (uint_v a < uint_v b)))

inline_for_extraction
val le: #t:inttype{is_public t} -> a:uint_t t -> b:uint_t t -> Pure bool
  (requires (True))
  (ensures (fun c -> c == (uint_v a <= uint_v b)))

inline_for_extraction
val gt: #t:inttype{is_public t} -> a:uint_t t -> b:uint_t t -> Pure bool
  (requires (True))
  (ensures (fun c -> c == (uint_v a > uint_v b)))

inline_for_extraction
val ge: #t:inttype{is_public t} -> a:uint_t t -> b:uint_t t -> Pure bool
  (requires (True))
  (ensures (fun c -> c == (uint_v a >= uint_v b)))

inline_for_extraction
let (/.) #t = div #t

inline_for_extraction
let (%.) #t = mod #t

inline_for_extraction
let (=.) #t = eq #t

inline_for_extraction
let (<.) #t = lt #t
inline_for_extraction
let (<=.) #t = le #t

inline_for_extraction
let (>.) #t = gt #t

inline_for_extraction
let (>=.) #t = ge #t
