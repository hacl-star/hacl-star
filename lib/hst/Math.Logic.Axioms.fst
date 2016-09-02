module Math.Logic.Axioms

module U8 = FStar.UInt8
module S8 = Hacl.UInt8
module U16 = FStar.UInt16
module S16 = Hacl.UInt16
module U32 = FStar.UInt32
module S32 = Hacl.UInt32
module U64 = FStar.UInt64
module S64 = Hacl.UInt64


(* Define Base types *)
let u8 = U8.t
let s8 = S8.t
let u16 = U16.t
let s16 = S16.t
let u32 = U32.t
let s32 = S32.t
let u64 = U64.t
let s64 = S64.t


(* Define extreme values *)
assume val u8_zero_f: unit -> Tot (z:u8{U8.v z = 0})
assume val u8_one_f: unit -> Tot (o:u8{U8.v o = 1})
assume val u8_ones_f: unit -> Tot (o:u8{U8.v o = pow2 8 - 1})

assume val s8_zero_f: unit -> Tot (z:s8{S8.v z = 0})
assume val s8_one_f: unit -> Tot (o:s8{S8.v o = 1})
assume val s8_ones_f: unit -> Tot (o:s8{S8.v o = pow2 8 - 1})

assume val u16_zero_f: unit -> Tot (z:u16{U16.v z = 0})
assume val u16_one_f: unit -> Tot (o:u16{U16.v o = 1})
assume val u16_ones_f: unit -> Tot (o:u16{U16.v o = pow2 16 - 1})

assume val s16_zero_f: unit -> Tot (z:s16{S16.v z = 0})
assume val s16_one_f: unit -> Tot (o:s16{S16.v o = 1})
assume val s16_ones_f: unit -> Tot (o:s16{S16.v o = pow2 16 - 1})

assume val u32_zero_f: unit -> Tot (z:u32{U32.v z = 0})
assume val u32_one_f: unit -> Tot (o:u32{U32.v o = 1})
assume val u32_ones_f: unit -> Tot (o:u32{U32.v o = pow2 32 - 1})

assume val s32_zero_f: unit -> Tot (z:s32{S32.v z = 0})
assume val s32_one_f: unit -> Tot (o:s32{S32.v o = 1})
assume val s32_ones_f: unit -> Tot (o:s32{S32.v o = pow2 32 - 1})

assume val u64_zero_f: unit -> Tot (z:u64{U64.v z = 0})
assume val u64_one_f: unit -> Tot (o:u64{U64.v o = 1})
assume val u64_ones_f: unit -> Tot (o:u64{U64.v o = pow2 64 - 1})

assume val s64_zero_f: unit -> Tot (z:s64{S64.v z = 0})
assume val s64_one_f: unit -> Tot (o:s64{S64.v o = 1})
assume val s64_ones_f: unit -> Tot (o:s64{S64.v o = pow2 64 - 1})

let u8_zero = u8_zero_f ()
let u8_one = u8_one_f ()
let u8_ones = u8_ones_f ()

let s8_zero = s8_zero_f ()
let s8_one = s8_one_f ()
let s8_ones = s8_ones_f ()

let u16_zero = u16_zero_f ()
let u16_one = u16_one_f ()
let u16_ones = u16_ones_f ()

let s16_zero = s16_zero_f ()
let s16_one = s16_one_f ()
let s16_ones = s16_ones_f ()

let u32_zero = u32_zero_f ()
let u32_one = u32_one_f ()
let u32_ones = u32_ones_f ()

let s32_zero = s32_zero_f ()
let s32_one = s32_one_f ()
let s32_ones = s32_ones_f ()

let u64_zero = u64_zero_f ()
let u64_one = u64_one_f ()
let u64_ones = u64_ones_f ()

let s64_zero = s64_zero_f ()
let s64_one = s64_one_f ()
let s64_ones = s64_ones_f ()



(*******************************************************************************)


(* Logical AND operator: commutativity *)
assume val axiom_u8_logand_1: a:u8 -> b:u8
  -> Lemma (requires True) (ensures (U8.v (U8.logand a b) = U8.v (U8.logand b a)))
    [SMTPat (U8.v (U8.logand a b))]

(* Logical AND operator: result of operation with zero *)
assume val axiom_u8_logand_2: a:u8
  -> Lemma (requires True) (ensures (U8.v (U8.logand a u8_zero) = 0))
    [SMTPat (U8.v (U8.logand a u8_zero))]

(* Logical AND operator: result of operation with ones *)
assume val axiom_u8_logand_3: a:u8
  -> Lemma (requires True) (ensures (U8.v (U8.logand a u8_ones) = U8.v a))
    [SMTPat (U8.v (U8.logand a u8_ones))]

(* Logical AND operator: modular reduction *)
assume val axiom_u8_logand_4: a:u8 -> m:nat -> b:u8
  -> Lemma (requires (U8.v b = pow2 m - 1)) (ensures (U8.v (U8.logand a b) = U8.v a % pow2 m))
    [SMTPat (U8.v (U8.logand a b))]


(* Logical XOR operator: commutativity *)
assume val axiom_u8_logxor_1: a:u8 -> b:u8
  -> Lemma (requires True) (ensures (U8.v (U8.logxor a b) = U8.v (U8.logxor b a)))
    [SMTPat (U8.v (U8.logxor a b))]

(* Logical XOR operator: result of operation with zero *)
assume val axiom_u8_logxor_2: a:u8
  -> Lemma (requires True) (ensures (U8.v (U8.logxor a u8_zero) = U8.v a))
    [SMTPat (U8.v (U8.logxor a u8_zero))]

(* Logical XOR operator: result of operation with ones *)
assume val axiom_u8_logxor_3: a:u8
  -> Lemma (requires True) (ensures (U8.v (U8.logxor a u8_ones) = U8.v (U8.lognot a)))
    [SMTPat (U8.v (U8.logxor a u8_ones))]

(* Logical XOR operator: result of operation with itself *)
assume val axiom_u8_logxor_4: a:u8
  -> Lemma (requires True) (ensures (U8.v (U8.logxor a a) = 0))
    [SMTPat (U8.v (U8.logxor a a))]


(* Logical OR operator: commutativity *)
assume val axiom_u8_logor_1: a:u8 -> b:u8
  -> Lemma (requires True) (ensures (U8.v (U8.logor a b) = U8.v (U8.logor b a)))
    [SMTPat (U8.v (U8.logor a b))]

(* Logical OR operator: result of operation with zero *)
assume val axiom_u8_logor_2: a:u8
  -> Lemma (requires True) (ensures (U8.v (U8.logor a u8_zero) = U8.v a))
    [SMTPat (U8.v (U8.logor a u8_zero))]

(* Logical OR operator: result of operation with ones *)
assume val axiom_u8_logor_3: a:u8
  -> Lemma (requires True) (ensures (U8.v (U8.logor a u8_ones) = U8.v u8_ones))
    [SMTPat (U8.v (U8.logor a u8_ones))]


(* Logical NOT operator: double negation *)
assume val axiom_u8_lognot_1: a:u8
  -> Lemma (requires True) (ensures (U8.v (U8.lognot (U8.lognot a)) = U8.v a))
    [SMTPat (U8.v (U8.lognot (U8.lognot a)))]

(* Logical NOT operator: negation of zeros *)
assume val axiom_u8_lognot_2: unit
  -> Lemma (requires True) (ensures (U8.v (U8.lognot u8_zero) = U8.v u8_ones))
    [SMTPat (U8.v (U8.lognot u8_zero))]

(* Logical NOT operator: negation of ones *)
assume val axiom_u8_lognot_3: unit
  -> Lemma (requires True) (ensures (U8.v (U8.lognot u8_ones) = U8.v u8_zero))
    [SMTPat (U8.v (U8.lognot u8_ones))]


(*******************************************************************************)


(* Logical AND operator: commutativity *)
assume val axiom_s8_logand_1: a:s8 -> b:s8
  -> Lemma (requires True) (ensures (S8.v (S8.logand a b) = S8.v (S8.logand b a)))
    [SMTPat (S8.v (S8.logand a b))]

(* Logical AND operator: result of operation with zero *)
assume val axiom_s8_logand_2: a:s8
  -> Lemma (requires True) (ensures (S8.v (S8.logand a s8_zero) = 0))
    [SMTPat (S8.v (S8.logand a s8_zero))]

(* Logical AND operator: result of operation with ones *)
assume val axiom_s8_logand_3: a:s8
  -> Lemma (requires True) (ensures (S8.v (S8.logand a s8_ones) = S8.v a))
    [SMTPat (S8.v (S8.logand a s8_ones))]

(* Logical AND operator: modular reduction *)
assume val axiom_s8_logand_4: a:s8 -> m:nat -> b:s8
  -> Lemma (requires (S8.v b = pow2 m - 1)) (ensures (S8.v (S8.logand a b) = S8.v a % pow2 m))
    [SMTPat (S8.v (S8.logand a b))]


(* Logical XOR operator: commutativity *)
assume val axiom_s8_logxor_1: a:s8 -> b:s8
  -> Lemma (requires True) (ensures (S8.v (S8.logxor a b) = S8.v (S8.logxor b a)))
    [SMTPat (S8.v (S8.logxor a b))]

(* Logical XOR operator: result of operation with zero *)
assume val axiom_s8_logxor_2: a:s8
  -> Lemma (requires True) (ensures (S8.v (S8.logxor a s8_zero) = S8.v a))
    [SMTPat (S8.v (S8.logxor a s8_zero))]

(* Logical XOR operator: result of operation with ones *)
assume val axiom_s8_logxor_3: a:s8
  -> Lemma (requires True) (ensures (S8.v (S8.logxor a s8_ones) = S8.v (S8.lognot a)))
    [SMTPat (S8.v (S8.logxor a s8_ones))]

(* Logical XOR operator: result of operation with itself *)
assume val axiom_s8_logxor_4: a:s8
  -> Lemma (requires True) (ensures (S8.v (S8.logxor a a) = 0))
    [SMTPat (S8.v (S8.logxor a a))]


(* Logical OR operator: commutativity *)
assume val axiom_s8_logor_1: a:s8 -> b:s8
  -> Lemma (requires True) (ensures (S8.v (S8.logor a b) = S8.v (S8.logor b a)))
    [SMTPat (S8.v (S8.logor a b))]

(* Logical OR operator: result of operation with zero *)
assume val axiom_s8_logor_2: a:s8
  -> Lemma (requires True) (ensures (S8.v (S8.logor a s8_zero) = S8.v a))
    [SMTPat (S8.v (S8.logor a s8_zero))]

(* Logical OR operator: result of operation with ones *)
assume val axiom_s8_logor_3: a:s8
  -> Lemma (requires True) (ensures (S8.v (S8.logor a s8_ones) = S8.v s8_ones))
    [SMTPat (S8.v (S8.logor a s8_ones))]


(* Logical NOT operator: double negation *)
assume val axiom_s8_lognot_1: a:s8
  -> Lemma (requires True) (ensures (S8.v (S8.lognot (S8.lognot a)) = S8.v a))
    [SMTPat (S8.v (S8.lognot (S8.lognot a)))]

(* Logical NOT operator: negation of zeros *)
assume val axiom_s8_lognot_2: unit
  -> Lemma (requires True) (ensures (S8.v (S8.lognot s8_zero) = S8.v s8_ones))
    [SMTPat (S8.v (S8.lognot s8_zero))]

(* Logical NOT operator: negation of ones *)
assume val axiom_s8_lognot_3: unit
  -> Lemma (requires True) (ensures (S8.v (S8.lognot s8_ones) = S8.v s8_zero))
    [SMTPat (S8.v (S8.lognot s8_ones))]


(*******************************************************************************)


(* Logical AND operator: commutativity *)
assume val axiom_u16_logand_1: a:u16 -> b:u16
  -> Lemma (requires True) (ensures (U16.v (U16.logand a b) = U16.v (U16.logand b a)))
    [SMTPat (U16.v (U16.logand a b))]

(* Logical AND operator: result of operation with zero *)
assume val axiom_u16_logand_2: a:u16
  -> Lemma (requires True) (ensures (U16.v (U16.logand a u16_zero) = 0))
    [SMTPat (U16.v (U16.logand a u16_zero))]

(* Logical AND operator: result of operation with ones *)
assume val axiom_u16_logand_3: a:u16
  -> Lemma (requires True) (ensures (U16.v (U16.logand a u16_ones) = U16.v a))
    [SMTPat (U16.v (U16.logand a u16_ones))]

(* Logical AND operator: modular reduction *)
assume val axiom_u16_logand_4: a:u16 -> m:nat -> b:u16
  -> Lemma (requires (U16.v b = pow2 m - 1)) (ensures (U16.v (U16.logand a b) = U16.v a % pow2 m))
    [SMTPat (U16.v (U16.logand a b))]


(* Logical XOR operator: commutativity *)
assume val axiom_u16_logxor_1: a:u16 -> b:u16
  -> Lemma (requires True) (ensures (U16.v (U16.logxor a b) = U16.v (U16.logxor b a)))
    [SMTPat (U16.v (U16.logxor a b))]

(* Logical XOR operator: result of operation with zero *)
assume val axiom_u16_logxor_2: a:u16
  -> Lemma (requires True) (ensures (U16.v (U16.logxor a u16_zero) = U16.v a))
    [SMTPat (U16.v (U16.logxor a u16_zero))]

(* Logical XOR operator: result of operation with ones *)
assume val axiom_u16_logxor_3: a:u16
  -> Lemma (requires True) (ensures (U16.v (U16.logxor a u16_ones) = U16.v (U16.lognot a)))
    [SMTPat (U16.v (U16.logxor a u16_ones))]

(* Logical XOR operator: result of operation with itself *)
assume val axiom_u16_logxor_4: a:u16
  -> Lemma (requires True) (ensures (U16.v (U16.logxor a a) = 0))
    [SMTPat (U16.v (U16.logxor a a))]


(* Logical OR operator: commutativity *)
assume val axiom_u16_logor_1: a:u16 -> b:u16
  -> Lemma (requires True) (ensures (U16.v (U16.logor a b) = U16.v (U16.logor b a)))
    [SMTPat (U16.v (U16.logor a b))]

(* Logical OR operator: result of operation with zero *)
assume val axiom_u16_logor_2: a:u16
  -> Lemma (requires True) (ensures (U16.v (U16.logor a u16_zero) = U16.v a))
    [SMTPat (U16.v (U16.logor a u16_zero))]

(* Logical OR operator: result of operation with ones *)
assume val axiom_u16_logor_3: a:u16
  -> Lemma (requires True) (ensures (U16.v (U16.logor a u16_ones) = U16.v u16_ones))
    [SMTPat (U16.v (U16.logor a u16_ones))]


(* Logical NOT operator: double negation *)
assume val axiom_u16_lognot_1: a:u16
  -> Lemma (requires True) (ensures (U16.v (U16.lognot (U16.lognot a)) = U16.v a))
    [SMTPat (U16.v (U16.lognot (U16.lognot a)))]

(* Logical NOT operator: negation of zeros *)
assume val axiom_u16_lognot_2: unit
  -> Lemma (requires True) (ensures (U16.v (U16.lognot u16_zero) = U16.v u16_ones))
    [SMTPat (U16.v (U16.lognot u16_zero))]

(* Logical NOT operator: negation of ones *)
assume val axiom_u16_lognot_3: unit
  -> Lemma (requires True) (ensures (U16.v (U16.lognot u16_ones) = U16.v u16_zero))
    [SMTPat (U16.v (U16.lognot u16_ones))]


(*******************************************************************************)


(* Logical AND operator: commutativity *)
assume val axiom_s16_logand_1: a:s16 -> b:s16
  -> Lemma (requires True) (ensures (S16.v (S16.logand a b) = S16.v (S16.logand b a)))
    [SMTPat (S16.v (S16.logand a b))]

(* Logical AND operator: result of operation with zero *)
assume val axiom_s16_logand_2: a:s16
  -> Lemma (requires True) (ensures (S16.v (S16.logand a s16_zero) = 0))
    [SMTPat (S16.v (S16.logand a s16_zero))]

(* Logical AND operator: result of operation with ones *)
assume val axiom_s16_logand_3: a:s16
  -> Lemma (requires True) (ensures (S16.v (S16.logand a s16_ones) = S16.v a))
    [SMTPat (S16.v (S16.logand a s16_ones))]

(* Logical AND operator: modular reduction *)
assume val axiom_s16_logand_4: a:s16 -> m:nat -> b:s16
  -> Lemma (requires (S16.v b = pow2 m - 1)) (ensures (S16.v (S16.logand a b) = S16.v a % pow2 m))
    [SMTPat (S16.v (S16.logand a b))]


(* Logical XOR operator: commutativity *)
assume val axiom_s16_logxor_1: a:s16 -> b:s16
  -> Lemma (requires True) (ensures (S16.v (S16.logxor a b) = S16.v (S16.logxor b a)))
    [SMTPat (S16.v (S16.logxor a b))]

(* Logical XOR operator: result of operation with zero *)
assume val axiom_s16_logxor_2: a:s16
  -> Lemma (requires True) (ensures (S16.v (S16.logxor a s16_zero) = S16.v a))
    [SMTPat (S16.v (S16.logxor a s16_zero))]

(* Logical XOR operator: result of operation with ones *)
assume val axiom_s16_logxor_3: a:s16
  -> Lemma (requires True) (ensures (S16.v (S16.logxor a s16_ones) = S16.v (S16.lognot a)))
    [SMTPat (S16.v (S16.logxor a s16_ones))]

(* Logical XOR operator: result of operation with itself *)
assume val axiom_s16_logxor_4: a:s16
  -> Lemma (requires True) (ensures (S16.v (S16.logxor a a) = 0))
    [SMTPat (S16.v (S16.logxor a a))]


(* Logical OR operator: commutativity *)
assume val axiom_s16_logor_1: a:s16 -> b:s16
  -> Lemma (requires True) (ensures (S16.v (S16.logor a b) = S16.v (S16.logor b a)))
    [SMTPat (S16.v (S16.logor a b))]

(* Logical OR operator: result of operation with zero *)
assume val axiom_s16_logor_2: a:s16
  -> Lemma (requires True) (ensures (S16.v (S16.logor a s16_zero) = S16.v a))
    [SMTPat (S16.v (S16.logor a s16_zero))]

(* Logical OR operator: result of operation with ones *)
assume val axiom_s16_logor_3: a:s16
  -> Lemma (requires True) (ensures (S16.v (S16.logor a s16_ones) = S16.v s16_ones))
    [SMTPat (S16.v (S16.logor a s16_ones))]


(* Logical NOT operator: double negation *)
assume val axiom_s16_lognot_1: a:s16
  -> Lemma (requires True) (ensures (S16.v (S16.lognot (S16.lognot a)) = S16.v a))
    [SMTPat (S16.v (S16.lognot (S16.lognot a)))]

(* Logical NOT operator: negation of zeros *)
assume val axiom_s16_lognot_2: unit
  -> Lemma (requires True) (ensures (S16.v (S16.lognot s16_zero) = S16.v s16_ones))
    [SMTPat (S16.v (S16.lognot s16_zero))]

(* Logical NOT operator: negation of ones *)
assume val axiom_s16_lognot_3: unit
  -> Lemma (requires True) (ensures (S16.v (S16.lognot s16_ones) = S16.v s16_zero))
    [SMTPat (S16.v (S16.lognot s16_ones))]


(*******************************************************************************)


(* Logical AND operator: commutativity *)
assume val axiom_u32_logand_1: a:u32 -> b:u32
  -> Lemma (requires True) (ensures (U32.v (U32.logand a b) = U32.v (U32.logand b a)))
    [SMTPat (U32.v (U32.logand a b))]

(* Logical AND operator: result of operation with zero *)
assume val axiom_u32_logand_2: a:u32
  -> Lemma (requires True) (ensures (U32.v (U32.logand a u32_zero) = 0))
    [SMTPat (U32.v (U32.logand a u32_zero))]

(* Logical AND operator: result of operation with ones *)
assume val axiom_u32_logand_3: a:u32
  -> Lemma (requires True) (ensures (U32.v (U32.logand a u32_ones) = U32.v a))
    [SMTPat (U32.v (U32.logand a u32_ones))]

(* Logical AND operator: modular reduction *)
assume val axiom_u32_logand_4: a:u32 -> m:nat -> b:u32
  -> Lemma (requires (U32.v b = pow2 m - 1)) (ensures (U32.v (U32.logand a b) = U32.v a % pow2 m))
    [SMTPat (U32.v (U32.logand a b))]


(* Logical XOR operator: commutativity *)
assume val axiom_u32_logxor_1: a:u32 -> b:u32
  -> Lemma (requires True) (ensures (U32.v (U32.logxor a b) = U32.v (U32.logxor b a)))
    [SMTPat (U32.v (U32.logxor a b))]

(* Logical XOR operator: result of operation with zero *)
assume val axiom_u32_logxor_2: a:u32
  -> Lemma (requires True) (ensures (U32.v (U32.logxor a u32_zero) = U32.v a))
    [SMTPat (U32.v (U32.logxor a u32_zero))]

(* Logical XOR operator: result of operation with ones *)
assume val axiom_u32_logxor_3: a:u32
  -> Lemma (requires True) (ensures (U32.v (U32.logxor a u32_ones) = U32.v (U32.lognot a)))
    [SMTPat (U32.v (U32.logxor a u32_ones))]

(* Logical XOR operator: result of operation with itself *)
assume val axiom_u32_logxor_4: a:u32
  -> Lemma (requires True) (ensures (U32.v (U32.logxor a a) = 0))
    [SMTPat (U32.v (U32.logxor a a))]


(* Logical OR operator: commutativity *)
assume val axiom_u32_logor_1: a:u32 -> b:u32
  -> Lemma (requires True) (ensures (U32.v (U32.logor a b) = U32.v (U32.logor b a)))
    [SMTPat (U32.v (U32.logor a b))]

(* Logical OR operator: result of operation with zero *)
assume val axiom_u32_logor_2: a:u32
  -> Lemma (requires True) (ensures (U32.v (U32.logor a u32_zero) = U32.v a))
    [SMTPat (U32.v (U32.logor a u32_zero))]

(* Logical OR operator: result of operation with ones *)
assume val axiom_u32_logor_3: a:u32
  -> Lemma (requires True) (ensures (U32.v (U32.logor a u32_ones) = U32.v u32_ones))
    [SMTPat (U32.v (U32.logor a u32_ones))]


(* Logical NOT operator: double negation *)
assume val axiom_u32_lognot_1: a:u32
  -> Lemma (requires True) (ensures (U32.v (U32.lognot (U32.lognot a)) = U32.v a))
    [SMTPat (U32.v (U32.lognot (U32.lognot a)))]

(* Logical NOT operator: negation of zeros *)
assume val axiom_u32_lognot_2: unit
  -> Lemma (requires True) (ensures (U32.v (U32.lognot u32_zero) = U32.v u32_ones))
    [SMTPat (U32.v (U32.lognot u32_zero))]

(* Logical NOT operator: negation of ones *)
assume val axiom_u32_lognot_3: unit
  -> Lemma (requires True) (ensures (U32.v (U32.lognot u32_ones) = U32.v u32_zero))
    [SMTPat (U32.v (U32.lognot u32_ones))]


(*******************************************************************************)


(* Logical AND operator: commutativity *)
assume val axiom_s32_logand_1: a:s32 -> b:s32
  -> Lemma (requires True) (ensures (S32.v (S32.logand a b) = S32.v (S32.logand b a)))
    [SMTPat (S32.v (S32.logand a b))]

(* Logical AND operator: result of operation with zero *)
assume val axiom_s32_logand_2: a:s32
  -> Lemma (requires True) (ensures (S32.v (S32.logand a s32_zero) = 0))
    [SMTPat (S32.v (S32.logand a s32_zero))]

(* Logical AND operator: result of operation with ones *)
assume val axiom_s32_logand_3: a:s32
  -> Lemma (requires True) (ensures (S32.v (S32.logand a s32_ones) = S32.v a))
    [SMTPat (S32.v (S32.logand a s32_ones))]

(* Logical AND operator: modular reduction *)
assume val axiom_s32_logand_4: a:s32 -> m:nat -> b:s32
  -> Lemma (requires (S32.v b = pow2 m - 1)) (ensures (S32.v (S32.logand a b) = S32.v a % pow2 m))
    [SMTPat (S32.v (S32.logand a b))]


(* Logical XOR operator: commutativity *)
assume val axiom_s32_logxor_1: a:s32 -> b:s32
  -> Lemma (requires True) (ensures (S32.v (S32.logxor a b) = S32.v (S32.logxor b a)))
    [SMTPat (S32.v (S32.logxor a b))]

(* Logical XOR operator: result of operation with zero *)
assume val axiom_s32_logxor_2: a:s32
  -> Lemma (requires True) (ensures (S32.v (S32.logxor a s32_zero) = S32.v a))
    [SMTPat (S32.v (S32.logxor a s32_zero))]

(* Logical XOR operator: result of operation with ones *)
assume val axiom_s32_logxor_3: a:s32
  -> Lemma (requires True) (ensures (S32.v (S32.logxor a s32_ones) = S32.v (S32.lognot a)))
    [SMTPat (S32.v (S32.logxor a s32_ones))]

(* Logical XOR operator: result of operation with itself *)
assume val axiom_s32_logxor_4: a:s32
  -> Lemma (requires True) (ensures (S32.v (S32.logxor a a) = 0))
    [SMTPat (S32.v (S32.logxor a a))]


(* Logical OR operator: commutativity *)
assume val axiom_s32_logor_1: a:s32 -> b:s32
  -> Lemma (requires True) (ensures (S32.v (S32.logor a b) = S32.v (S32.logor b a)))
    [SMTPat (S32.v (S32.logor a b))]

(* Logical OR operator: result of operation with zero *)
assume val axiom_s32_logor_2: a:s32
  -> Lemma (requires True) (ensures (S32.v (S32.logor a s32_zero) = S32.v a))
    [SMTPat (S32.v (S32.logor a s32_zero))]

(* Logical OR operator: result of operation with ones *)
assume val axiom_s32_logor_3: a:s32
  -> Lemma (requires True) (ensures (S32.v (S32.logor a s32_ones) = S32.v s32_ones))
    [SMTPat (S32.v (S32.logor a s32_ones))]


(* Logical NOT operator: double negation *)
assume val axiom_s32_lognot_1: a:s32
  -> Lemma (requires True) (ensures (S32.v (S32.lognot (S32.lognot a)) = S32.v a))
    [SMTPat (S32.v (S32.lognot (S32.lognot a)))]

(* Logical NOT operator: negation of zeros *)
assume val axiom_s32_lognot_2: unit
  -> Lemma (requires True) (ensures (S32.v (S32.lognot s32_zero) = S32.v s32_ones))
    [SMTPat (S32.v (S32.lognot s32_zero))]

(* Logical NOT operator: negation of ones *)
assume val axiom_s32_lognot_3: unit
  -> Lemma (requires True) (ensures (S32.v (S32.lognot s32_ones) = S32.v s32_zero))
    [SMTPat (S32.v (S32.lognot s32_ones))]


(*******************************************************************************)


(* Logical AND operator: commutativity *)
assume val axiom_u64_logand_1: a:u64 -> b:u64
  -> Lemma (requires True) (ensures (U64.v (U64.logand a b) = U64.v (U64.logand b a)))
    [SMTPat (U64.v (U64.logand a b))]

(* Logical AND operator: result of operation with zero *)
assume val axiom_u64_logand_2: a:u64
  -> Lemma (requires True) (ensures (U64.v (U64.logand a u64_zero) = 0))
    [SMTPat (U64.v (U64.logand a u64_zero))]

(* Logical AND operator: result of operation with ones *)
assume val axiom_u64_logand_3: a:u64
  -> Lemma (requires True) (ensures (U64.v (U64.logand a u64_ones) = U64.v a))
    [SMTPat (U64.v (U64.logand a u64_ones))]

(* Logical AND operator: modular reduction *)
assume val axiom_u64_logand_4: a:u64 -> m:nat -> b:u64
  -> Lemma (requires (U64.v b = pow2 m - 1)) (ensures (U64.v (U64.logand a b) = U64.v a % pow2 m))
    [SMTPat (U64.v (U64.logand a b))]


(* Logical XOR operator: commutativity *)
assume val axiom_u64_logxor_1: a:u64 -> b:u64
  -> Lemma (requires True) (ensures (U64.v (U64.logxor a b) = U64.v (U64.logxor b a)))
    [SMTPat (U64.v (U64.logxor a b))]

(* Logical XOR operator: result of operation with zero *)
assume val axiom_u64_logxor_2: a:u64
  -> Lemma (requires True) (ensures (U64.v (U64.logxor a u64_zero) = U64.v a))
    [SMTPat (U64.v (U64.logxor a u64_zero))]

(* Logical XOR operator: result of operation with ones *)
assume val axiom_u64_logxor_3: a:u64
  -> Lemma (requires True) (ensures (U64.v (U64.logxor a u64_ones) = U64.v (U64.lognot a)))
    [SMTPat (U64.v (U64.logxor a u64_ones))]

(* Logical XOR operator: result of operation with itself *)
assume val axiom_u64_logxor_4: a:u64
  -> Lemma (requires True) (ensures (U64.v (U64.logxor a a) = 0))
    [SMTPat (U64.v (U64.logxor a a))]


(* Logical OR operator: commutativity *)
assume val axiom_u64_logor_1: a:u64 -> b:u64
  -> Lemma (requires True) (ensures (U64.v (U64.logor a b) = U64.v (U64.logor b a)))
    [SMTPat (U64.v (U64.logor a b))]

(* Logical OR operator: result of operation with zero *)
assume val axiom_u64_logor_2: a:u64
  -> Lemma (requires True) (ensures (U64.v (U64.logor a u64_zero) = U64.v a))
    [SMTPat (U64.v (U64.logor a u64_zero))]

(* Logical OR operator: result of operation with ones *)
assume val axiom_u64_logor_3: a:u64
  -> Lemma (requires True) (ensures (U64.v (U64.logor a u64_ones) = U64.v u64_ones))
    [SMTPat (U64.v (U64.logor a u64_ones))]


(* Logical NOT operator: double negation *)
assume val axiom_u64_lognot_1: a:u64
  -> Lemma (requires True) (ensures (U64.v (U64.lognot (U64.lognot a)) = U64.v a))
    [SMTPat (U64.v (U64.lognot (U64.lognot a)))]

(* Logical NOT operator: negation of zeros *)
assume val axiom_u64_lognot_2: unit
  -> Lemma (requires True) (ensures (U64.v (U64.lognot u64_zero) = U64.v u64_ones))
    [SMTPat (U64.v (U64.lognot u64_zero))]

(* Logical NOT operator: negation of ones *)
assume val axiom_u64_lognot_3: unit
  -> Lemma (requires True) (ensures (U64.v (U64.lognot u64_ones) = U64.v u64_zero))
    [SMTPat (U64.v (U64.lognot u64_ones))]


(*******************************************************************************)


(* Logical AND operator: commutativity *)
assume val axiom_s64_logand_1: a:s64 -> b:s64
  -> Lemma (requires True) (ensures (S64.v (S64.logand a b) = S64.v (S64.logand b a)))
    [SMTPat (S64.v (S64.logand a b))]

(* Logical AND operator: result of operation with zero *)
assume val axiom_s64_logand_2: a:s64
  -> Lemma (requires True) (ensures (S64.v (S64.logand a s64_zero) = 0))
    [SMTPat (S64.v (S64.logand a s64_zero))]

(* Logical AND operator: result of operation with ones *)
assume val axiom_s64_logand_3: a:s64
  -> Lemma (requires True) (ensures (S64.v (S64.logand a s64_ones) = S64.v a))
    [SMTPat (S64.v (S64.logand a s64_ones))]

(* Logical AND operator: modular reduction *)
assume val axiom_s64_logand_4: a:s64 -> m:nat -> b:s64
  -> Lemma (requires (S64.v b = pow2 m - 1)) (ensures (S64.v (S64.logand a b) = S64.v a % pow2 m))
    [SMTPat (S64.v (S64.logand a b))]


(* Logical XOR operator: commutativity *)
assume val axiom_s64_logxor_1: a:s64 -> b:s64
  -> Lemma (requires True) (ensures (S64.v (S64.logxor a b) = S64.v (S64.logxor b a)))
    [SMTPat (S64.v (S64.logxor a b))]

(* Logical XOR operator: result of operation with zero *)
assume val axiom_s64_logxor_2: a:s64
  -> Lemma (requires True) (ensures (S64.v (S64.logxor a s64_zero) = S64.v a))
    [SMTPat (S64.v (S64.logxor a s64_zero))]

(* Logical XOR operator: result of operation with ones *)
assume val axiom_s64_logxor_3: a:s64
  -> Lemma (requires True) (ensures (S64.v (S64.logxor a s64_ones) = S64.v (S64.lognot a)))
    [SMTPat (S64.v (S64.logxor a s64_ones))]

(* Logical XOR operator: result of operation with itself *)
assume val axiom_s64_logxor_4: a:s64
  -> Lemma (requires True) (ensures (S64.v (S64.logxor a a) = 0))
    [SMTPat (S64.v (S64.logxor a a))]


(* Logical OR operator: commutativity *)
assume val axiom_s64_logor_1: a:s64 -> b:s64
  -> Lemma (requires True) (ensures (S64.v (S64.logor a b) = S64.v (S64.logor b a)))
    [SMTPat (S64.v (S64.logor a b))]

(* Logical OR operator: result of operation with zero *)
assume val axiom_s64_logor_2: a:s64
  -> Lemma (requires True) (ensures (S64.v (S64.logor a s64_zero) = S64.v a))
    [SMTPat (S64.v (S64.logor a s64_zero))]

(* Logical OR operator: result of operation with ones *)
assume val axiom_s64_logor_3: a:s64
  -> Lemma (requires True) (ensures (S64.v (S64.logor a s64_ones) = S64.v s64_ones))
    [SMTPat (S64.v (S64.logor a s64_ones))]


(* Logical NOT operator: double negation *)
assume val axiom_s64_lognot_1: a:s64
  -> Lemma (requires True) (ensures (S64.v (S64.lognot (S64.lognot a)) = S64.v a))
    [SMTPat (S64.v (S64.lognot (S64.lognot a)))]

(* Logical NOT operator: negation of zeros *)
assume val axiom_s64_lognot_2: unit
  -> Lemma (requires True) (ensures (S64.v (S64.lognot s64_zero) = S64.v s64_ones))
    [SMTPat (S64.v (S64.lognot s64_zero))]

(* Logical NOT operator: negation of ones *)
assume val axiom_s64_lognot_3: unit
  -> Lemma (requires True) (ensures (S64.v (S64.lognot s64_ones) = S64.v s64_zero))
    [SMTPat (S64.v (S64.lognot s64_ones))]
