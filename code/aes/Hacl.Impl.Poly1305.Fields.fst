module Hacl.Impl.Poly1305.Fields

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open LowStar.Buffer
open Lib.Utils
module F32 = Hacl.Impl.Poly1305.Field32
module F64 = Hacl.Impl.Poly1305.Field64

type field_spec = 
  | M32 
  | M64 


unfold
let limb (s:field_spec) =
  match s with
  | M32 -> uint32
  | M64 -> uint64

unfold
let limb_zero (s:field_spec) : limb s=
  match s with
  | M32 -> u32 0 
  | M64 -> u64 0

unfold
let wide (s:field_spec) =
  match s with
  | M32 -> uint64
  | M64 -> uint128

unfold
let nlimb (s:field_spec) : size_nat =
  match s with
  | M32 -> 5
  | M64 -> 3

unfold
let blocklen (s:field_spec) : size_nat =
  match s with
  | M32 -> 1
  | M64 -> 1


type felem (s:field_spec) = lbuffer (limb s) (nlimb s)
type felem_wide (s:field_spec) = lbuffer (wide s) (nlimb s)

noextract 
val as_nat: #s:field_spec -> h:mem -> e:felem s-> GTot nat 
let as_nat #s h (e:felem s) = 
  match s with
  | M32 -> F32.as_nat h e
  | M64 -> F64.as_nat h e
  
inline_for_extraction
val create_felem: s:field_spec -> StackInline (felem s)
                   (requires (fun h -> True))
		   (ensures (fun h0 f h1 -> live h1 f 
			    /\ as_nat h1 f == 0))
let create_felem s = 
  match s with
  | M32 -> (F32.create_felem ()) <: felem s
  | M64 -> (F64.create_felem ()) <: felem s


inline_for_extraction
val carry_felem: #s:field_spec -> f:felem s -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f) h0 h1))
let carry_felem #s f =
  match s with
  | M32 -> F32.carry_felem f
  | M64 -> F64.carry_felem f

inline_for_extraction
val carry_top_felem: #s:field_spec -> f:felem s -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f) h0 h1))
let carry_top_felem #s f =
  match s with
  | M32 -> F32.carry_top_felem f
  | M64 -> F64.carry_top_felem f

inline_for_extraction
val load_felem: #s:field_spec -> f:felem s -> lo:uint64 -> hi:uint64 -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f) h0 h1))
let load_felem (#s:field_spec) (f:felem s) (lo:uint64) (hi:uint64) = 
  match s with
  | M32 -> F32.load_felem f lo hi
  | M64 -> F64.load_felem f lo hi

inline_for_extraction
val load_felem_le: #s:field_spec -> f:felem s -> b:lbytes 16 -> Stack unit
                   (requires (fun h -> live h f /\ live h b))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f) h0 h1))
let load_felem_le (#s:field_spec) (f:felem s) (b:lbytes 16) =
  match s with
  | M32 -> F32.load_felem_le f b
  | M64 -> F64.load_felem_le f b

inline_for_extraction
val store_felem: #s:field_spec -> f:felem s -> Stack (lo:uint64 * hi:uint64)
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> h0 == h1))
let store_felem (#s:field_spec) (f:felem s) =
  match s with
  | M32 -> F32.store_felem f
  | M64 -> F64.store_felem f 

inline_for_extraction
val set_bit: #s:field_spec -> f:felem s -> i:size_t{size_v i < 130} -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f) h0 h1))
let set_bit (#s:field_spec) (f:felem s) (i:size_t{size_v i < 130}) = 
  match s with
  | M32 -> F32.set_bit f i
  | M64 -> F64.set_bit f i

inline_for_extraction
val set_bit128: #s:field_spec -> f:felem s -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f) h0 h1))
let set_bit128 (#s:field_spec) (f:felem s) = 
  match s with
  | M32 -> F32.set_bit128 f
  | M64 -> F64.set_bit128 f


inline_for_extraction
val set_zero: #s:field_spec -> f:felem s -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f) h0 h1))
let set_zero (#s:field_spec) (f:felem s) = 
  match s with
  | M32 -> F32.set_zero f
  | M64 -> F64.set_zero f

inline_for_extraction
val smul_top_felem: #s:field_spec -> f1:felem s -> f2:felem s-> Stack unit
                   (requires (fun h -> live h f1 /\ live h f2))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f1) h0 h1))
let smul_top_felem #s f1 f2 = 
  match s with
  | M32 -> F32.smul_top_felem f1 f2
  | M64 -> F64.smul_top_felem f1 f2


inline_for_extraction
val fadd_mul_felem: #s:field_spec -> acc:felem s -> f1:felem s -> f2:felem s -> f2_20:felem s -> Stack unit
                   (requires (fun h -> live h acc /\ live h f1 /\ live h f2 /\ live h f2_20))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer acc) h0 h1))
let fadd_mul_felem #s acc f1 f2 f2_20 =
  match s with
  | M32 -> F32.fadd_mul_felem acc f1 f2 f2_20
  | M64 -> F64.fadd_mul_felem acc f1 f2 f2_20

inline_for_extraction
val add_felem: #s:field_spec -> f1:felem s -> f2:felem s -> Stack unit
                   (requires (fun h -> live h f1 /\ live h f2))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f1) h0 h1))
let add_felem #s f1 f2=
  match s with
  | M32 -> F32.add_felem f1 f2 
  | M64 -> F64.add_felem f1 f2 

inline_for_extraction
val subtract_p: #s:field_spec -> f:felem s -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f) h0 h1))
let subtract_p #s f=
  match s with
  | M32 -> F32.subtract_p f
  | M64 -> F64.subtract_p f

