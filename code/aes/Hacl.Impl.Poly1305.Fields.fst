module Hacl.Impl.Poly1305.Fields

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open LowStar.Buffer
open Lib.Utils
open Lib.Vec128
module F32 = Hacl.Impl.Poly1305.Field32
module F64 = Hacl.Impl.Poly1305.Field64
module F128 = Hacl.Impl.Poly1305.Field128

type field_spec = 
  | M32 
  | M64 
  | M128 


unfold
let limb (s:field_spec) =
  match s with
  | M32 -> uint32
  | M64 -> uint64
  | M128 -> vec128

unfold
let limb_zero (s:field_spec) : limb s=
  match s with
  | M32 -> u32 0 
  | M64 -> u64 0
  | M128 -> vec128_zero

unfold
let wide (s:field_spec) =
  match s with
  | M32 -> uint64
  | M64 -> uint128
  | M128 -> vec128

unfold
let nlimb (s:field_spec) : size_nat =
  match s with
  | M32 -> 5
  | M64 -> 3
  | M128 -> 5

unfold
let blocklen (s:field_spec) : size_nat =
  match s with
  | M32 -> 16
  | M64 -> 16
  | M128 -> 32


type felem (s:field_spec) = lbuffer (limb s) (nlimb s)
type felem_wide (s:field_spec) = lbuffer (wide s) (nlimb s)

noextract 
val as_nat: #s:field_spec -> h:mem -> e:felem s-> GTot nat 
let as_nat #s h (e:felem s) = 
  match s with
  | M32 -> F32.as_nat h e
  | M64 -> F64.as_nat h e
  | M128 -> admit()
  
inline_for_extraction
val create_felem: s:field_spec -> StackInline (felem s)
                   (requires (fun h -> True))
		   (ensures (fun h0 f h1 -> live h1 f 
			    /\ as_nat h1 f == 0))
let create_felem s = 
  match s with
  | M32 -> (F32.create_felem ()) <: felem s
  | M64 -> (F64.create_felem ()) <: felem s
  | M128 -> (F128.create_felem ()) <: felem s


inline_for_extraction
val load_felem_le: #s:field_spec -> f:felem s -> b:lbytes 16 -> Stack unit
                   (requires (fun h -> live h f /\ live h b))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f) h0 h1))
let load_felem_le (#s:field_spec) (f:felem s) (b:lbytes 16) =
  match s with
  | M32 -> F32.load_felem_le f b
  | M64 -> F64.load_felem_le f b
  | M128 -> F128.load_felem_le f b

inline_for_extraction
val store_felem_le: #s:field_spec -> b:lbytes 16 -> f:felem s -> Stack unit
                   (requires (fun h -> live h f /\ live h b))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer b) h0 h1))
let store_felem_le #s b f = 
  match s with
  | M32 -> F32.store_felem_le b f 
  | M64 -> F64.store_felem_le b f 
  | M128 -> F128.store_felem_le b f 

inline_for_extraction
val set_bit: #s:field_spec -> f:felem s -> i:size_t{size_v i < 130} -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f) h0 h1))
let set_bit (#s:field_spec) (f:felem s) (i:size_t{size_v i < 130}) = 
  match s with
  | M32 -> F32.set_bit f i
  | M64 -> F64.set_bit f i
  | M128 -> F128.set_bit f i

inline_for_extraction
val set_bit128: #s:field_spec -> f:felem s -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f) h0 h1))
let set_bit128 (#s:field_spec) (f:felem s) = 
  match s with
  | M32 -> F32.set_bit128 f
  | M64 -> F64.set_bit128 f
  | M128 -> F128.set_bit128 f


inline_for_extraction
val set_zero: #s:field_spec -> f:felem s -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f) h0 h1))
let set_zero (#s:field_spec) (f:felem s) = 
  match s with
  | M32 -> F32.set_zero f
  | M64 -> F64.set_zero f
  | M128 -> F128.set_zero f

inline_for_extraction
val copy_felem: #s:field_spec -> f:felem s -> f':felem s -> Stack unit
                   (requires (fun h -> live h f /\ live h f'))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f) h0 h1))
let copy_felem (#s:field_spec) (f:felem s) (f':felem s) = 
  match s with
  | M32 -> F32.copy_felem f f'
  | M64 -> F64.copy_felem f f'
  | M128 -> F128.copy_felem f f'


inline_for_extraction
val reduce_felem: #s:field_spec -> f:felem s -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f) h0 h1))
let reduce_felem #s f =
  match s with
  | M32 -> F32.reduce_felem f
  | M64 -> F64.reduce_felem f
  | M128 -> F128.reduce_felem f
  
inline_for_extraction
val precompute_shift_reduce: #s:field_spec -> f1:felem s -> f2:felem s-> Stack unit
                   (requires (fun h -> live h f1 /\ live h f2))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f1) h0 h1))
let precompute_shift_reduce #s f1 f2 = 
  match s with
  | M32 -> F32.precompute_shift_reduce f1 f2
  | M64 -> F64.precompute_shift_reduce f1 f2
  | M128 -> F128.precompute_shift_reduce f1 f2


inline_for_extraction
val fmul: #s:field_spec -> out:felem s -> f1:felem s -> f2:felem s -> precomp:felem s -> Stack unit
                   (requires (fun h -> live h out /\ live h f1 /\ live h f2 /\ live h precomp))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer out) h0 h1))
let fmul #s out f1 f2 precomp =
  match s with
  | M32 -> F32.fmul out f1 f2 precomp
  | M64 -> F64.fmul out f1 f2 precomp
  | M128 -> F128.fmul out f1 f2 precomp


inline_for_extraction
val fadd_mul: #s:field_spec -> out:felem s -> f1:felem s -> f2:felem s -> precomp:felem s -> Stack unit
                   (requires (fun h -> live h out /\ live h f1 /\ live h f2 /\ live h precomp))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer out) h0 h1))
let fadd_mul #s out f1 f2 precomp =
  match s with
  | M32 -> F32.fadd_mul out f1 f2 precomp
  | M64 -> F64.fadd_mul out f1 f2 precomp
  | M128 -> F128.fadd_mul out f1 f2 precomp



inline_for_extraction
val fadd: #s:field_spec -> out:felem s -> f1:felem s -> f2:felem s -> Stack unit
                   (requires (fun h -> live h out /\ live h f1 /\ live h f2))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer out) h0 h1))
let fadd #s out f1 f2=
  match s with
  | M32 -> F32.fadd out f1 f2 
  | M64 -> F64.fadd out f1 f2 
  | M128 -> F128.fadd out f1 f2 

