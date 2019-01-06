module Hacl.Impl.Poly1305.Fields

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.Vec256
//module F32 = Hacl.Impl.Poly1305.Field32
module F64 = Hacl.Impl.Poly1305.Field64
//module F128 = Hacl.Impl.Poly1305.Field128
//module F256 = Hacl.Impl.Poly1305.Field256
module F32xN = Hacl.Impl.Poly1305.Field32xN

type field_spec = 
  | M32 
  | M64 
  | M128 
  | M256


unfold
let limb (s:field_spec) =
  match s with
//  | M32 -> uint32
  | M32 -> F32xN.uint64xN 1
  | M64 -> uint64
//  | M128 -> F128.uint64x2
  | M128 -> F32xN.uint64xN 2
//  | M256 -> vec256
  | M256 -> F32xN.uint64xN 4

unfold
let limb_zero (s:field_spec) : limb s=
  match s with
//  | M32 -> u32 0 
  | M32 -> F32xN.zero 1 
  | M64 -> u64 0
//  | M128 -> F128.zero
  | M128 -> F32xN.zero 2
//| M256 -> vec256_zero
  | M256 -> F32xN.zero 4
  
unfold
let wide (s:field_spec) =
  match s with
//  | M32 -> uint64
  | M32 -> F32xN.uint64xN 1
  | M64 -> uint128
//  | M128 -> F128.uint64x2
  | M128 -> F32xN.uint64xN 2
//  | M256 -> vec256
  | M256 -> F32xN.uint64xN 4

unfold
let nlimb (s:field_spec) : size_t =
  match s with
  | M32 -> 5ul
  | M64 -> 3ul
  | M128 -> 5ul
  | M256 -> 5ul

unfold
let blocklen (s:field_spec) : size_t =
  match s with
  | M32 -> 16ul
  | M64 -> 16ul
  | M128 -> 32ul
  | M256 -> 64ul

unfold
let nelem (s:field_spec) : size_t =
  match s with
  | M32 -> 1ul
  | M64 -> 1ul
  | M128 -> 2ul
  | M256 -> 4ul

unfold
let precomplen (s:field_spec) : size_t =
  match s with
//  | M32 -> 10ul
  | M32 -> 20ul
  | M64 -> 6ul
  | M128 -> 20ul
  | M256 -> 20ul


type felem (s:field_spec) = lbuffer (limb s) (nlimb s)
type felem_wide (s:field_spec) = lbuffer (wide s) (nlimb s)
type precomp_r (s:field_spec) = lbuffer (limb s) (precomplen s)
noextract 
val as_nat: #s:field_spec -> h:mem -> e:felem s-> GTot nat 
let as_nat #s h (e:felem s) = 
  match s with
  | M32 -> admit() //F32.as_nat h e
  | M64 -> F64.as_nat h e
  | M128 -> admit()
  | M256 -> admit()
  
inline_for_extraction
val create_felem: s:field_spec -> StackInline (felem s)
                   (requires (fun h -> True))
		   (ensures (fun h0 f h1 -> live h1 f))
let create_felem s = 
  match s with
//  | M32 -> (F32.create_felem ()) <: felem s
  | M32 -> (F32xN.create_felem 1) <: felem s
  | M64 -> (F64.create_felem ()) <: felem s
//  | M128 -> (F128.create_felem ()) <: felem s
  | M128 -> (F32xN.create_felem 2) <: felem s
//  | M256 -> (F256.create_felem ()) <: felem s
  | M256 -> (F32xN.create_felem 4) <: felem s


inline_for_extraction
val load_felem_le: #s:field_spec -> f:felem s -> b:lbuffer uint8 16ul -> Stack unit
                   (requires (fun h -> live h f /\ live h b))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let load_felem_le (#s:field_spec) (f:felem s) (b:lbuffer uint8 16ul) =
  match s with
//  | M32 -> F32.load_felem_le f b
  | M32 -> F32xN.load_felem_le #1 f b
  | M64 -> F64.load_felem_le f b
//  | M128 -> F128.load_felem_le f b
  | M128 -> F32xN.load_felem_le #2 f b
//  | M256 -> F256.load_felem_le f b
  | M256 -> F32xN.load_felem_le #4 f b

inline_for_extraction
val load_felems_le: #s:field_spec -> f:felem s -> b:lbuffer uint8 (blocklen s) -> Stack unit
                   (requires (fun h -> live h f /\ live h b))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let load_felems_le (#s:field_spec) (f:felem s) (b:lbuffer uint8 (blocklen s)) =
  match s with
//  | M32 -> F32.load_felems_le f b
  | M32 -> F32xN.load_felems_le #1 f b
  | M64 -> F64.load_felems_le f b
//  | M128 -> F128.load_felems_le f b
  | M128 -> F32xN.load_felems_le #2 f b
//  | M256 -> F256.load_felems_le f b
  | M256 -> F32xN.load_felems_le #4 f b

inline_for_extraction
val store_felem_le: #s:field_spec -> b:lbuffer uint8 16ul -> f:felem s -> Stack unit
                   (requires (fun h -> live h f /\ live h b))
		   (ensures (fun h0 _ h1 -> modifies (loc b |+| loc f) h0 h1))
let store_felem_le #s b f = 
  match s with
//  | M32 -> admit(); F32.store_felem_le b f 
  | M32 -> F32xN.store_felem_le #1 b f 
  | M64 -> F64.store_felem_le b f 
//  | M128 -> F128.store_felem_le b f 
  | M128 -> F32xN.store_felem_le #2 b f 
//  | M256 -> F256.store_felem_le b f 
  | M256 -> F32xN.store_felem_le #4 b f 

inline_for_extraction
val set_bit: #s:field_spec -> f:felem s -> i:size_t{size_v i < 130} -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let set_bit (#s:field_spec) (f:felem s) (i:size_t{size_v i < 130}) = 
  match s with
//  | M32 -> F32.set_bit f i
  | M32 -> F32xN.set_bit #1 f i
  | M64 -> F64.set_bit f i
//  | M128 -> F128.set_bit f i
  | M128 -> F32xN.set_bit #2 f i
//| M256 -> F256.set_bit f i
  | M256 -> F32xN.set_bit #4 f i
  
inline_for_extraction
val set_bit128: #s:field_spec -> f:felem s -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let set_bit128 (#s:field_spec) (f:felem s) = 
  match s with
//  | M32 -> F32.set_bit128 f
  | M32 -> F32xN.set_bit128 #1 f
  | M64 -> F64.set_bit128 f
//  | M128 -> F128.set_bit128 f
  | M128 -> F32xN.set_bit128 #2 f
//  | M256 -> F256.set_bit128 f
  | M256 -> F32xN.set_bit128 #4 f


inline_for_extraction
val set_zero: #s:field_spec -> f:felem s -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let set_zero (#s:field_spec) (f:felem s) = 
  match s with
//  | M32 -> F32.set_zero f
  | M32 -> F32xN.set_zero #1 f
  | M64 -> F64.set_zero f
//  | M128 -> F128.set_zero f
  | M128 -> F32xN.set_zero #2 f
//  | M256 -> F256.set_zero f
  | M256 -> F32xN.set_zero #4 f

inline_for_extraction
val copy_felem: #s:field_spec -> f:felem s -> f':felem s -> Stack unit
                   (requires (fun h -> live h f /\ live h f'))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let copy_felem (#s:field_spec) (f:felem s) (f':felem s) = 
  match s with
//  | M32 -> F32.copy_felem f f'
  | M32 -> F32xN.copy_felem #1 f f'
  | M64 -> F64.copy_felem f f'
//  | M128 -> F128.copy_felem f f'
  | M128 -> F32xN.copy_felem #2 f f'
//  | M256 -> F256.copy_felem f f'
  | M256 -> F32xN.copy_felem #4 f f'


inline_for_extraction
val reduce_felem: #s:field_spec -> f:felem s -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let reduce_felem #s f =
  match s with
//  | M32 -> admit(); F32.reduce_felem f
  | M32 -> F32xN.reduce_felem #1 f
  | M64 -> F64.reduce_felem f
//  | M128 -> F128.reduce_felem f
  | M128 -> F32xN.reduce_felem #2 f
//  | M256 -> F256.reduce_felem f
  | M256 -> F32xN.reduce_felem #4 f
  
inline_for_extraction
val load_precompute_r: #s:field_spec -> p:precomp_r s -> r0:uint64 -> r1:uint64 -> Stack unit
                   (requires (fun h -> live h p))
		   (ensures (fun h0 _ h1 -> modifies (loc p) h0 h1))
let load_precompute_r #s p r0 r1 = 
  match s with
//  | M32 -> F32.load_precompute_r p r0 r1
  | M32 -> F32xN.load_precompute_r #1 p r0 r1
  | M64 -> F64.load_precompute_r p r0 r1
//  | M128 -> F128.load_precompute_r p r0 r1
  | M128 -> F32xN.load_precompute_r #2 p r0 r1
//  | M256 -> F256.load_precompute_r p r0 r1
  | M256 -> F32xN.load_precompute_r #4 p r0 r1


inline_for_extraction
val fmul_r: #s:field_spec -> out:felem s -> f1:felem s -> precomp:precomp_r s -> Stack unit
                   (requires (fun h -> live h out /\ live h f1 /\ live h precomp))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
let fmul_r #s out f1 precomp =
  match s with
//  | M32 -> admit(); F32.fmul_r out f1 precomp
  | M32 -> F32xN.fmul_r #1 out f1 precomp
  | M64 -> F64.fmul_r out f1 precomp
//  | M128 -> F128.fmul_r out f1 precomp
  | M128 -> F32xN.fmul_r #2 out f1 precomp
//  | M256 -> F256.fmul_r out f1 precomp
  | M256 -> F32xN.fmul_r #4 out f1 precomp

inline_for_extraction
val fadd_mul_r: #s:field_spec -> out:felem s -> f1:felem s -> precomp:precomp_r s -> Stack unit
                   (requires (fun h -> live h out /\ live h f1 /\ live h precomp))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
let fadd_mul_r #s out f1 precomp =
  match s with
//  | M32 -> F32.fadd_mul_r out f1 precomp
  | M32 -> F32xN.fadd_mul_r #1 out f1 precomp
  | M64 -> F64.fadd_mul_r out f1 precomp
//  | M128 -> F128.fadd_mul_r out f1 precomp
  | M128 -> F32xN.fadd_mul_r #2 out f1 precomp
//  | M256 -> F256.fadd_mul_r out f1 precomp
  | M256 -> F32xN.fadd_mul_r #4 out f1 precomp

inline_for_extraction
val fmul_rn: #s:field_spec -> out:felem s -> f1:felem s -> precomp:precomp_r s -> Stack unit
                   (requires (fun h -> live h out /\ live h f1 /\ live h precomp))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
let fmul_rn #s out f1 precomp =
  match s with
//  | M32 -> F32.fmul_rn out f1 precomp
  | M32 -> F32xN.fmul_rn #1 out f1 precomp
  | M64 -> F64.fmul_rn out f1 precomp
//  | M128 -> F128.fmul_rn out f1 precomp
  | M128 -> F32xN.fmul_rn #2 out f1 precomp
//  | M256 -> F256.fmul_rn out f1 precomp
  | M256 -> F32xN.fmul_rn #4 out f1 precomp

inline_for_extraction
val fmul_rn_normalize: #s:field_spec -> out:felem s -> precomp:precomp_r s -> Stack unit
                   (requires (fun h -> live h out /\ live h precomp))
		   (ensures (fun h0 _ h1 -> modifies (loc out |+| loc precomp) h0 h1))
let fmul_rn_normalize #s out precomp =
  match s with
//  | M32 -> F32.fmul_rn_normalize out precomp
  | M32 -> F32xN.fmul_rn_normalize #1 out precomp
  | M64 -> F64.fmul_rn_normalize out precomp
//  | M128 -> F128.fmul_rn_normalize out precomp
  | M128 -> F32xN.fmul_rn_normalize #2 out precomp
//  | M256 -> F256.fmul_rn_normalize out precomp
  | M256 -> F32xN.fmul_rn_normalize #4 out precomp

inline_for_extraction
val fadd: #s:field_spec -> out:felem s -> f1:felem s -> f2:felem s -> Stack unit
                   (requires (fun h -> live h out /\ live h f1 /\ live h f2))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
let fadd #s out f1 f2=
  match s with
//  | M32 -> admit(); F32.fadd out f1 f2 
  | M32 -> F32xN.fadd #1 out f1 f2 
  | M64 -> admit(); F64.fadd out f1 f2 
//  | M128 -> F128.fadd out f1 f2 
  | M128 -> F32xN.fadd #2 out f1 f2 
//  | M256 -> F256.fadd out f1 f2 
  | M256 -> F32xN.fadd #4 out f1 f2 
