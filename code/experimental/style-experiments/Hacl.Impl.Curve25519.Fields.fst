module Hacl.Impl.Curve25519.Fields

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer
module F51 = Hacl.Impl.Curve25519.Field51
module F64 = Hacl.Impl.Curve25519.Field64


type field_spec = 
  | M51
  | M64


unfold
let limb (s:field_spec) =
  match s with
  | M51 -> uint64
  | M64 -> uint64

unfold
let limb_zero (s:field_spec) : limb s=
  match s with
  | M51 -> u64 0
  | M64 -> u64 0

unfold
let wide (s:field_spec) =
  match s with
  | M51 -> uint128
  | M64 -> uint128

unfold
let nlimb (s:field_spec) : size_t =
  match s with
  | M51 -> 5ul
  | M64 -> 4ul
  
type felem (s:field_spec) = lbuffer (limb s) (nlimb s)
type felem_wide (s:field_spec) = lbuffer (wide s) (nlimb s)


noextract 
val as_nat: #s:field_spec -> h:mem -> e:felem s-> GTot nat 
let as_nat #s h (e:felem s) = 
  match s with
  | M51 -> F51.as_nat h e
  | M64 -> admit()
  
inline_for_extraction
val create_felem: s:field_spec -> StackInline (felem s)
                   (requires (fun h -> True))
		   (ensures (fun h0 f h1 -> stack_allocated f h0 h1 (Seq.create (v (nlimb s)) (limb_zero s)) /\ as_nat h1 f == 0))
inline_for_extraction
let create_felem s = 
  match s with
  | M51 -> (F51.create_felem ()) <: felem s
  | M64 -> admit(); (F64.create_felem ()) <: felem s



inline_for_extraction
val load_felem: #s:field_spec -> f:felem s -> u64s:lbuffer uint64 4ul -> Stack unit
                   (requires (fun h -> live h f /\ live h u64s))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
inline_for_extraction
let load_felem (#s:field_spec) (f:felem s) (b:lbuffer uint64 4ul) =
  match s with
  | M51 -> F51.load_felem f b
  | M64 -> F64.load_felem f b

inline_for_extraction
val store_felem: #s:field_spec -> b:lbuffer uint64 4ul -> f:felem s -> Stack unit
                   (requires (fun h -> live h f /\ live h b))
		   (ensures (fun h0 _ h1 -> modifies (loc b) h0 h1))
inline_for_extraction
let store_felem #s b f = 
  match s with
  | M51 -> F51.store_felem b f 
  | M64 -> F64.store_felem b f 

inline_for_extraction
val set_bit1: #s:field_spec -> f:felem s -> i:size_t{size_v i < 255} -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
inline_for_extraction
let set_bit1 #s f i =
  match s with
  | M51 -> F51.set_bit1 f i
  | M64 -> F64.set_bit1 f i

inline_for_extraction
val set_bit0: #s:field_spec -> f:felem s -> i:size_t{size_v i < 255} -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
inline_for_extraction
let set_bit0 #s f i =
  match s with
  | M51 -> F51.set_bit0 f i
  | M64 -> F64.set_bit0 f i


inline_for_extraction
val set_zero: #s:field_spec -> f:felem s -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
inline_for_extraction
let set_zero (#s:field_spec) (f:felem s) = 
  match s with
  | M51 -> F51.set_zero f
  | M64 -> F64.set_zero f

inline_for_extraction
val copy_felem: #s:field_spec -> f:felem s -> f':felem s -> Stack unit
                   (requires (fun h -> live h f /\ live h f'))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
inline_for_extraction
let copy_felem (#s:field_spec) (f:felem s) (f':felem s) = 
  match s with
  | M51 -> F51.copy_felem f f'
  | M64 -> F64.copy_felem f f'

inline_for_extraction
val fadd: #s:field_spec -> out:felem s -> f1:felem s -> f2:felem s -> Stack unit
                   (requires (fun h -> live h out /\ live h f1 /\ live h f2))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
inline_for_extraction
let fadd #s out f1 f2=
  match s with
  | M51 -> admit(); F51.fadd out f1 f2 
  | M64 -> admit(); F64.fadd out f1 f2 

inline_for_extraction
val fsub: #s:field_spec -> out:felem s -> f1:felem s -> f2:felem s -> Stack unit
                   (requires (fun h -> live h out /\ live h f1 /\ live h f2))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
inline_for_extraction
let fsub #s out f1 f2=
  match s with
  | M51 -> F51.fsub out f1 f2 
  | M64 -> F64.fsub out f1 f2 


inline_for_extraction
val fmul: #s:field_spec -> out:felem s -> f1:felem s -> f2:felem s -> Stack unit
                   (requires (fun h -> live h out /\ live h f1 /\ live h f2))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\ live h1 out /\ live h1 f1 /\ live h1 f2))
inline_for_extraction
let fmul #s out f1 f2=
  match s with
  | M51 -> F51.fmul out f1 f2 
  | M64 -> F64.fmul out f1 f2 

inline_for_extraction
val fmul2: #s:field_spec -> out1:felem s -> out2:felem s -> f1:felem s -> f2:felem s -> f3:felem s -> f4:felem s -> Stack unit
                   (requires (fun h -> live h out1 /\ live h out2 /\ live h f1 /\ live h f2 /\ live h f3 /\ live h f4))
		   (ensures (fun h0 _ h1 -> modifies (loc out1 |+| loc out2) h0 h1))
inline_for_extraction
let fmul2 #s out1 out2 f1 f2 f3 f4=
  match s with
  | M51 -> F51.fmul2 out1 out2 f1 f2 f3 f4 
  | M64 -> F64.fmul2 out1 out2 f1 f2 f3 f4 

inline_for_extraction
val fmul1: #s:field_spec -> out:felem s -> f1:felem s -> f2:uint64 -> Stack unit
                   (requires (fun h -> live h out /\ live h f1))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\ live h1 out /\ live h1 f1))
inline_for_extraction
let fmul1 #s out f1 f2 =
  match s with
  | M51 -> F51.fmul1 out f1 f2 
  | M64 -> F64.fmul1 out f1 f2 

inline_for_extraction
val fsqr: #s:field_spec -> out:felem s -> f1:felem s -> Stack unit
                   (requires (fun h -> live h out /\ 
				    live h f1))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
inline_for_extraction
let fsqr #s out f1 =
  match s with
  | M51 -> F51.fsqr out f1 
  | M64 -> F64.fsqr out f1 


[@ CInline]
val fsqr2: #s:field_spec -> out1:felem s -> out2:felem s -> f1:felem s -> f2:felem s -> Stack unit
                   (requires (fun h -> live h out1 /\ live h out2 /\ live h f1 /\ live h f2))
		   (ensures (fun h0 _ h1 -> modifies (loc out1 |+| loc out2) h0 h1))
[@ CInline]
let fsqr2 #s out1 out2 f1 f2 = 
  match s with
  | M51 -> F51.fsqr2 out1 out2 f1 f2
  | M64 -> F64.fsqr2 out1 out2 f1 f2
  
