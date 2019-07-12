module Hacl.Impl.Gf128.Fields

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer
open Lib.Vec128

type field_spec = 
  | F32
  | FNI

inline_for_extraction noextract
let elem_t (s:field_spec) = 
  match s with
  | F32 -> uint64
  | FNI -> vec128

inline_for_extraction noextract
let elem_zero (s:field_spec) : elem_t s = 
  match s with
  | F32 -> u64 0
  | FNI -> vec128_zero

inline_for_extraction noextract
let felem_len (s:field_spec) = 
  match s with
  | F32 -> 2ul
  | FNI -> 1ul

inline_for_extraction noextract
let precomp_len (s:field_spec) = 
  match s with
  | F32 -> 264ul
  | FNI -> 4ul

inline_for_extraction noextract
let felem (s:field_spec) = lbuffer (elem_t s) (felem_len s)
inline_for_extraction noextract
let felem4 (s:field_spec) = lbuffer (elem_t s) (4ul *. felem_len s)
inline_for_extraction noextract
let precomp (s:field_spec) = lbuffer (elem_t s) (precomp_len s)
inline_for_extraction noextract
type block = lbuffer uint8 16ul
inline_for_extraction noextract
type block4 = lbuffer uint8 64ul
inline_for_extraction noextract
let gcm_ctx (s:field_spec) = lbuffer (elem_t s) (felem_len s +. precomp_len s)

inline_for_extraction noextract
val create_felem: s:field_spec -> StackInline (felem s)
	  (requires (fun h -> True))
	  (ensures (fun h0 f h1 -> live h1 f /\ stack_allocated f h0 h1 (Seq.create (v (felem_len s)) (elem_zero s))))
inline_for_extraction noextract
let create_felem s = 
  match s with
  | F32 -> create 2ul (u64 0)
  | FNI -> create 1ul vec128_zero

inline_for_extraction
val felem_set_zero: #s:field_spec -> f:felem s -> StackInline unit
	  (requires (fun h -> live h f))
	  (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))    
let felem_set_zero #s f =  
  match s with
  | F32 -> Hacl.Impl.Gf128.FieldPreComp.felem_set_zero f
  | FNI -> Hacl.Impl.Gf128.FieldNI.felem_set_zero f


inline_for_extraction
val create_felem4: s:field_spec -> StackInline (felem4 s)
	  (requires (fun h -> True))
	  (ensures (fun h0 f h1 -> live h1 f /\ 
	    stack_allocated f h0 h1 (Seq.create (v (4ul *. felem_len s)) (elem_zero s))))
let create_felem4 s = 
  match s with
  | F32 -> create 8ul (u64 0)
  | FNI -> create 4ul (vec128_zero)

inline_for_extraction
val create_ctx: s:field_spec -> StackInline (gcm_ctx s)
	  (requires (fun h -> True))
	  (ensures (fun h0 f h1 -> live h1 f /\ 
	    stack_allocated f h0 h1 (Seq.create (v (felem_len s +. precomp_len s)) (elem_zero s))))
let create_ctx s = 
  match s with
  | F32 -> create 266ul (u64 0)
  | FNI -> create 5ul (vec128_zero)

inline_for_extraction
val load_felem: #s:field_spec -> x:felem s -> y:block -> Stack unit
	  (requires (fun h -> live h x /\ live h y))
	  (ensures (fun h0 _ h1 -> live h1 x /\ live h1 y /\ modifies (loc x) h0 h1))
let load_felem #s x y = 
  match s with
  | F32 -> Hacl.Impl.Gf128.FieldPreComp.load_felem x y
  | FNI -> Hacl.Impl.Gf128.FieldNI.load_felem x y

inline_for_extraction
val load_felem4: #s:field_spec -> x:felem4 s -> y:block4 -> Stack unit
	  (requires (fun h -> live h x /\ live h y))
	  (ensures (fun h0 _ h1 -> live h1 x /\ live h1 y /\ modifies (loc x) h0 h1))
let load_felem4 #s x y = 
  match s with
  | F32 -> Hacl.Impl.Gf128.FieldPreComp.load_felem4 x y
  | FNI -> Hacl.Impl.Gf128.FieldNI.load_felem4 x y

inline_for_extraction
val store_felem: #s:field_spec -> x:block -> y:felem s -> Stack unit
	  (requires (fun h -> live h x /\ live h y))
	  (ensures (fun h0 _ h1 -> live h1 x /\ live h1 y /\ modifies (loc x) h0 h1))
let store_felem #s x y = 
  match s with
  | F32 -> Hacl.Impl.Gf128.FieldPreComp.store_felem x y
  | FNI -> Hacl.Impl.Gf128.FieldNI.store_felem x y

inline_for_extraction
val get_acc: #s:field_spec -> ctx:gcm_ctx s -> Stack (felem s)
	     (requires (fun h -> live h ctx))
	     (ensures (fun h0 f h1 -> h0 == h1 /\ live h1 f))
let get_acc #s ctx = 
  match s with
  | F32 -> Hacl.Impl.Gf128.FieldPreComp.get_acc ctx
  | FNI -> Hacl.Impl.Gf128.FieldNI.get_acc ctx

inline_for_extraction
val get_r: #s:field_spec -> ctx:gcm_ctx s -> Stack (felem s)
	     (requires (fun h -> live h ctx))
	     (ensures (fun h0 f h1 -> h0 == h1 /\ live h1 f))
let get_r #s ctx = 
  match s with
  | F32 -> Hacl.Impl.Gf128.FieldPreComp.get_r ctx
  | FNI -> Hacl.Impl.Gf128.FieldNI.get_r ctx


inline_for_extraction
val get_precomp: #s:field_spec -> ctx:gcm_ctx s -> Stack (precomp s)
	     (requires (fun h -> live h ctx))
	     (ensures (fun h0 f h1 -> h0 == h1 /\ live h1 f))
let get_precomp #s ctx = 
  match s with
  | F32 -> Hacl.Impl.Gf128.FieldPreComp.get_precomp ctx
  | FNI -> Hacl.Impl.Gf128.FieldNI.get_precomp ctx


inline_for_extraction
val load_precompute_r: #s:field_spec -> pre:precomp s -> key:block -> Stack unit
	  (requires (fun h -> live h pre /\ live h key))
	  (ensures (fun h0 _ h1 -> modifies (loc pre) h0 h1))

let load_precompute_r #s pre key = 
  match s with
  | F32 -> Hacl.Impl.Gf128.FieldPreComp.load_precompute_r pre key
  | FNI -> Hacl.Impl.Gf128.FieldNI.load_precompute_r pre key

inline_for_extraction
val fadd: #s:field_spec -> x:felem s -> y:felem s -> Stack unit
	  (requires (fun h -> live h x /\ live h y))
	  (ensures (fun h0 _ h1 -> live h1 x /\ live h1 y /\ modifies (loc x) h0 h1))
let fadd #s x y =
  match s with
  | F32 -> Hacl.Impl.Gf128.FieldPreComp.fadd x y
  | FNI -> Hacl.Impl.Gf128.FieldNI.fadd x y 

inline_for_extraction
val fmul: #s:field_spec -> x:felem s -> y:felem s -> Stack unit
	  (requires (fun h -> live h x /\ live h y))
	  (ensures (fun h0 _ h1 -> live h1 x /\ live h1 y /\ modifies (loc x) h0 h1))
let fmul #s x y =
  match s with
  | F32 -> Hacl.Impl.Gf128.FieldPreComp.fmul x y
  | FNI -> Hacl.Impl.Gf128.FieldNI.fmul x y 

inline_for_extraction
val fadd4: #s:field_spec -> x:felem4 s -> y:felem4 s -> Stack unit
	  (requires (fun h -> live h x /\ live h y))
	  (ensures (fun h0 _ h1 -> live h1 x /\ live h1 y /\ modifies (loc x) h0 h1))
let fadd4 #s x y =
  match s with
  | F32 -> Hacl.Impl.Gf128.FieldPreComp.fadd4 x y
  | FNI -> Hacl.Impl.Gf128.FieldNI.fadd4 x y 


inline_for_extraction
val fmul_pre: #s:field_spec -> x:felem s -> y:precomp s -> Stack unit
	  (requires (fun h -> live h x /\ live h y))
	  (ensures (fun h0 _ h1 -> live h1 x /\ live h1 y /\ modifies (loc x) h0 h1))
let fmul_pre #s x y =
  match s with
  | F32 -> Hacl.Impl.Gf128.FieldPreComp.fmul_pre x y
  | FNI -> Hacl.Impl.Gf128.FieldNI.fmul_pre x y 


inline_for_extraction
val fmul4: #s:field_spec -> x:felem4 s -> y:precomp s -> Stack unit
	  (requires (fun h -> live h x /\ live h y))
	  (ensures (fun h0 _ h1 -> live h1 x /\ live h1 y /\ modifies (loc x) h0 h1))
let fmul4 #s x pre =
  match s with
  | F32 -> Hacl.Impl.Gf128.FieldPreComp.fmul4 x pre
  | FNI -> Hacl.Impl.Gf128.FieldNI.fmul4 x pre

inline_for_extraction
val fadd_mul4: #s:field_spec -> acc:felem s -> x:felem4 s -> y:precomp s -> Stack unit
	  (requires (fun h -> live h acc /\ live h x /\ live h y))
	  (ensures (fun h0 _ h1 -> live h1 acc /\ live h1 x /\ live h1 y /\ modifies (loc acc) h0 h1))
let fadd_mul4 #s acc x pre =
  match s with
  | F32 -> Hacl.Impl.Gf128.FieldPreComp.fadd_mul4 acc x pre
  | FNI -> Hacl.Impl.Gf128.FieldNI.fadd_mul4 acc x pre


