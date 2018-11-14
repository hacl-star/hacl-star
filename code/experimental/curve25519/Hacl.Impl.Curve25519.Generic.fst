module Hacl.Impl.Curve25519.Generic
module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Hacl.Impl.Curve25519.Fields
module F51 = Hacl.Impl.Curve25519.Field51
module F64 = Hacl.Impl.Curve25519.Field64

#set-options "--z3rlimit 50 --max_fuel 2 --max_ifuel 2"
#set-options "--debug Hacl.Impl.Curve25519.Generic --debug_level ExtractNorm"

inline_for_extraction noextract
val fsquare_times_: #s:field_spec -> o:felem s -> i:felem s -> n:size_t{v n > 0} -> Stack unit
	     (requires (fun h0 -> live h0 o /\ live h0 i))
	     (ensures (fun h0 _ h1 -> modifies (loc o) h0 h1 /\ live h1 o /\ live h1 i))
inline_for_extraction noextract
let fsquare_times_ #s o i n = 
    fsqr #s o i;
    let h0 = ST.get() in
    loop1 h0 (n -! 1ul) o
    (fun h -> (fun i s -> s))
    (fun i -> fsqr #s o o; admit())

(* WRAPPER to Prevent Inlining *)
[@CInline]
let fsquare_times_51 (o:F51.felem) (i:F51.felem) (n:size_t{v n > 0}) = fsquare_times_ #M51 o i n
[@CInline]
let fsquare_times_64 (o:F64.felem) (i:F64.felem) (n:size_t{v n > 0}) = fsquare_times_ #M64 o i n

inline_for_extraction noextract
val fsquare_times: #s:field_spec -> o:felem s -> i:felem s -> n:size_t{v n > 0} -> Stack unit
	     (requires (fun h0 -> live h0 o /\ live h0 i))
	     (ensures (fun h0 _ h1 -> modifies (loc o) h0 h1 /\ live h1 o /\ live h1 i))
let fsquare_times (#s:field_spec) (o:felem s) (i:felem s) (n:size_t{v n > 0}) =
  match s with
  | M51 -> fsquare_times_51 o i n
  | M64 -> fsquare_times_64 o i n
(* WRAPPER to Prevent Inlining *)


inline_for_extraction noextract
val footprint: h0:mem ->
	     l:Ghost.erased LowStar.Buffer.loc -> 
	     impl: (unit -> Stack unit
			   (requires (fun h -> modifies (Ghost.reveal l) h0 h))
			   (ensures (fun h _ h' -> modifies (Ghost.reveal l) h h'))) ->
	     Stack unit
	      (requires (fun h -> modifies (Ghost.reveal l) h0 h))
	      (ensures (fun _ _ h -> modifies (Ghost.reveal l) h0 h))
inline_for_extraction noextract
let footprint h0 l impl = impl()
	      
inline_for_extraction noextract
val finv_: #s:field_spec -> o:felem s -> i:felem s -> Stack unit
	     (requires (fun h0 -> live h0 o /\ live h0 i))
	     (ensures (fun h0 _ h1 -> modifies (loc o) h0 h1))
inline_for_extraction noextract
let finv_ #s o i = 
  push_frame();
  let tmp = create (4ul *. nlimb s) (limb_zero s) in
  let a : felem s = sub tmp 0ul (nlimb s) in
  let b : felem s = sub tmp (nlimb s) (nlimb s) in
  let c : felem s = sub tmp (2ul *. nlimb s) (nlimb s) in
  let t0 : felem s = sub tmp (3ul *. nlimb s) (nlimb s) in 
  let h0 = ST.get() in
  let gloc = Ghost.hide (loc tmp |+| loc o) in
  (* 2 *) footprint h0 gloc (fun () -> fsquare_times #s a i  1ul); 
  (* 8 *) footprint h0 gloc (fun () -> fsquare_times #s t0 a 2ul); 
  (* 9 *) footprint h0 gloc (fun () -> fmul #s b t0 i); 
  (* 11 *) footprint h0 gloc (fun () -> fmul #s a b a); 
  (* 22 *) footprint h0 gloc (fun () -> fsquare_times #s t0 a 1ul); 
  (* 2^5 - 2^0 = 31 *) footprint h0 gloc (fun () -> fmul #s b t0 b);
  (* 2^10 - 2^5 *) footprint h0 gloc (fun () -> fsquare_times #s t0 b 5ul); 
  (* 2^10 - 2^0 *) footprint h0 gloc (fun () -> fmul #s b t0 b); 
  (* 2^20 - 2^10 *) footprint h0 gloc (fun () -> fsquare_times #s t0 b 10ul); 
  (* 2^20 - 2^0 *) footprint h0 gloc (fun () -> fmul #s c t0 b); 
  (* 2^40 - 2^20 *) footprint h0 gloc (fun () -> fsquare_times #s t0 c 20ul); 
  (* 2^40 - 2^0 *) footprint h0 gloc (fun () -> fmul #s t0 t0 c); 
  (* 2^50 - 2^10 *) footprint h0 gloc (fun () -> fsquare_times #s t0 t0 10ul);
  (* 2^50 - 2^0 *) footprint h0 gloc (fun () -> fmul #s b t0 b); 
  (* 2^100 - 2^50 *) footprint h0 gloc (fun () -> fsquare_times #s t0 b 50ul);
  (* 2^100 - 2^0 *) footprint h0 gloc (fun () -> fmul #s c t0 b); 
  (* 2^200 - 2^100 *) footprint h0 gloc (fun () -> fsquare_times #s t0 c 100ul); 
  (* 2^200 - 2^0 *) footprint h0 gloc (fun () -> fmul #s t0 t0 c); 
  (* 2^250 - 2^50 *) footprint h0 gloc (fun () -> fsquare_times #s t0 t0 50ul); 
  (* 2^250 - 2^0 *) footprint h0 gloc (fun () -> fmul #s t0 t0 b); 
  (* 2^255 - 2^5 *) footprint h0 gloc (fun () -> fsquare_times #s t0 t0 5ul); 
  (* 2^255 - 21 *) footprint h0 gloc (fun () -> fmul #s o t0 a);
  pop_frame()


(* WRAPPER to Prevent Inlining *)
let finv_51 (o:F51.felem) (i:F51.felem) = finv_ #M51 o i 
let finv_64 (o:F64.felem) (i:F64.felem) = finv_ #M64 o i 
inline_for_extraction noextract
val finv: #s:field_spec -> o:felem s -> i:felem s -> Stack unit
	     (requires (fun h0 -> live h0 o /\ live h0 i))
	     (ensures (fun h0 _ h1 -> modifies (loc o) h0 h1))
let finv #s o i =
  match s with
  | M51 -> finv_51 o i
  | M64 -> finv_64 o i
 (* WRAPPER to Prevent Inlining *)



unfold let scalar = lbuffer uint64 4ul
unfold let point (s:field_spec) = lbuffer (limb s) (2ul *. nlimb s)

(* NEEDED ONLY FOR WRAPPERS *)
unfold let point51 = lbuffer uint64 10ul
unfold let point64 = lbuffer uint64 8ul
(* NEEDED ONLY FOR WRAPPERS *)


inline_for_extraction
val decode_scalar: o:scalar -> i:lbuffer uint8 32ul -> Stack unit
			 (requires fun h0 -> live h0 o /\ live h0 i /\ disjoint o i)
			 (ensures fun h0 _ h1 -> modifies (loc o) h0 h1)
inline_for_extraction
let decode_scalar o i = 
  uints_from_bytes_le #U64 o i;
  o.(0ul) <- o.(0ul) &. u64 0xfffffffffffffff8;
  o.(3ul) <- o.(3ul) &. u64 0x7fffffffffffffff;
  o.(3ul) <- o.(3ul) |. u64 0x4000000000000000

inline_for_extraction
val scalar_bit: s:scalar -> n:size_t{v n < 256} -> Stack uint64 
			 (requires fun h0 -> live h0 s)
			 (ensures fun h0 r h1 -> h0 == h1)
inline_for_extraction
let scalar_bit s n = (s.(n /. 64ul) >>. (n %. 64ul)) &. (u64 1)

inline_for_extraction
val decode_point_: #s:field_spec -> o:point s -> i:lbuffer uint8 32ul -> Stack unit 
				  (requires fun h0 -> live h0 o /\ live h0 i /\ disjoint o i)
				 (ensures fun h0 _ h1 -> modifies (loc o) h0 h1)

inline_for_extraction
let decode_point_ #s o i = 
  push_frame();
  let tmp = create 4ul (u64 0) in
  uints_from_bytes_le #U64 tmp i;
  tmp.(3ul) <- tmp.(3ul) &. u64 0x7fffffffffffffff;
  let x : felem s = sub o 0ul (nlimb s) in
  let z : felem s = sub o (nlimb s) (nlimb s) in
  set_zero z;
  set_bit1 z 0ul;
  load_felem x tmp;
  pop_frame()

(* WRAPPER to Prevent Inlining *)
let decode_point_51 (o:point51) i = decode_point_ #M51 o i
let decode_point_64 (o:point64) i = decode_point_ #M64 o i
inline_for_extraction
val decode_point: #s:field_spec -> o:point s -> i:lbuffer uint8 32ul -> Stack unit 
				  (requires fun h0 -> live h0 o /\ live h0 i /\ disjoint o i)
				 (ensures fun h0 _ h1 -> modifies (loc o) h0 h1)

let decode_point #s o i = 
  match s with
  | M51 -> decode_point_51 o i
  | M64 -> decode_point_64 o i
(* WRAPPER to Prevent Inlining *)


inline_for_extraction
val encode_point_: #s:field_spec -> o:lbuffer uint8 32ul -> i:point s  -> Stack unit 
				  (requires fun h0 -> live h0 o /\ live h0 i /\ disjoint o i)
				 (ensures fun h0 _ h1 -> modifies (loc o) h0 h1)

inline_for_extraction
let encode_point_ #s o i = 
  push_frame();
  let x : felem s = sub i 0ul (nlimb s) in
  let z : felem s = sub i (nlimb s) (nlimb s) in
  let tmp = create_felem s in
  let u64s = create 4ul (u64 0) in
  finv #s tmp z;
  fmul #s tmp tmp x;
  store_felem u64s tmp;
  uints_to_bytes_le #U64 4ul o u64s;
  pop_frame()

(* WRAPPER to Prevent Inlining *)
let encode_point_51 o (i:point51) = encode_point_ #M51 o i
let encode_point_64 o (i:point64) = encode_point_ #M64 o i
inline_for_extraction
val encode_point: #s:field_spec -> o:lbuffer uint8 32ul -> i:point s  -> Stack unit 
				  (requires fun h0 -> live h0 o /\ live h0 i /\ disjoint o i)
				 (ensures fun h0 _ h1 -> modifies (loc o) h0 h1)
let encode_point #s o i = 
  match s with
  | M51 -> encode_point_51 o i
  | M64 -> encode_point_64 o i
(* WRAPPER to Prevent Inlining *)


inline_for_extraction
val point_add_and_double_: #s:field_spec -> q:point s -> nq: point s -> nq_p1:point s -> Stack unit
				(requires fun h0 -> live h0 q /\ live h0 nq /\ live h0 nq_p1)
				(ensures fun h0 _ h1 -> modifies (loc nq |+| loc nq_p1) h0 h1)
inline_for_extraction
let point_add_and_double_ #s q nq nq_p1 =
   push_frame();
   let x1 = sub q 0ul (nlimb s) in
   let z1 = sub q (nlimb s) (nlimb s) in
   let x2 = sub nq 0ul (nlimb s) in
   let z2 = sub nq (nlimb s) (nlimb s) in
   let x3 = sub nq_p1 0ul (nlimb s) in
   let z3 = sub nq_p1 (nlimb s) (nlimb s) in
   let tmp : lbuffer (limb s) (4ul *. nlimb s) = create (4ul *. nlimb s) (limb_zero s) in
   let a : felem s = sub tmp 0ul (nlimb s) in
   let b : felem s = sub tmp (nlimb s) (nlimb s) in
   let c : felem s = sub tmp (2ul *. nlimb s) (nlimb s) in
   let d : felem s = sub tmp (3ul *. nlimb s) (nlimb s) in
   let gloc = Ghost.hide (loc nq |+| loc nq_p1 |+| loc tmp) in
   let h0 = ST.get() in
   footprint h0 gloc (fun () -> fadd a x2 z2); // a = x2 + z2
   footprint h0 gloc (fun () -> fsub b x2 z2); // b = x2 - z2
   footprint h0 gloc (fun () -> fadd c x3 z3); // c = x3 + z3
   footprint h0 gloc (fun () -> fsub d x3 z3); // d = x3 - z3

   (* CAN RUN IN PARALLEL *)
   footprint h0 gloc (fun () -> fmul d d a);   // d = da = d * a 
   footprint h0 gloc (fun () -> fmul c c b);   // c = cb = c * b
//   footprint h0 gloc (fun () -> fmul2 d c d a c b);   // c = cb = c * b
   
   footprint h0 gloc (fun () -> fadd x3 d c);  // x3 = da + cb
   footprint h0 gloc (fun () -> fsub z3 d c);  // z3 = da - cb

   (* CAN RUN IN PARALLEL *)
   footprint h0 gloc (fun () -> fsqr x3 x3);   // x3 = (da + cb) ^ 2
   footprint h0 gloc (fun () -> fsqr z3 z3);   // z3 = (da - cb) ^ 2
//   footprint h0 gloc (fun () -> fsqr2 x3 z3 x3 z3);   // z3 = (da - cb) ^ 2
   
   footprint h0 gloc (fun () -> fmul z3 z3 x1); // z3 = x1 * (da - cb) ^ 2

   (* CAN RUN IN PARALLEL *)
   footprint h0 gloc (fun () -> fsqr c a);     // c = aa = a^2
   footprint h0 gloc (fun () -> fsqr d b);     // d = bb = b^2
//   footprint h0 gloc (fun () -> fsqr2 c d a b);     // d = bb = b^2
   
   footprint h0 gloc (fun () -> fmul x2 c d);  // x2 = aa * bb
   footprint h0 gloc (fun () -> fsub b c d);   // b = e = aa - bb
   footprint h0 gloc (fun () -> fmul1 a b (u64 121665)); // a = e * 121665
   footprint h0 gloc (fun () -> fadd a a c);   // a = (e * 121665) + aa 
   footprint h0 gloc (fun () -> fmul z2 b a);  // z2 = e * (aa + (e * 121665))
   pop_frame()

(* WRAPPER to Prevent Inlining *)
let point_add_and_double_51  (q:point51) (nq:point51) (nq_p1:point51) = point_add_and_double_ #M51 q nq nq_p1
let point_add_and_double_64  (q:point64) (nq:point64) (nq_p1:point64) = point_add_and_double_ #M64 q nq nq_p1
inline_for_extraction
val point_add_and_double: #s:field_spec -> q:point s -> nq: point s -> nq_p1:point s -> Stack unit
				(requires fun h0 -> live h0 q /\ live h0 nq /\ live h0 nq_p1)
				(ensures fun h0 _ h1 -> modifies (loc nq |+| loc nq_p1) h0 h1)
inline_for_extraction
let point_add_and_double #s q nq nq_p1 =
  match s with
  | M51 -> point_add_and_double_51 q nq nq_p1
  | M64 -> point_add_and_double_64 q nq nq_p1
(* WRAPPER to Prevent Inlining *)


inline_for_extraction
val cswap_: #s:field_spec -> bit:uint64 -> p1:point s -> p2:point s -> Stack unit
			 (requires (fun h0 -> live h0 p1 /\ live h0 p2))
			 (ensures (fun h0 _ h1 -> modifies (loc p1 |+| loc p2) h0 h1))
inline_for_extraction
let cswap_ #s bit p0 p1 = 
    let mask = u64 0 -. bit in
    let h0 = ST.get() in
    loop2 h0 (2ul *. nlimb s) p0 p1
    (fun h -> (fun i s -> s))
    (fun i -> 
         let dummy = mask &. (p0.(i) ^. p1.(i)) in
         p0.(i) <- p0.(i) ^. dummy;
         p1.(i) <- p1.(i) ^. dummy;
	 admit())


(* WRAPPER to Prevent Inlining *)
[@CInline]
let cswap_51 bit (p0:point51) (p1:point51) = cswap_ #M51 bit p0 p1
[@CInline]
let cswap_64 bit (p0:point64) (p1:point64) = cswap_ #M64 bit p0 p1
inline_for_extraction
val cswap: #s:field_spec -> bit:uint64 -> p1:point s -> p2:point s -> Stack unit
			 (requires (fun h0 -> live h0 p1 /\ live h0 p2))
			 (ensures (fun h0 _ h1 -> modifies (loc p1 |+| loc p2) h0 h1))
let cswap #s bit p0 p1 =
  match s with
  | M51 -> cswap_51 bit p0 p1
  | M64 -> cswap_64 bit p0 p1
(* WRAPPER to Prevent Inlining *)


inline_for_extraction
val montgomery_ladder_: #s:field_spec -> o:point s -> k:scalar -> i:point s -> Stack unit
			  (requires (fun h0 -> live h0 o /\ live h0 k /\ live h0 i))
			  (ensures (fun h0 _ h1 -> modifies (loc o) h0 h1))

inline_for_extraction
let montgomery_ladder_ #s out key init = 
  push_frame();
  let p0 : point s = create (2ul *. nlimb s) (limb_zero s) in
  let p1 : point s = create (2ul *. nlimb s) (limb_zero s) in
  copy p1 init;
  let x0 : felem s = sub p0 0ul (nlimb s) in
  let z0 : felem s = sub p0 (nlimb s) (nlimb s) in
  set_bit1 x0 0ul;
  let h0 = ST.get() in
  loop2 h0 256ul p0 p1
    (fun h -> (fun i s -> s))
    (fun i -> 
         let bit = scalar_bit key (255ul -. i) in
         cswap #s bit p0 p1;   
         point_add_and_double #s init p0 p1;
         cswap #s bit p0 p1;   
	 admit());
  copy out p0;  
  pop_frame()

(* WRAPPER to Prevent Inlining *)
let montgomery_ladder_51 (out:point51) key (init:point51) = montgomery_ladder_ #M51 out key init
let montgomery_ladder_64 (out:point64) key (init:point64) = montgomery_ladder_ #M64 out key init
inline_for_extraction
val montgomery_ladder: #s:field_spec -> o:point s -> k:scalar -> i:point s -> Stack unit
			  (requires (fun h0 -> live h0 o /\ live h0 k /\ live h0 i))
			  (ensures (fun h0 _ h1 -> modifies (loc o) h0 h1))
let montgomery_ladder #s out key init =
  match s with
  | M51 -> montgomery_ladder_51 out key init
  | M64 -> montgomery_ladder_64 out key init
(* WRAPPER to Prevent Inlining *)

inline_for_extraction
val scalarmult: #s:field_spec 
    -> o:lbuffer uint8 32ul 
    -> k:lbuffer uint8 32ul 
    -> i:lbuffer uint8 32ul ->
    Stack unit
    (requires (fun h0 -> live h0 o /\ live h0 k /\ live h0 i))
    (ensures (fun h0 _ h1 -> modifies (loc o) h0 h1))

inline_for_extraction
let scalarmult #s out priv pub = 
    push_frame ();
    let scalar = create 4ul (u64 0) in
    decode_scalar scalar priv;
    let init = create (2ul *. nlimb s) (limb_zero s) in
    decode_point #s init pub;
    montgomery_ladder #s init scalar init;
    encode_point #s out init;
    pop_frame()

inline_for_extraction noextract
let l : List.Tot.llist byte_t 32 = 
  [@inline_let]
  let l_ = [9uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy;
	    0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy;
	    0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy;
	    0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy] in
  assert_norm (List.Tot.length l_ == 32);
  l_

let g25519 : x:ilbuffer byte_t 32ul{recallable x /\ witnessed x (Seq.of_list l)}= 
  [@inline_let]
  let l_ = [9uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy;
	    0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy;
	    0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy;
	    0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy] in
  assert_norm (List.Tot.length l_ == 32);
  createL_global l

inline_for_extraction
val secret_to_public: #s:field_spec 
    -> o:lbuffer uint8 32ul 
    -> i:lbuffer uint8 32ul ->
    Stack unit
    (requires (fun h0 -> live h0 o /\ live h0 i))
    (ensures (fun h0 _ h1 -> modifies (loc o) h0 h1))
inline_for_extraction
let secret_to_public #s pub priv = 
  push_frame ();
  recall_contents g25519 (Seq.of_list l);
  let basepoint = create 32ul (u8 0) in
  mapT 32ul basepoint secret g25519; 
  scalarmult #s pub priv basepoint;
  pop_frame()

