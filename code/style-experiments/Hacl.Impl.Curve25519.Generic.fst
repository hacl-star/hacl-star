module Hacl.Impl.Curve25519.Generic
module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer
open Hacl.Impl.Curve25519.Fields

#set-options "--z3rlimit 50 --max_fuel 2 --max_ifuel 2"

val fsquare_times: #s:field_spec -> o:felem s -> i:felem s -> n:size_t{v n > 0} -> Stack unit
	     (requires (fun h0 -> live h0 o /\ live h0 i))
	     (ensures (fun h0 _ h1 -> modifies (loc o) h0 h1 /\ live h1 o /\ live h1 i))
let fsquare_times #s o i n = 
    fsqr #s o i;
    let h0 = ST.get() in
    loop_nospec #h0 (n -! 1ul) o
    (fun i -> fsqr o o)

let live_modifies (#a:Type0) (#len:size_t) (b0:lbuffer a len) (b1:lbuffer a len) (b2:lbuffer a len) (b3:lbuffer a len) (h0:mem) = 
		   let h = ST.get() in
		   cut (modifies (loc b0 |+| loc b1 |+| loc b2 |+| loc b3) h0 h /\  live h b0 /\ live h b1 /\ live h b2 /\ live h b3)

val footprint: h0:mem ->
	     l:Ghost.erased LowStar.Buffer.loc -> 
	     impl: (unit -> Stack unit
			   (requires (fun h -> modifies (Ghost.reveal l) h0 h))
			   (ensures (fun h _ h' -> modifies (Ghost.reveal l) h h'))) ->
	     Stack unit
	      (requires (fun h -> modifies (Ghost.reveal l) h0 h))
	      (ensures (fun _ _ h -> modifies (Ghost.reveal l) h0 h))
let footprint h0 l impl = impl()
	      
val finv: #s:field_spec -> o:felem s -> i:felem s -> Stack unit
	     (requires (fun h0 -> live h0 o /\ live h0 i))
	     (ensures (fun h0 _ h1 -> modifies (loc o) h0 h1))
let finv #s o i = 
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



assume val uint64s_from_bytes_le: #len:size_t -> o:lbuffer uint64 len -> i:lbuffer uint8 (len *. 8ul) -> Stack unit
					     (requires (fun h0 -> live h0 o /\ live h0 i))
					     (ensures (fun h0 _ h1 -> modifies (loc o) h0 h1))

assume val uint64s_to_bytes_le: #len:size_t -> o:lbuffer uint8 (len *. 8ul) -> i:lbuffer uint64 len -> Stack unit
					     (requires (fun h0 -> live h0 o /\ live h0 i))
					     (ensures (fun h0 _ h1 -> modifies (loc o) h0 h1))

let scalar = lbuffer uint64 4ul
let point (s:field_spec) = lbuffer (limb s) (2ul *. nlimb s)

val decode_scalar: #s:field_spec -> o:scalar -> i:lbuffer uint8 32ul -> Stack unit
				 (requires fun h0 -> live h0 o /\ live h0 i /\ disjoint o i)
				 (ensures fun h0 _ h1 -> modifies (loc o) h0 h1)
let decode_scalar #s o i = 
  uint64s_from_bytes_le o i;
  o.(0ul) <- o.(0ul) &. u64 0xfffffffffffffff8;
  o.(3ul) <- o.(3ul) &. u64 0x7fffffffffffffff;
  o.(3ul) <- o.(3ul) |. u64 0x40ffffffffffffff

val decode_point: #s:field_spec -> o:point s -> i:lbuffer uint8 32ul -> Stack unit 
				  (requires fun h0 -> live h0 o /\ live h0 i /\ disjoint o i)
				 (ensures fun h0 _ h1 -> modifies (loc o) h0 h1)

let decode_point #s o i = 
  push_frame();
  let tmp = create 4ul (u64 0) in
  uint64s_from_bytes_le tmp i;
  tmp.(3ul) <- tmp.(3ul) &. u64 0x7fffffffffffffff;
  let x : felem s = sub o 0ul (nlimb s) in
  let z : felem s = sub o (nlimb s) (nlimb s) in
  set_zero z;
  set_bit1 z 0ul;
  load_felem x tmp;
  pop_frame()

val encode_point: #s:field_spec -> o:lbuffer uint8 32ul -> i:point s  -> Stack unit 
				  (requires fun h0 -> live h0 o /\ live h0 i /\ disjoint o i)
				 (ensures fun h0 _ h1 -> modifies (loc o) h0 h1)

let encode_point #s o i = 
  push_frame();
  let x : felem s = sub i 0ul (nlimb s) in
  let z : felem s = sub i (nlimb s) (nlimb s) in
  let tmp = create_felem s in
  let u64s = create 4ul (u64 0) in
  finv #s tmp z;
  fmul #s tmp tmp x;
  store_felem u64s tmp;
  uint64s_to_bytes_le o u64s;
  pop_frame()

val point_add_and_double: #s:field_spec -> q:point s -> nq: point s -> nq_p1:point s -> Stack unit
				(requires fun h0 -> live h0 q /\ live h0 nq /\ live h0 nq_p1)
				(ensures fun h0 _ h1 -> modifies (loc nq |+| loc nq_p1) h0 h1)

let point_add_and_double #s q nq nq_p1 =
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
   footprint h0 gloc (fun () -> fmul d d a);   // d = da = d * a 
   footprint h0 gloc (fun () -> fmul c c b);   // c = cb = c * b
   footprint h0 gloc (fun () -> fadd x3 d c);  // x3 = da + cb
   footprint h0 gloc (fun () -> fsqr x3 x3);   // x3 = (da + cb) ^ 2
   footprint h0 gloc (fun () -> fsub z3 d c);  // z3 = da - cb
   footprint h0 gloc (fun () -> fsqr z3 z3);   // z3 = (da - cb) ^ 2
   footprint h0 gloc (fun () -> fmul z3 z3 x1); // z3 = x1 * (da - cb) ^ 2
   footprint h0 gloc (fun () -> fsqr c a);     // c = aa = a^2
   footprint h0 gloc (fun () -> fsqr d b);     // d = bb = b^2
   footprint h0 gloc (fun () -> fmul x2 c d);  // x2 = aa * bb
   footprint h0 gloc (fun () -> fsub b c d);   // b = e = aa - bb
   footprint h0 gloc (fun () -> fmul1 a b (u64 121665)); // a = e * 121665
   footprint h0 gloc (fun () -> fadd a a c);   // a = (e * 121665) + aa 
   footprint h0 gloc (fun () -> fmul z2 b a);  // z2 = e * (aa + (e * 121665))
   pop_frame()
