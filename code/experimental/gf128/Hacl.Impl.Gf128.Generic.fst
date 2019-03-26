module Hacl.Impl.Gf128.Generic

open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer
open Hacl.Impl.Gf128.Fields

module ST = FStar.HyperStack.ST


#set-options "--z3rlimit 50 --max_fuel 0"

inline_for_extraction
val encode:
    #s: field_spec
  -> x: felem s
  -> y:block ->
  Stack unit
  (requires (fun h -> live h x /\ live h y))
  (ensures (fun h0 _ h1 -> modifies1 x h0 h1))

let encode #s x y = load_felem x y


inline_for_extraction
val encode4:
    #s: field_spec
  -> x: felem4 s
  -> y: block4 ->
  Stack unit
  (requires (fun h -> live h x /\ live h y))
  (ensures (fun h0 _ h1 -> modifies1 x h0 h1))

let encode4 #s x y = load_felem4 x y


inline_for_extraction
val decode:
    #s: field_spec
  -> y: block
  -> x: felem s ->
  Stack unit
  (requires (fun h -> live h x /\ live h y))
  (ensures (fun h0 _ h1 -> modifies1 y h0 h1))

let decode #s y x = store_felem y x


inline_for_extraction
val encode_last:
    #s: field_spec
  -> x: felem s
  -> len: size_t{v len < 16}
  -> y: lbuffer uint8 len ->
  Stack unit
  (requires (fun h -> live h x /\ live h y))
  (ensures (fun h0 _ h1 -> modifies1 x h0 h1))

let encode_last #s x len y =
  push_frame();
  let b = create 16ul (u8 0) in
  copy (sub b 0ul len) y;
  encode x b;
  pop_frame()


inline_for_extraction
val update:
    #s: field_spec
  -> acc: felem s
  -> x: block
  -> r: felem s ->
  Stack unit
  (requires (fun h -> live h x /\ live h r /\ live h acc))
  (ensures (fun h0 _ h1 -> modifies1 acc h0 h1))

inline_for_extraction
let update #s acc x r =
  push_frame();
  let elem = create_felem s in
  encode elem x;
  fadd acc elem;
  fmul acc r;
  pop_frame()


inline_for_extraction
val update_last:
    #s: field_spec
  -> acc: felem s
  -> len: size_t{v len < 16}
  -> x: lbuffer uint8 len
  -> r: felem s ->
  Stack unit
  (requires (fun h -> live h x /\ live h r /\ live h acc))
  (ensures (fun h0 _ h1 -> modifies1 acc h0 h1))

inline_for_extraction
let update_last #s acc l x r =
  push_frame();
  let elem = create_felem s in
  encode_last elem l x;
  fadd acc elem;
  fmul acc r;
  pop_frame()


inline_for_extraction
val poly:
    #s: field_spec
  -> ctx: gcm_ctx s
  -> len: size_t
  -> text: lbuffer uint8 len ->
  Stack unit
  (requires (fun h -> live h ctx /\ live h text))
  (ensures (fun h0 _ h1 -> modifies1 ctx h0 h1))

let poly #s ctx len text =
  let acc = get_acc ctx in
  let r = get_r ctx in
  let blocks = len /. size 16 in
  let h2 = ST.get() in
  loop_nospec #h2 blocks acc (fun i ->
    update #s acc (sub text (i *. size 16) (size 16)) r);
  let rem = len %. size 16 in
  if (rem >. size 0) then (
    let last = sub text (blocks *. size 16) rem in
    update_last #s acc rem last r)


inline_for_extraction
val poly_pre:
    #s: field_spec
  -> ctx: gcm_ctx s
  -> len: size_t
  -> text: lbuffer uint8 len ->
  Stack unit
  (requires (fun h -> live h ctx /\ live h text))
  (ensures (fun h0 _ h1 -> modifies1 ctx h0 h1))

let poly_pre #s ctx len text =
  push_frame ();
  let acc = get_acc ctx in
  let pre = get_precomp ctx in
  let b = create_felem s in
  let blocks = len /. size 16 in
  let h0 = ST.get() in
  loop_nospec2 #h0 blocks acc b (fun i ->
    encode b (sub text (i *. size 16) (size 16));
    fadd acc b;
    fmul_pre acc pre);
  let rem = len %. size 16 in
  if (rem >. size 0) then (
    let last = sub text (blocks *. size 16) rem in
    encode_last b rem last;
    fadd acc b;
    fmul_pre acc pre);
  pop_frame()


inline_for_extraction
val poly4_add_mul:
    #s: field_spec
  -> ctx: gcm_ctx s
  -> len: size_t
  -> text: lbuffer uint8 len ->
  Stack unit
  (requires (fun h -> live h ctx /\ live h text))
  (ensures (fun h0 _ h1 -> modifies1 ctx h0 h1))

let poly4_add_mul #s ctx len text =
  push_frame ();
  let acc = get_acc ctx in
  let pre = get_precomp ctx in
  let b4 = create_felem4 s in
  let blocks = len /. size 64 in
  let h0 = ST.get() in
  loop_nospec2 #h0 blocks acc b4
    (fun i -> encode4 b4 (sub text (i *. size 64) (size 64));
           fadd_mul4 acc b4 pre );
  let rem = len %. size 64 in
  let last = sub text (blocks *. size 64) rem in
  poly #s ctx rem last;
  pop_frame()


#set-options "--z3rlimit 1000 --max_fuel 1"

inline_for_extraction
val poly4_mul_add:
    #s: field_spec
  -> ctx: gcm_ctx s
  -> len: size_t
  -> text: lbuffer uint8 len ->
  Stack unit
  (requires (fun h -> live h ctx /\ live h text /\ s == F32))
  (ensures (fun h0 _ h1 -> modifies1 ctx h0 h1))

let poly4_mul_add #s ctx len text =
  let h0 = ST.get () in
  push_frame ();
  let h1 = ST.get () in
  let b4 = create_felem4 s in
  let acc4 = create_felem4 s in
  let h2 = ST.get () in
  let acc = get_acc ctx in
  let pre = get_precomp ctx in
  copy (sub acc4 0ul (felem_len s)) acc;
  let h3 = ST.get () in
  assert(modifies1 acc4 h2 h3);
  let blocks = len /. size 64 in
  if (blocks >. 0ul) then (
    let h4 = ST.get () in
    encode4 b4 (sub text (size 0) (size 64));
    fadd4 acc4 b4;
    let h5 = ST.get() in
    loop_nospec2 #h5 (blocks -. 1ul) b4 acc4 (fun i ->
      encode4 b4 (sub text ((i +. size 1) *. size 64) (size 64));
      fmul4 acc4 pre;
	   fadd4 acc4 b4);
    let r4 = sub pre 0ul 2ul in
    let r3 = sub pre 2ul 2ul in
    let r2 = sub pre 4ul 2ul in
    let r = sub pre 6ul 2ul in
    let acc0 = sub acc4 0ul 2ul in
    let acc1 = sub acc4 2ul 2ul in
    let acc2 = sub acc4 4ul 2ul in
    let acc3 = sub acc4 6ul 2ul in
    fmul acc0 r4;
    fmul acc1 r3;
    fmul acc2 r2;
    fmul acc3 r;
    copy acc acc0;
    fadd acc acc1;
    fadd acc acc2;
    fadd acc acc3;
    let h10 = ST.get() in
    assert(modifies3 acc b4 acc4 h3 h10)
  )
  else (
    let h11 = ST.get () in
    modifies1_is_modifies3 acc b4 acc4 h3 h11
  );
  let rem = len %. size 64 in
  let last = sub text (blocks *. size 64) rem in
  poly #s ctx rem last;
  let h13 = ST.get () in
  assert(modifies3 ctx b4 acc4 h2 h13);
  pop_frame();
  let h14 = ST.get () in
  assert(modifies1 ctx h0 h14)


inline_for_extraction
val gcm_init:
    #s: field_spec
  -> ctx: gcm_ctx s
  -> key: block ->
  Stack unit
  (requires (fun h -> live h ctx /\ live h key))
  (ensures (fun h0 _ h1 -> modifies1 ctx h0 h1))

let gcm_init #s ctx key =
  let acc = get_acc ctx in
  let pre = get_precomp ctx in
  felem_set_zero acc;
  load_precompute_r pre key


inline_for_extraction
val ghash_add_mul:
    #s: field_spec
  -> tag: block
  -> len: size_t
  -> text: lbuffer uint8 len
  -> key: block ->
  Stack unit
  (requires (fun h -> live h tag /\ live h text /\ live h key))
  (ensures (fun h0 _ h1 -> modifies1 tag h0 h1))

let ghash_add_mul #s tag len text key =
  push_frame();
  let ctx = create_ctx s in
  gcm_init ctx key;
  poly4_add_mul ctx len text;
  let acc = get_acc ctx in
  decode tag acc;
  pop_frame()


inline_for_extraction
val ghash_mul_add:
    #s: field_spec
  -> tag: block
  -> len: size_t
  -> text: lbuffer uint8 len
  -> key: block ->
  Stack unit
  (requires (fun h -> s == F32 /\ live h tag /\ live h text /\ live h key))
  (ensures (fun h0 _ h1 -> modifies1 tag h0 h1))

let ghash_mul_add #s tag len text key =
  push_frame();
  let ctx = create_ctx s in
  gcm_init ctx key;
  poly4_mul_add ctx len text;
//  poly_pre ctx len text;
  let acc = get_acc ctx in
  decode tag acc;
  pop_frame()
