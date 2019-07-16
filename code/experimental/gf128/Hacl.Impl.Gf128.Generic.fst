module Hacl.Impl.Gf128.Generic

open FStar.HyperStack
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Gf128.Fields

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence

module S = Spec.GF128
module GF = Spec.GaloisField
module Vec = Hacl.Spec.GF128.Vec

friend Lib.LoopCombinators


#set-options "--z3rlimit 50 --max_fuel 0"


let as_get_acc #s h ctx = feval h (gsub ctx 0ul (felem_len s))

let as_get_r #s h ctx = feval h (gsub ctx (felem4_len s) (felem_len s))

inline_for_extraction noextract
let get_acc #s (ctx:gcm_ctx s) = sub ctx 0ul (felem_len s)

inline_for_extraction noextract
let get_r #s (ctx:gcm_ctx s) = sub ctx (felem4_len s) (felem_len s)

inline_for_extraction noextract
let get_precomp #s (ctx:gcm_ctx s) = sub ctx (felem_len s) (precomp_len s)


inline_for_extraction
val encode:
    #s:field_spec
  -> x:felem s
  -> y:block ->
  Stack unit
  (requires fun h -> live h x /\ live h y /\ disjoint x y)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    feval h1 x == S.encode (as_seq h0 y))

let encode #s x y = load_felem x y


inline_for_extraction
val encode4:
    #s:field_spec
  -> x:felem4 s
  -> y:block4 ->
  Stack unit
  (requires fun h -> live h x /\ live h y /\ disjoint x y)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    feval4 h1 x == Vec.encode4 (as_seq h0 y))

let encode4 #s x y = load_felem4 x y


inline_for_extraction
val decode:
    #s:field_spec
  -> x:block
  -> y:felem s ->
  Stack unit
  (requires fun h -> live h x /\ live h y /\ disjoint x y)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    as_seq h1 x == S.decode (feval #s h0 y))

let decode #s x y = store_felem x y


inline_for_extraction
val encode_last:
    #s:field_spec
  -> x:felem s
  -> len:size_t{v len < 16}
  -> y:lbuffer uint8 len ->
  Stack unit
  (requires fun h -> live h x /\ live h y /\ disjoint x y)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    feval h1 x == S.encode_last (v len) (as_seq h0 y))

let encode_last #s x len y =
  push_frame();
  let b = create 16ul (u8 0) in
  update_sub b 0ul len y;
  encode x b;
  pop_frame()


inline_for_extraction
val gf128_update1:
    #s:field_spec
  -> acc:felem s
  -> x:block
  -> r:felem s ->
  Stack unit
  (requires fun h ->
    live h x /\ live h r /\ live h acc /\
    disjoint acc r /\ disjoint acc x)
  (ensures  fun h0 _ h1 -> modifies1 acc h0 h1 /\
    feval h1 acc == S.gf128_update1 (feval h0 r) (as_seq h0 x) (feval h0 acc))

let gf128_update1 #s acc x r =
  push_frame();
  let elem = create_felem s in
  encode elem x;
  fadd acc elem;
  fmul acc r;
  pop_frame()


inline_for_extraction
val gf128_update_last:
    #s:field_spec
  -> acc:felem s
  -> len:size_t{0 < v len /\ v len < 16}
  -> x:lbuffer uint8 len
  -> r:felem s ->
  Stack unit
  (requires fun h ->
    live h x /\ live h r /\ live h acc /\
    disjoint acc x /\ disjoint acc r)
  (ensures  fun h0 _ h1 -> modifies1 acc h0 h1 /\
    feval h1 acc == S.gf128_update_last (feval h0 r) (v len) (as_seq h0 x) (feval h0 acc))

let gf128_update_last #s acc len x r =
  push_frame();
  let elem = create_felem s in
  encode_last elem len x;
  fadd acc elem;
  fmul acc r;
  pop_frame()

inline_for_extraction noextract
val gf128_update_scalar_f:
    #s:field_spec
  -> r:felem s
  -> nb:size_t
  -> len:size_t{v nb == v len / 16}
  -> text:lbuffer uint8 len
  -> i:size_t{v i < v nb}
  -> acc:felem s ->
  Stack unit
  (requires fun h ->
    live h r /\ live h acc /\ live h text /\
    disjoint acc r /\ disjoint acc text)
  (ensures  fun h0 _ h1 -> modifies1 acc h0 h1 /\
    feval h1 acc == LSeq.repeat_blocks_f #uint8 #S.elem 16 (as_seq h0 text)
      (S.gf128_update1 (feval h0 r)) (v nb) (v i) (feval h0 acc))

let gf128_update_scalar_f #s r nb len text i acc =
  let tb = sub text (i *. 16ul) 16ul in
  gf128_update1 #s acc tb r


#set-options "--max_fuel 1"

inline_for_extraction
val gf128_update_scalar:
    #s:field_spec
  -> acc:felem s
  -> r:felem s
  -> len:size_t
  -> text:lbuffer uint8 len ->
  Stack unit
  (requires fun h ->
    live h acc /\ live h r /\ live h text /\
    disjoint acc r /\ disjoint acc text)
  (ensures  fun h0 _ h1 -> modifies1 acc h0 h1 /\
    feval h1 acc == S.gf128_update (as_seq h0 text) (feval h0 acc) (feval h0 r))

let gf128_update_scalar #s acc r len text =
  let nb = len /. 16ul in
  let rem = len %. 16ul in
  let h0 = ST.get () in

  LSeq.lemma_repeat_blocks #uint8 #S.elem 16 (as_seq h0 text)
  (S.gf128_update1 (feval h0 r))
  (S.gf128_update_last (feval h0 r))
  (feval h0 acc);

  [@ inline_let]
  let spec_fh h0 =
    LSeq.repeat_blocks_f 16 (as_seq h0 text)
      (S.gf128_update1 (feval h0 r)) (v nb) in

  [@ inline_let]
  let inv h (i:nat{i <= v nb}) =
    modifies1 acc h0 h /\
    live h acc /\ live h r /\ live h text /\
    disjoint acc r /\ disjoint acc text /\
    feval h acc == Lib.LoopCombinators.repeati i (spec_fh h0) (feval h0 acc) in

  Lib.Loops.for (size 0) nb inv
  (fun i ->
    Lib.LoopCombinators.unfold_repeati (v nb) (spec_fh h0) (feval h0 acc) (v i);
    gf128_update_scalar_f #s r nb len text i acc);

  let h1 = ST.get () in
  assert (feval h1 acc == Lib.LoopCombinators.repeati (v nb) (spec_fh h0) (feval h0 acc));

  if rem >. 0ul then (
    let last = sub text (nb *! 16ul) rem in
    as_seq_gsub h1 text (nb *! 16ul) rem;
    assert (disjoint acc last);
    gf128_update_last #s acc rem last r)


//NI
inline_for_extraction
val gf128_update_multi_add_mul:
    #s:field_spec
  -> acc:felem s
  -> pre:precomp s
  -> len:size_t{0 < v len /\ v len % 64 = 0}
  -> text:lbuffer uint8 len ->
  Stack unit
  (requires fun h ->
    live h acc /\ live h pre /\ live h text /\
    disjoint acc pre /\ disjoint acc text)
  (ensures  fun h0 _ h1 -> modifies1 acc h0 h1 /\
    feval h1 acc == Vec.gf128_update_multi_add_mul (as_seq h0 text) (feval h0 acc) (get_r1 h0 pre))

let gf128_update_multi_add_mul #s acc pre len text =
  push_frame ();
  let b4 = create_felem4 s in
  let blocks = len /. size 64 in

  let h0 = ST.get() in
  loop_nospec2 #h0 blocks acc b4
  (fun i ->
    let tb = sub text (i *. size 64) (size 64) in
    encode4 b4 tb;
    normalize4 acc b4 pre);
  pop_frame (); admit()

//PreComp
inline_for_extraction
val gf128_update_multi_mul_add:
    #s:field_spec
  -> acc:felem s
  -> pre:precomp s
  -> len:size_t{0 < v len /\ v len % 64 = 0}
  -> text:lbuffer uint8 len ->
  Stack unit
  (requires fun h ->
    live h acc /\ live h pre /\ live h text /\
    disjoint acc pre /\ disjoint acc text)
  (ensures  fun h0 _ h1 -> modifies1 acc h0 h1 /\
    feval h1 acc == Vec.gf128_update_multi_mul_add (as_seq h0 text) (feval h0 acc) (get_r1 h0 pre))

let gf128_update_multi_mul_add #s acc pre len text =
  push_frame ();
  let b4 = create_felem4 s in
  let acc4 = create_felem4 s in
  copy_felem (sub acc4 0ul (felem_len s)) acc;

  let tb = sub text 0ul 64ul in
  encode4 b4 tb;
  fadd4 acc4 b4;

  let len1 = len -! 64ul in
  let blocks = len1 /. 64ul in
  let text1 = sub text 64ul len1 in
  let h0 = ST.get () in
  loop_nospec2 #h0 blocks b4 acc4
  (fun i ->
    let tb = sub text1 (i *. 64ul) 64ul in
    encode4 b4 tb;
    fmul_r4 acc4 pre;
    fadd4 acc4 b4);
  felem_set_zero acc;
  normalize4 acc acc4 pre;
  pop_frame (); admit()


inline_for_extraction
val gf128_update_multi:
    #s:field_spec
  -> acc:felem s
  -> pre:precomp s
  -> len:size_t{0 < v len /\ v len % 64 = 0}
  -> text:lbuffer uint8 len ->
  Stack unit
  (requires fun h ->
    live h acc /\ live h pre /\ live h text /\
    disjoint acc pre /\ disjoint acc text)
  (ensures  fun h0 _ h1 -> modifies1 acc h0 h1 /\
    feval h1 acc == Vec.gf128_update_multi s (as_seq h0 text) (feval h0 acc) (get_r1 h0 pre))

let gf128_update_multi #s acc pre len text =
  match s with
  | Vec.NI -> gf128_update_multi_add_mul acc pre len text
  | Vec.PreComp -> gf128_update_multi_mul_add acc pre len text


inline_for_extraction
val gf128_update_vec:
    #s:field_spec
  -> acc:felem s
  -> pre:precomp s
  -> len:size_t
  -> text:lbuffer uint8 len ->
  Stack unit
  (requires fun h ->
    live h acc /\ live h pre /\ live h text /\
    disjoint acc pre /\ disjoint acc text)
  (ensures  fun h0 _ h1 -> modifies1 acc h0 h1 /\
    feval h1 acc == Vec.gf128_update_vec s (as_seq h0 text) (feval h0 acc) (get_r1 h0 pre))

let gf128_update_vec #s acc pre len text =
  let len0 = len /. 64ul *. 64ul in
  let t0 = sub text 0ul len0 in
  if (len0 >. 0ul) then gf128_update_multi #s acc pre len0 t0;

  let len1 = len -! len0 in
  let t1 = sub text len0 len1 in
  let r1 = sub pre (3ul *. felem_len s) (felem_len s) in
  gf128_update_scalar #s acc r1 len1 t1; admit()


let gf128_init #s ctx key =
  let acc = get_acc ctx in
  let pre = get_precomp ctx in

  felem_set_zero acc;
  load_precompute_r pre key


let gf128_update #s ctx len text =
  let acc = get_acc ctx in
  let pre = get_precomp ctx in
  let h0 = ST.get () in
  gf128_update_vec #s acc pre len text;
  let h1 = ST.get () in
  assume (as_get_acc h1 ctx == S.gf128_update (as_seq h0 text) (as_get_acc h0 ctx) (as_get_r h0 ctx))


let gf128_emit #s tag ctx =
  let acc = get_acc ctx in
  decode tag acc


let ghash #s tag len text key =
  push_frame();
  let ctx : gcm_ctx s = create (felem_len s +! precomp_len s) (elem_zero s) in
  gf128_init ctx key;
  gf128_update ctx len text;
  gf128_emit tag ctx;
  pop_frame()
