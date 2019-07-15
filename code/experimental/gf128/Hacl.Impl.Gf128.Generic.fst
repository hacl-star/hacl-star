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


#set-options "--z3rlimit 50 --max_fuel 0"

inline_for_extraction noextract
let gcm_ctx (s:field_spec) = lbuffer (elem_t s) (felem_len s +! precomp_len s)

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
  (requires fun h -> live h x /\ live h y)
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
  (requires fun h -> live h x /\ live h y)
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
  (requires fun h -> live h x /\ live h y)
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
  (requires fun h -> live h x /\ live h r /\ live h acc)
  (ensures  fun h0 _ h1 -> modifies1 acc h0 h1 /\
    feval h1 acc == S.gf128_update1 (feval h0 r) (as_seq h0 x) (feval h0 acc))

let gf128_update1 #s acc x r =
  push_frame();
  let elem = create_felem s in
  encode elem x;
  fadd acc elem;
  fmul acc r;
  pop_frame(); admit()

(*
let gf128_update1 (r:elem) (b:lbytes size_block) (acc:elem) : Tot elem =
(encode b `fadd` acc) `fmul_be` r
*)

inline_for_extraction
val gf128_update_last:
    #s:field_spec
  -> acc:felem s
  -> len:size_t{v len < 16}
  -> x:lbuffer uint8 len
  -> r:felem s ->
  Stack unit
  (requires fun h -> live h x /\ live h r /\ live h acc)
  (ensures  fun h0 _ h1 -> modifies1 acc h0 h1 /\
    feval h1 acc == S.gf128_update_last (feval h0 r) (v len) (as_seq h0 x) (feval h0 acc))

let gf128_update_last #s acc l x r =
  push_frame();
  let elem = create_felem s in
  encode_last elem l x;
  fadd acc elem;
  fmul acc r;
  pop_frame(); admit()

(*
let gf128_update_last (r:elem) (l:size_nat{l < size_block}) (b:lbytes l) (acc:elem) =
  if l = 0 then acc else (encode_last l b `fadd` acc) `fmul_be` r
*)

inline_for_extraction
val gf128_update_scalar:
    #s:field_spec
  -> acc:felem s
  -> r:felem s
  -> len:size_t
  -> text:lbuffer uint8 len ->
  Stack unit
  (requires fun h -> live h acc /\ live h r /\ live h text)
  (ensures  fun h0 _ h1 -> modifies1 acc h0 h1 /\
    feval h1 acc == S.gf128_update (as_seq h0 text) (feval h0 acc) (feval h0 r))

let gf128_update_scalar #s acc r len text =
  let blocks = len /. size 16 in
  let h2 = ST.get() in

  loop_nospec #h2 blocks acc
  (fun i ->
    let tb = sub text (i *. size 16) (size 16) in
    gf128_update1 #s acc tb r);

  let rem = len %. size 16 in
  if (rem >. size 0) then (
    let last = sub text (blocks *. size 16) rem in
    gf128_update_last #s acc rem last r); admit()

//NI
inline_for_extraction
val gf128_update_multi_add_mul:
    #s:field_spec
  -> acc:felem s
  -> pre:precomp s
  -> len:size_t{0 < v len /\ v len % 64 = 0}
  -> text:lbuffer uint8 len ->
  Stack unit
  (requires fun h -> live h acc /\ live h pre /\ live h text)
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
  (requires fun h -> live h acc /\ live h pre /\ live h text)
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
  (requires fun h -> live h acc /\ live h pre /\ live h text)
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
  (requires fun h -> live h acc /\ live h pre /\ live h text)
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


inline_for_extraction
val gcm_init:
    #s:field_spec
  -> ctx:gcm_ctx s
  -> key:block ->
  Stack unit
  (requires fun h -> live h ctx /\ live h key /\ disjoint ctx key)
  (ensures  fun h0 _ h1 -> modifies1 ctx h0 h1)

let gcm_init #s ctx key =
  let acc = get_acc ctx in
  let pre = get_precomp ctx in

  felem_set_zero acc;
  load_precompute_r pre key


inline_for_extraction
val ghash:
    #s:field_spec
  -> tag:block
  -> len:size_t
  -> text:lbuffer uint8 len
  -> key:block ->
  Stack unit
  (requires fun h -> live h tag /\ live h text /\ live h key)
  (ensures  fun h0 _ h1 -> modifies1 tag h0 h1)

let ghash #s tag len text key =
  push_frame();
  let ctx : gcm_ctx s = create (felem_len s +! precomp_len s) (elem_zero s) in
  gcm_init ctx key;
  let acc = get_acc ctx in
  let pre = get_precomp ctx in
  gf128_update_vec acc pre len text;
  decode tag acc;
  pop_frame()
