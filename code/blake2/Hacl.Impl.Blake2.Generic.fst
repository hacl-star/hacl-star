module Hacl.Impl.Blake2.Generic

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.LoopCombinators

module ST = FStar.HyperStack.ST
module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators
module Spec = Spec.Blake2

open Hacl.Impl.Blake2.Constants
open Hacl.Impl.Blake2.Core

#set-options "--z3rlimit 50 --max_ifuel 0 --max_fuel 0"

noextract
let is_valid_blake2_config (a : Spec.alg) (m : m_spec) =
  match a, m with
  | Spec.Blake2S, M32 | Spec.Blake2S, M128
  | Spec.Blake2B, M32 | Spec.Blake2B, M256 -> true
  | _ -> false

inline_for_extraction noextract
let valid_m_spec (a : Spec.alg) = m:m_spec{is_valid_blake2_config a m}

/// Accessors for constants

inline_for_extraction noextract
val get_iv:
  a:Spec.alg
  -> s: size_t{size_v s < 8} ->
  Stack (word_t a)
    (requires (fun h -> True))
    (ensures  (fun h0 z h1 -> h0 == h1 /\
      v z == v (Seq.index (Spec.ivTable a) (v s))))

let get_iv a s =
  recall_contents #(Spec.pub_word_t Spec.Blake2S) #8ul ivTable_S (Spec.ivTable Spec.Blake2S);
  recall_contents #(Spec.pub_word_t Spec.Blake2B) #8ul ivTable_B (Spec.ivTable Spec.Blake2B);
  [@inline_let]
  let ivTable: (x:glbuffer (Spec.pub_word_t a) 8ul{witnessed x (Spec.ivTable a) /\ recallable x}) =
    match a with
    | Spec.Blake2S -> ivTable_S
    | Spec.Blake2B -> ivTable_B
  in
  let r = index ivTable s in
  secret #(Spec.wt a) r


inline_for_extraction noextract
val get_sigma:
  s: size_t{v s < 160} ->
  Stack Spec.sigma_elt_t
    (requires (fun h -> True))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ z == Lib.Sequence.(Spec.sigmaTable.[v s])))

let get_sigma s =
  recall_contents sigmaTable Spec.sigmaTable;
  index sigmaTable s


inline_for_extraction noextract
val get_sigma_sub:
  start: size_t ->
  i: size_t{v i < 16 /\ v start + v i < 160} ->
  Stack Spec.sigma_elt_t
    (requires (fun h -> True))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ v z == v (Seq.index Spec.sigmaTable (v start + v i))))

let get_sigma_sub start i = get_sigma (start +. i)

inline_for_extraction noextract
let rounds_t (a:Spec.alg): size_t = size (Spec.rounds a)

inline_for_extraction noextract
val size_to_word: al:Spec.alg -> s:size_t -> u:word_t al{u == Spec.nat_to_word al (v s)}
let size_to_word al s = match al with
  | Spec.Blake2S -> size_to_uint32 s
  | Spec.Blake2B -> size_to_uint64 s

inline_for_extraction noextract
val size_to_limb: al:Spec.alg -> s:size_t -> u:Spec.limb_t al{u == Spec.nat_to_limb al (v s)}
let size_to_limb al s = match al with
  | Spec.Blake2S -> size_to_uint64 s
  | Spec.Blake2B -> to_u128 (size_to_uint64 s)

/// Constants

/// Define algorithm functions

inline_for_extraction noextract
val g1: #al:Spec.alg -> #m:m_spec -> wv:state_p al m -> a:index_t -> b:index_t -> r:rotval (Spec.wt al) ->
  Stack unit
    (requires (fun h -> live h wv /\ a <> b))
    (ensures  (fun h0 _ h1 -> modifies (loc wv) h0 h1
                         /\ (state_v h1 wv) == Spec.g1 al (state_v h0 wv) (v a) (v b) r))

let g1 #al #m wv a b r =
  let h0 = ST.get() in
  let wv_a = rowi wv a in
  let wv_b = rowi wv b in
  xor_row wv_a wv_b;
  ror_row wv_a r;
  let h2 = ST.get() in
  Lib.Sequence.eq_intro (state_v h2 wv) (Spec.g1 al (state_v h0 wv) (v a) (v b) r)


#push-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1"
inline_for_extraction noextract
val g2: #al:Spec.alg -> #m:m_spec -> wv:state_p al m -> a:index_t -> b:index_t -> x:row_p al m ->
  Stack unit
    (requires (fun h -> live h wv /\ live h x /\ disjoint wv x /\ a <> b))
    (ensures  (fun h0 _ h1 -> modifies (loc wv) h0 h1
                         /\ state_v h1 wv == Spec.g2 al (state_v h0 wv) (v a) (v b) (row_v h0 x)))

let g2 #al #m wv a b x =
  let h0 = ST.get() in
  let wv_a = rowi wv a in
  let wv_b = rowi wv b in
  add_row wv_a wv_b;
  add_row wv_a x;
  let h1 = ST.get() in
  Lib.Sequence.eq_intro (state_v  h1 wv) (Spec.g2 al (state_v h0 wv) (v a) (v b) (row_v h0 x))

#push-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1"
inline_for_extraction noextract
val g2z: #al:Spec.alg -> #m:m_spec -> wv:state_p al m -> a:index_t -> b:index_t ->
  Stack unit
    (requires (fun h -> live h wv /\ a <> b))
    (ensures  (fun h0 _ h1 -> modifies (loc wv) h0 h1
                         /\ state_v h1 wv == Spec.g2z al (state_v h0 wv) (v a) (v b)))

let g2z #al #m wv a b =
  let h0 = ST.get() in
  let wv_a = rowi wv a in
  let wv_b = rowi wv b in
  add_row wv_a wv_b;
  let h1 = ST.get() in
  Lib.Sequence.eq_intro (state_v  h1 wv) (Spec.g2z al (state_v h0 wv) (v a) (v b))

inline_for_extraction noextract
val blake2_mixing : #al:Spec.alg -> #m:m_spec -> wv:state_p al m -> x:row_p al m -> y:row_p al m ->
  Stack unit
    (requires (fun h -> live h wv /\ live h x /\ live h y /\ disjoint wv x /\ disjoint wv y))
    (ensures  (fun h0 _ h1 -> modifies (loc wv) h0 h1
                         /\ state_v h1 wv == Spec.blake2_mixing al (state_v h0 wv) (row_v h0 x) (row_v h0 y)))

let blake2_mixing #al #m wv x y =
  let h0 = ST.get() in
  push_frame ();
  let a = 0ul in
  let b = 1ul in
  let c = 2ul in
  let d = 3ul in
  [@inline_let]
  let r0 = normalize_term (Lib.Sequence.index (Spec.rTable al) 0) in
  normalize_term_spec (Lib.Sequence.index (Spec.rTable al) 0);
  [@inline_let]
  let r1 = normalize_term (Lib.Sequence.index (Spec.rTable al) 1) in
  normalize_term_spec (Lib.Sequence.index (Spec.rTable al) 1);
  [@inline_let]
  let r2 = normalize_term (Lib.Sequence.index (Spec.rTable al) 2) in
  normalize_term_spec (Lib.Sequence.index (Spec.rTable al) 2);
  [@inline_let]
  let r3 = normalize_term (Lib.Sequence.index (Spec.rTable al) 3) in
  normalize_term_spec (Lib.Sequence.index (Spec.rTable al) 3);
  let h1 = ST.get() in
  g2 wv a b x;
  g1 wv d a r0;
  g2z wv c d;
  g1 wv b c r1;
  g2 wv a b y;
  g1 wv d a r2;
  g2z wv c d;
  g1 wv b c r3;
  let h2 = ST.get() in
  pop_frame ();
  let h3 = ST.get() in
  assert(modifies (loc wv) h0 h3);
  Lib.Sequence.eq_intro (state_v h2 wv) (Spec.blake2_mixing al (state_v h1 wv) (row_v h1 x) (row_v h1 y))
#pop-options

inline_for_extraction noextract
val diag: #a:Spec.alg -> #m:m_spec -> wv:state_p a m
	  -> Stack unit
	    (requires (fun h -> live h wv))
	    (ensures (fun h0 _ h1 -> modifies (loc wv) h0 h1 /\
				  state_v h1 wv == Spec.diag (state_v h0 wv)))
let diag #a #m wv =
  let r1 = rowi wv 1ul in
  let r2 = rowi wv 2ul in
  let r3 = rowi wv 3ul in
  let h0 = ST.get() in
  permr_row r1 1ul;
  permr_row r2 2ul;
  permr_row r3 3ul


inline_for_extraction noextract
val undiag: #a:Spec.alg -> #m:m_spec -> wv:state_p a m
	  -> Stack unit
	    (requires (fun h -> live h wv))
	    (ensures (fun h0 _ h1 -> modifies (loc wv) h0 h1 /\
				  state_v h1 wv == Spec.undiag (state_v h0 wv)))
let undiag #a #m wv =
  let r1 = rowi wv 1ul in
  let r2 = rowi wv 2ul in
  let r3 = rowi wv 3ul in
  let h0 = ST.get() in
  permr_row r1 3ul;
  permr_row r2 2ul;
  permr_row r3 1ul


inline_for_extraction noextract
val gather_state: #a:Spec.alg -> #ms:m_spec -> st:state_p a ms -> m:block_w a -> start:size_t{v start <= 144} -> Stack unit
		  (requires (fun h -> live h st /\ live h m /\ disjoint st m))
		  (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1 /\
					state_v h1 st == Spec.gather_state a (as_seq h0 m) (v start)))

inline_for_extraction noextract
let get_sigma' (start: size_t { v start <= 144 }) (i: size_t { normalize (i <=. 15ul) }):
  Stack Spec.sigma_elt_t
    (requires (fun h -> True))
    (ensures  (fun h0 z h1 ->
      h0 == h1 /\ z == Lib.Sequence.(Spec.sigmaTable.[v start + v i])))
=
  get_sigma (start +! i)

#push-options "--z3rlimit 500"
let gather_state #a #ms st m start =
  let h0 = ST.get() in
  let r0 = rowi st 0ul in
  let r1 = rowi st 1ul in
  let r2 = rowi st 2ul in
  let r3 = rowi st 3ul in
  let s0 = get_sigma' start 0ul in
  let s1 = get_sigma' start 1ul in
  let s2 = get_sigma' start 2ul in
  let s3 = get_sigma' start 3ul in
  let s4 = get_sigma' start 4ul in
  let s5 = get_sigma' start 5ul in
  let s6 = get_sigma' start 6ul in
  let s7 = get_sigma' start 7ul in
  let s8 = get_sigma' start 8ul in
  let s9 = get_sigma' start 9ul in
  let s10 = get_sigma' start 10ul in
  let s11 = get_sigma' start 11ul in
  let s12 = get_sigma' start 12ul in
  let s13 = get_sigma' start 13ul in
  let s14 = get_sigma' start 14ul in
  let s15 = get_sigma' start 15ul in
  let h1 = ST.get() in
  gather_row r0 m s0 s2 s4 s6;
  let h2 = ST.get() in
  gather_row r1 m s1 s3 s5 s7;
  let h3 = ST.get() in
  gather_row r2 m s8 s10 s12 s14;
  let h4 = ST.get() in
  gather_row r3 m s9 s11 s13 s15;
  let h5 = ST.get() in
  assert(modifies (loc st) h0 h5);
  Lib.Sequence.eq_intro (state_v h5 st) (Spec.gather_state a (as_seq h0 m) (v start))

inline_for_extraction noextract
val blake2_round : #al:Spec.alg -> #ms:m_spec -> wv:state_p al ms ->  m:block_w al -> i:size_t ->
  Stack unit
    (requires (fun h -> live h wv /\ live h m /\ disjoint wv m))
    (ensures  (fun h0 _ h1 -> modifies (loc wv) h0 h1
                         /\ state_v h1 wv == Spec.blake2_round al (as_seq h0 m) (v i) (state_v h0 wv)))

let blake2_round #al #ms wv m i =
  push_frame();
  let start_idx = (i %. size 10) *. size 16 in
  assert (v start_idx == (v i % 10) * 16);
  assert (v start_idx <= 144);
  let m_st = alloc_state al ms in
  gather_state m_st m start_idx;
  let x = rowi m_st 0ul in
  let y = rowi m_st 1ul in
  let z = rowi m_st 2ul in
  let w = rowi m_st 3ul in
  let h1 = ST.get() in
  assert (disjoint wv m_st);
  assert (disjoint m_st wv);
  assert (disjoint x wv);
  assert (disjoint wv x);
  assert (disjoint y wv);
  assert (disjoint wv y);
  assert (disjoint z wv);
  assert (disjoint wv z);
  assert (disjoint w wv);
  assert (disjoint wv w);
  blake2_mixing wv x y;
  diag  wv;
  blake2_mixing wv z w;
  undiag wv;
  pop_frame ()

inline_for_extraction noextract
val blake2_compress0:
    #al:Spec.alg
  -> m_s: block_p al
  -> m_w: block_w al
  -> Stack unit
    (requires (fun h -> live h m_s /\ live h m_w /\ disjoint m_s m_w))
    (ensures  (fun h0 _ h1 -> modifies (loc m_w) h0 h1
                         /\ as_seq h1 m_w == Spec.blake2_compress0 al (as_seq h0 m_s)))

let blake2_compress0 #al m_s m_w =
  uints_from_bytes_le m_w m_s

inline_for_extraction noextract
val blake2_compress1:
    #al:Spec.alg
  -> #m:m_spec
  -> wv: state_p al m
  -> s_iv: state_p al m
  -> offset: Spec.limb_t al
  -> flag: bool ->
  Stack unit
    (requires (fun h -> live h wv /\ live h s_iv /\ disjoint wv s_iv))
    (ensures  (fun h0 _ h1 -> modifies (loc wv) h0 h1
                         /\ state_v h1 wv == Spec.blake2_compress1 al (state_v h0 s_iv) offset flag))

let blake2_compress1 #al #m wv s_iv offset flag =
  let h0 = ST.get() in
  push_frame();
  let mask = alloc_row al m in
  [@inline_let]
  let wv_12 = Spec.limb_to_word al offset in
  [@inline_let]
  let wv_13 = Spec.limb_to_word al (offset >>. (size (bits (Spec.wt al)))) in
  // SH: TODO: for some reason, ``ones`` below doesn't get inlined by KaRaMeL,
  // causing an extraction problem. The 3 lines below are a hack to fix
  // extraction for the time being:
  // [> let wv_14 = if flag then (ones (Spec.wt al) SEC) else (Spec.zero al) in
  // After investigation, it is because ones is [@(strict_on_arguments [0])],
  // and so isn't unfolded if its first argument is not normalized to a constant.
  // However, the first argument should always be normalized (I checked the
  // output generated by KaRaMeL and the definitions).
  (**) normalize_term_spec (Spec.wt al);
  [@inline_let] let wt_al = normalize_term (Spec.wt al) in
  let wv_14 = if flag then ones wt_al SEC else (Spec.zero al) in
  // end of the TODO
  let wv_15 = Spec.zero al in
  create_row mask wv_12 wv_13 wv_14 wv_15;
  copy_state wv s_iv;
  let wv3 = rowi wv 3ul in
  xor_row wv3 mask;
  pop_frame();
  let h1 = ST.get() in
  assert(modifies (loc wv) h0 h1);
  Lib.Sequence.eq_intro (state_v h1 wv) (Spec.blake2_compress1 al (state_v h0 s_iv) offset flag)

inline_for_extraction noextract
val blake2_compress2 :
  #al:Spec.alg
  -> #ms:m_spec
  -> wv: state_p al ms
  -> m: block_w al ->
  Stack unit
    (requires (fun h -> live h wv /\ live h m /\ disjoint wv m))
    (ensures  (fun h0 _ h1 -> modifies1 wv h0 h1
                         /\ state_v h1 wv == Spec.blake2_compress2 al (state_v h0 wv) (as_seq h0 m)))

#push-options "--z3rlimit 400"
let blake2_compress2 #al #ms wv m =
  let h0 = ST.get () in
  [@inline_let]
  let a_spec = Spec.state al in
  [@inline_let]
  let refl h = state_v h wv in
  [@inline_let]
  let footprint = Ghost.hide(loc wv) in
  [@inline_let]
  let spec h = Spec.blake2_round al h.[|m|] in
  loop_refl h0 (rounds_t al) a_spec refl footprint spec
  (fun i ->
    Loops.unfold_repeati (Spec.rounds al) (spec h0) (state_v h0 wv) (v i);
    blake2_round wv m i)
#pop-options

inline_for_extraction noextract
val blake2_compress3 :
  #al:Spec.alg
  -> #ms:m_spec
  -> s_iv:state_p al ms
  -> wv:state_p al ms ->
  Stack unit
    (requires (fun h -> live h s_iv /\ live h wv /\ disjoint s_iv wv))
    (ensures  (fun h0 _ h1 -> modifies (loc s_iv) h0 h1
                         /\ state_v h1 s_iv == Spec.blake2_compress3 al (state_v h0 wv) (state_v h0 s_iv)))

let blake2_compress3 #al #ms s_iv wv =
  let h0 = ST.get() in
  let s0 = rowi s_iv 0ul in
  let s1 = rowi s_iv 1ul in
  let r0 = rowi wv 0ul in
  let r1 = rowi wv 1ul in
  let r2 = rowi wv 2ul in
  let r3 = rowi wv 3ul in
  assert (disjoint s0 wv);
  assert (disjoint wv s0);
  assert (disjoint s1 wv);
  assert (disjoint wv s1);
  assert (disjoint r0 s0);
  assert (disjoint r2 s0);
  assert (disjoint r1 s1);
  assert (disjoint r3 s1);
  xor_row s0 r0;
  let h1 = ST.get() in
  xor_row s0 r2;
  let h2 = ST.get() in
  xor_row s1 r1;
  let h3 = ST.get() in
  xor_row s1 r3;
  let h4 = ST.get() in
  assert (modifies (loc s_iv) h0 h4);
  let open Lib.Sequence in
  assert (row_v h0 r0 == (state_v h0 wv).[0]);
  assert (row_v h1 r2 == (state_v h0 wv).[2]);
  assert (row_v h4 s0 == Spec.(((state_v h0 s_iv).[0] ^| (state_v h0 wv).[0]) ^| (state_v h0 wv).[2]));
  assert (row_v h4 s1 == Spec.(((state_v h0 s_iv).[1] ^| (state_v h0 wv).[1]) ^| (state_v h0 wv).[3]));
  eq_intro (state_v h2 s_iv) ((state_v h0 s_iv).[0] <- row_v h4 s0);
  eq_intro (state_v h4 s_iv) ((state_v h2 s_iv).[1] <- row_v h4 s1);
  eq_intro (state_v h4 s_iv) (Spec.blake2_compress3 al (state_v h0 wv) (state_v h0 s_iv))



inline_for_extraction noextract
let compress_t (al:Spec.alg) (ms:m_spec) =
    wv:state_p al ms
  -> s: state_p al ms
  -> m: block_p al
  -> offset: Spec.limb_t al
  -> flag: bool ->
  Stack unit
    (requires (fun h -> live h wv /\ live h s /\ live h m /\ disjoint s m /\ disjoint wv s /\ disjoint wv m))
    (ensures  (fun h0 _ h1 -> modifies (loc s |+| loc wv) h0 h1
                         /\ state_v h1 s == Spec.blake2_compress al (state_v h0 s) h0.[|m|] offset flag))


inline_for_extraction noextract
val blake2_compress: #al:Spec.alg -> #ms:m_spec -> compress_t al ms

let blake2_compress #al #ms wv s m offset flag =
  push_frame();
  let m_w = create 16ul (Spec.zero al) in
  blake2_compress0 #al m m_w;
  blake2_compress1 wv s offset flag;
  blake2_compress2 wv m_w;
  blake2_compress3 s wv;
  pop_frame()

inline_for_extraction noextract
let blake2_update_block_st (al:Spec.alg) (ms:m_spec) =
    wv:state_p al ms
  -> hash: state_p al ms
  -> flag: bool
  -> totlen: Spec.limb_t al{v totlen <= Spec.max_limb al}
  -> d: block_p al ->
  Stack unit
    (requires (fun h -> live h wv /\ live h hash /\ live h d /\ disjoint hash d /\ disjoint wv hash /\ disjoint wv d))
    (ensures  (fun h0 _ h1 -> modifies (loc hash |+| loc wv) h0 h1
                         /\ state_v h1 hash == Spec.blake2_update_block al flag (v totlen) h0.[|d|] (state_v h0 hash)))

inline_for_extraction noextract
val blake2_update_block: #al:Spec.alg -> #ms:m_spec -> blake2_update_block_st al ms

let blake2_update_block #al #ms wv hash flag totlen d =
    blake2_compress wv hash d totlen flag

inline_for_extraction noextract
let blake2_update1_st (al:Spec.alg) (ms:m_spec) =
   #len:size_t
  -> wv: state_p al ms
  -> hash: state_p al ms
  -> prev: Spec.limb_t al{v prev + v len <= Spec.max_limb al}
  -> d: lbuffer uint8 len
  -> i: size_t{v i < length d / Spec.size_block al} ->
  Stack unit
    (requires (fun h -> live h wv /\ live h hash /\ live h d /\ disjoint hash d /\ disjoint wv hash /\ disjoint wv d))
    (ensures  (fun h0 _ h1 -> modifies (loc hash |+| loc wv) h0 h1
                         /\ state_v h1 hash == Spec.blake2_update1 al (v prev) h0.[|d|] (v i) (state_v h0 hash)))

inline_for_extraction noextract
val blake2_update1: #al:Spec.alg -> #ms:m_spec -> blake2_update_block: blake2_update_block_st al ms -> blake2_update1_st al ms

let blake2_update1 #al #ms blake2_update_block #len wv hash prev d i =
  let totlen = prev +. size_to_limb al ((i+!1ul) *! size_block al) in
  assert (v totlen == v prev + (v i + 1) * Spec.size_block al);
  let b = sub d (i *. size_block al) (size_block al) in
  let h = ST.get() in
  assert (as_seq h b == Spec.get_blocki al (as_seq h d) (v i));
  blake2_update_block wv hash false totlen b

inline_for_extraction noextract
let blake2_update_last_st (al:Spec.alg) (ms:m_spec) =
   #len:size_t
  -> wv: state_p al ms
  -> hash: state_p al ms
  -> prev: Spec.limb_t al{v prev + v len <= Spec.max_limb al}
  -> rem: size_t {v rem <= v len /\ v rem <= Spec.size_block al}
  -> d: lbuffer uint8 len ->
  Stack unit
    (requires (fun h -> live h wv /\ live h hash /\ live h d /\ disjoint hash d /\ disjoint wv hash /\ disjoint wv d))
    (ensures  (fun h0 _ h1 -> modifies (loc hash |+| loc wv) h0 h1
                         /\ state_v h1 hash == Spec.blake2_update_last al (v prev) (v rem) h0.[|d|] (state_v h0 hash)))

inline_for_extraction noextract
val blake2_update_last:
     #al:Spec.alg
  -> #ms:m_spec
  -> blake2_update_block: blake2_update_block_st al ms
  -> blake2_update_last_st al ms

let blake2_update_last #al #ms blake2_update_block #len wv hash prev rem d =
  let h0 = ST.get () in
  [@inline_let]
  let spec _ h1 = state_v h1 hash == Spec.blake2_update_last al (v prev) (v rem) h0.[|d|] (state_v h0 hash) in
  salloc1 h0 (size_block al) (u8 0) (Ghost.hide (loc hash |+| loc wv)) spec
  (fun last_block ->
    let last = sub d (len -! rem) rem in
    let h1 = ST.get() in
    update_sub last_block 0ul rem last;
    let h2 = ST.get() in
    as_seq_gsub h1 d (len -! rem) rem;
    assert (as_seq h1 last == Seq.sub (as_seq h1 d) (v len - v rem) (v rem));
    assert (as_seq h1 last == Seq.slice (as_seq h0 d) (v len - v rem) (v len));
    assert (as_seq h2 last_block == Spec.get_last_padded_block al (as_seq h0 d) (v rem));
    let totlen = prev +. (size_to_limb al len) in
    blake2_update_block wv hash true totlen last_block;
    let h3 = ST.get() in
    assert (v totlen == v prev + v len);
    assert (state_v h3 hash == Spec.blake2_update_block al true (v totlen) (as_seq h2 last_block) (state_v h0 hash)))

inline_for_extraction noextract
let blake2_init_st  (al:Spec.alg) (ms:m_spec) =
    hash: state_p al ms
  -> kk: size_t{v kk <= Spec.max_key al}
  -> nn: size_t{1 <= v nn /\ v nn <= Spec.max_output al} ->
  Stack unit
    (requires (fun h -> live h hash))
    (ensures  (fun h0 _ h1 -> modifies (loc hash) h0 h1 /\
			   state_v h1 hash == Spec.blake2_init_hash al (Spec.blake2_default_params al) (v kk) (v nn)))

inline_for_extraction noextract
val serialize_params (al:Spec.alg)
  (kk:size_t{v kk <= Spec.max_key al})
  (nn: size_t{1 <= v nn /\ v nn <= Spec.max_output al})
  (p: blake2_params al)
  (b: lbuffer (word_t al) 8ul)
  : Stack unit
    (requires fun h ->
      live h b /\
      blake2_params_inv h p /\
      LowStar.Buffer.loc_disjoint (loc b) (blake2_params_loc p) /\
      as_seq h b == Seq.create 8 (Spec.nat_to_word al 0)
    )
    (ensures fun h0 _ h1 ->
      modifies (loc b) h0 h1 /\
      as_seq h1 b == Spec.serialize_blake2_params
        {blake2_params_v h0 p with key_length = u8 (v kk); digest_length = u8 (v nn)}
    )

#push-options "--z3rlimit 100 --fuel 0"
inline_for_extraction noextract
let serialize_params_blake2s
  (kk:size_t{v kk <= Spec.max_key Spec.Blake2S})
  (nn: size_t{1 <= v nn /\ v nn <= Spec.max_output Spec.Blake2S})
  (p: blake2_params Spec.Blake2S)
  (b: lbuffer (word_t Spec.Blake2S) 8ul)
  : Stack unit
    (requires fun h -> live h b /\
      blake2_params_inv h p /\
      LowStar.Buffer.loc_disjoint (loc b) (blake2_params_loc p) /\
      as_seq h b == Seq.create 8 (u32 0)
    )
    (ensures fun h0 _ h1 ->
      modifies (loc b) h0 h1 /\
      as_seq h1 b == Spec.serialize_blake2_params
         {blake2_params_v h0 p with key_length = u8 (v kk); digest_length = u8 (v nn)}
    )
  = let h0 = ST.get () in
    [@inline_let]
    let kk_shift_8 = shift_left (to_u32 kk) (size 8) in
    [@inline_let]
    let fanout_shift_16 = shift_left (to_u32 p.fanout) (size 16) in
    [@inline_let]
    let depth_shift_24 = shift_left (to_u32 p.depth) (size 24) in
    [@inline_let]
    let v0 = (to_u32 nn) ^. kk_shift_8 ^. fanout_shift_16 ^. depth_shift_24 in
    [@inline_let]
    let v1 = p.leaf_length in
    [@inline_let]
    let v2 = to_u32 p.node_offset in
    [@inline_let]
    let node_offset_high = to_u32 (shift_right p.node_offset (size 32)) in
    [@inline_let]
    let node_depth_shift_16 = shift_left (to_u32 p.node_depth) (size 16) in
    [@inline_let]
    let inner_length_shift_16 = shift_left (to_u32 p.inner_length) (size 24) in
    [@inline_let]
    let v3 = node_offset_high ^. node_depth_shift_16 ^. inner_length_shift_16 in

    uints_from_bytes_le (sub b 4ul 2ul) p.salt;
    uints_from_bytes_le (sub b 6ul 2ul) p.personal;

    // AF: Putting these writes *after* modifications on a subbuffer of b helps with modifies-reasoning:
    // By putting them before, F* struggles with proving that b[0..3] is not modified by uints_from_bytes_le
    b.(0ul) <- v0;
    b.(1ul) <- v1;
    b.(2ul) <- v2;
    b.(3ul) <- v3;

    let h1 = ST.get () in
    let aux () : Lemma (as_seq h1 b `Seq.equal` Spec.serialize_blake2s_params
         {blake2_params_v h0 p with key_length = u8 (v kk); digest_length = u8 (v nn)}) =
      let open Lib.Sequence in
      let open Lib.ByteSequence in
      let s0 = (u32 (v nn)) ^.
               (u32 (v kk) <<. (size 8)) ^.
               (u32 (v p.fanout) <<. (size 16)) ^.
               (u32 (v p.depth) <<. (size 24)) in
      let s1 = p.leaf_length in
      (* Take the first four bytes *)
      let s2 = (to_u32 p.node_offset) in
      (* Take the last four bytes of node_offset *)
      let s3 = (to_u32 (p.node_offset >>. (size 32))) ^.
               (u32 (v p.node_depth) <<. (size 16)) ^.
               (u32 (v p.inner_length) <<. (size 24)) in
      let salt_u32: lseq uint32 2 = uints_from_bytes_le (as_seq h0 p.salt) in
      let s4 = salt_u32.[0] in
      let s5 = salt_u32.[1] in
      let personal_u32: lseq uint32 2 = uints_from_bytes_le (as_seq h0 p.personal) in
      let s6 = personal_u32.[0] in
      let s7 = personal_u32.[1] in
      [@inline_let]
      let l = [s0; s1; s2; s3; s4; s5; s6; s7] in
      assert_norm (List.Tot.length l == 8);

      // There seems to be something not triggering with createL, requiring the
      // following lemma calls, and assert_norms to relate List.index to the
      // actual elements

      assert_norm (List.Tot.index l 0 == s0);
      assert_norm (List.Tot.index l 1 == s1);
      assert_norm (List.Tot.index l 2 == s2);
      assert_norm (List.Tot.index l 3 == s3);
      assert_norm (List.Tot.index l 4 == s4);
      assert_norm (List.Tot.index l 5 == s5);
      assert_norm (List.Tot.index l 6 == s6);
      assert_norm (List.Tot.index l 7 == s7);
      of_list_index l 0;
      of_list_index l 1;
      of_list_index l 2;
      of_list_index l 3;
      of_list_index l 4;
      of_list_index l 5;
      of_list_index l 6;
      of_list_index l 7
    in
    aux()

inline_for_extraction noextract
let serialize_params_blake2b
  (kk:size_t{v kk <= Spec.max_key Spec.Blake2B})
  (nn: size_t{1 <= v nn /\ v nn <= Spec.max_output Spec.Blake2B})
  (p: blake2_params Spec.Blake2B)
  (b: lbuffer (word_t Spec.Blake2B) 8ul)
  : Stack unit
    (requires fun h -> live h b /\
      blake2_params_inv #Spec.Blake2B h p /\
      LowStar.Buffer.loc_disjoint (loc b) (blake2_params_loc p) /\
      as_seq h b == Seq.create 8 (u64 0)
    )
    (ensures fun h0 _ h1 ->
      modifies (loc b) h0 h1 /\
      as_seq h1 b == Spec.serialize_blake2_params
         {blake2_params_v h0 p with key_length = u8 (v kk); digest_length = u8 (v nn)}
    )
  = let h0 = ST.get () in
    [@inline_let]
    let kk_shift_8 = shift_left (to_u64 kk) (size 8) in
    [@inline_let]
    let fanout_shift_16 = shift_left (to_u64 p.fanout) (size 16) in
    [@inline_let]
    let depth_shift_24 = shift_left (to_u64 p.depth) (size 24) in
    [@inline_let]
    let leaf_length_shift_32 = shift_left (to_u64 p.leaf_length) (size 32) in
    [@inline_let]
    let v0 = (to_u64 nn) ^. kk_shift_8 ^. fanout_shift_16 ^. depth_shift_24 ^. leaf_length_shift_32 in
    [@inline_let]
    let v1 = p.node_offset in
    [@inline_let]
    let inner_length_shift_8 = shift_left (to_u64 p.inner_length) (size 8) in
    [@inline_let]
    let v2 = (to_u64 p.node_depth) ^. inner_length_shift_8 in

    uints_from_bytes_le (sub b 4ul 2ul) p.salt;
    uints_from_bytes_le (sub b 6ul 2ul) p.personal;

    b.(0ul) <- v0;
    b.(1ul) <- v1;
    b.(2ul) <- v2;
    b.(3ul) <- (u64 0);

    let h1 = ST.get () in
    let aux () : Lemma (as_seq h1 b `Seq.equal` Spec.serialize_blake2b_params
        {blake2_params_v h0 p with key_length = u8 (v kk); digest_length = u8 (v nn)}) =
      let open Lib.Sequence in
      let open Lib.ByteSequence in
      let s0 = (u64 (v nn)) ^.
               (u64 (v kk) <<. (size 8)) ^.
               (u64 (v p.fanout) <<. (size 16)) ^.
               (u64 (v p.depth) <<. (size 24)) ^.
               (u64 (v p.leaf_length) <<. (size 32)) in
      let s1 = p.node_offset in
      // The serialization corresponding to s2 contains node_depth and inner_length,
      // followed by the 14 reserved bytes which always seem to be zeros, and can hence
      // be ignored when building the corresponding uint64 using xor's
      let s2 = (u64 (v p.node_depth)) ^.
               (u64 (v p.inner_length) <<. (size 8)) in
      // s3 corresponds to the remaining of the reserved bytes
      let s3 = u64 0 in
      let salt_u64: lseq uint64 2 = uints_from_bytes_le (as_seq h0 p.salt) in
      let s4 = salt_u64.[0] in
      let s5 = salt_u64.[1] in
      let personal_u64: lseq uint64 2 = uints_from_bytes_le (as_seq h0 p.personal) in
      let s6 = personal_u64.[0] in
      let s7 = personal_u64.[1] in
      [@inline_let]
      let l = [s0; s1; s2; s3; s4; s5; s6; s7] in
      assert_norm (List.Tot.length l == 8);

      // There seems to be something not triggering with createL, requiring the
      // following lemma calls, and assert_norms to relate List.index to the
      // actual elements

      assert_norm (List.Tot.index l 0 == s0);
      assert_norm (List.Tot.index l 1 == s1);
      assert_norm (List.Tot.index l 2 == s2);
      assert_norm (List.Tot.index l 3 == s3);
      assert_norm (List.Tot.index l 4 == s4);
      assert_norm (List.Tot.index l 5 == s5);
      assert_norm (List.Tot.index l 6 == s6);
      assert_norm (List.Tot.index l 7 == s7);
      of_list_index l 0;
      of_list_index l 1;
      of_list_index l 2;
      of_list_index l 3;
      of_list_index l 4;
      of_list_index l 5;
      of_list_index l 6;
      of_list_index l 7
    in
    aux()
#pop-options

let serialize_params al kk nn p b =
  match al with
  | Spec.Blake2S -> serialize_params_blake2s kk nn p b
  | Spec.Blake2B -> serialize_params_blake2b kk nn p b

inline_for_extraction noextract
val blake2_init:
    #al:Spec.alg
  -> #ms:m_spec
  -> blake2_init_st al ms

let blake2_init #al #ms hash kk nn =
  push_frame ();
  let h0 = ST.get() in
  let tmp = create 8ul (Spec.nat_to_word al 0) in
  let r0 = rowi hash 0ul in
  let r1 = rowi hash 1ul in
  let r2 = rowi hash 2ul in
  let r3 = rowi hash 3ul in
  let iv0 = get_iv al 0ul in
  let iv1 = get_iv al 1ul in
  let iv2 = get_iv al 2ul in
  let iv3 = get_iv al 3ul in
  let iv4 = get_iv al 4ul in
  let iv5 = get_iv al 5ul in
  let iv6 = get_iv al 6ul in
  let iv7 = get_iv al 7ul in
  create_row #al #ms r2 iv0 iv1 iv2 iv3;
  create_row #al #ms r3 iv4 iv5 iv6 iv7;
  let salt = create (salt_len al) (u8 0) in
  let personal = create (personal_len al) (u8 0) in
  let p = create_default_params al salt personal in
  serialize_params al kk nn p tmp;
  let tmp0 = tmp.(0ul) in
  let tmp1 = tmp.(1ul) in
  let tmp2 = tmp.(2ul) in
  let tmp3 = tmp.(3ul) in
  let tmp4 = tmp.(4ul) in
  let tmp5 = tmp.(5ul) in
  let tmp6 = tmp.(6ul) in
  let tmp7 = tmp.(7ul) in
  let iv0' = iv0 ^. tmp0 in
  let iv1' = iv1 ^. tmp1 in
  let iv2' = iv2 ^. tmp2 in
  let iv3' = iv3 ^. tmp3 in
  let iv4' = iv4 ^. tmp4 in
  let iv5' = iv5 ^. tmp5 in
  let iv6' = iv6 ^. tmp6 in
  let iv7' = iv7 ^. tmp7 in
  create_row #al #ms r0 iv0' iv1' iv2' iv3';
  create_row #al #ms r1 iv4' iv5' iv6' iv7';
  let h1 = ST.get() in
  assert (disjoint hash tmp);
  assert (modifies (loc hash `union` loc tmp) h0 h1);
  Lib.Sequence.eq_intro (state_v h1 hash) (Spec.blake2_init_hash al (Spec.blake2_default_params al) (v kk) (v nn));
  pop_frame ()

#push-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"
let _ : squash (inversion Spec.alg) = allow_inversion Spec.alg

inline_for_extraction noextract
val split_blocks: al:Spec.alg -> len:size_t -> r:(size_t & size_t){
					  let (x,y) = r in
					  let (sx,sy) = Spec.split al (v len) in
					  sx == v x /\
					  sy == v y}

let split_blocks al len =
  let nb = len /. size_block al in
  let rem = len %. size_block al in
  (if rem =. 0ul && nb >. 0ul then nb -! 1ul else nb),
  (if rem =. 0ul && nb >. 0ul then size_block al else rem)

inline_for_extraction noextract
let blake2_update_multi_st (al : Spec.alg) (ms : m_spec) =
     #len:size_t
  -> wv: state_p al ms
  -> hash: state_p al ms
  -> prev: Spec.limb_t al{v prev + v len <= Spec.max_limb al}
  -> blocks: lbuffer uint8 len
  -> nb : size_t{length blocks >= v nb * v (size_block al) } ->
  Stack unit
    (requires (fun h -> live h wv /\ live h hash /\ live h blocks /\
                      disjoint hash blocks /\ disjoint wv hash /\ disjoint wv blocks))
    (ensures  (fun h0 _ h1 ->
      modifies (loc hash |+| loc wv) h0 h1 /\
      state_v h1 hash == repeati (v nb) (Spec.blake2_update1 al (v prev) h0.[|blocks|])
                                 (state_v h0 hash)))

inline_for_extraction noextract
val blake2_update_multi (#al : Spec.alg) (#ms : m_spec) :
     blake2_update_block:blake2_update_block_st al ms
  -> blake2_update_multi_st al ms

let blake2_update_multi #al #ms blake2_update_block #len wv hash prev blocks nb =
  let h0 = ST.get () in
  [@inline_let]
  let a_spec = Spec.state al in
  [@inline_let]
  let refl h = state_v h hash in
  [@inline_let]
  let footprint = Ghost.hide(loc hash |+| loc wv) in
  [@inline_let]
  let spec h = Spec.blake2_update1 al (v prev) h.[|blocks|] in
  loop_refl h0 nb a_spec refl footprint spec
  (fun i ->
    Loops.unfold_repeati (v nb) (spec h0) (state_v h0 hash) (v i);
    blake2_update1 #al #ms blake2_update_block #len wv hash prev blocks i)

inline_for_extraction noextract
let blake2_update_blocks_st (al : Spec.alg) (ms : m_spec) =
     #len:size_t
  -> wv: state_p al ms
  -> hash: state_p al ms
  -> prev: Spec.limb_t al{v prev + v len <= Spec.max_limb al}
  -> blocks: lbuffer uint8 len ->
  Stack unit
    (requires (fun h -> live h wv /\ live h hash /\ live h blocks /\ disjoint hash blocks /\ disjoint wv hash /\ disjoint wv blocks))
    (ensures  (fun h0 _ h1 -> modifies (loc hash |+| loc wv) h0 h1 /\
			   state_v h1 hash ==
			   Spec.blake2_update_blocks al (v prev) h0.[|blocks|] (state_v h0 hash)))

inline_for_extraction noextract
val blake2_update_blocks (#al : Spec.alg) (#ms : m_spec) :
     blake2_update_multi_st al ms
  -> blake2_update_last_st al ms
  -> blake2_update_blocks_st al ms

let blake2_update_blocks #al #ms blake2_update_multi blake2_update_last #len wv hash prev blocks =
  let (nb,rem) = split_blocks al len in
  blake2_update_multi wv hash prev blocks nb;
  blake2_update_last #len wv hash prev rem blocks

inline_for_extraction noextract
let blake2_finish_st (al:Spec.alg) (ms:m_spec) =
    nn: size_t{1 <= v nn /\ v nn <= Spec.max_output al}
  -> output: lbuffer uint8 nn
  -> hash: state_p al ms ->
  Stack unit
    (requires (fun h -> live h hash /\ live h output /\ disjoint output hash))
    (ensures  (fun h0 _ h1 -> modifies (loc output) h0 h1
                         /\ h1.[|output|] == Spec.blake2_finish al (state_v h0 hash) (v nn)))

inline_for_extraction noextract
val blake2_finish:#al:Spec.alg -> #ms:m_spec -> blake2_finish_st al ms

let blake2_finish #al #ms nn output hash =
  let h0 = ST.get () in
  [@inline_let]
  let double_row = 2ul *. size_row al in
  [@inline_let]
  let spec _ h1 = h1.[|output|] == Spec.blake2_finish al (state_v h0 hash) (v nn) in
  salloc1 h0 double_row (u8 0) (Ghost.hide (loc output)) spec
  (fun full ->
    let first = sub full 0ul (size_row al) in
    let second = sub full (size_row al) (size_row al) in
    let row0 = rowi hash 0ul in
    let row1 = rowi hash 1ul in
    store_row first row0;
    store_row second row1;
    let h1 = ST.get() in
    Lib.Sequence.eq_intro (as_seq h1 full)
	(Lib.Sequence.(as_seq h1 (gsub full 0ul (size_row al)) @|
		       as_seq h1 (gsub full (size_row al) (size_row al))));
    let final = sub full (size 0) nn in
    copy output final)


inline_for_extraction noextract
let blake2_update_key_st (al:Spec.alg) (ms:m_spec) =
    wv:state_p al ms
  -> hash: state_p al ms
  -> kk: size_t{v kk > 0 /\ v kk <= Spec.max_key al}
  -> k: lbuffer uint8 kk
  -> ll: size_t ->
  Stack unit
    (requires (fun h -> live h wv /\ live h hash /\ live h k /\
                     disjoint hash k /\ disjoint wv hash /\ disjoint wv k))
    (ensures  (fun h0 _ h1 -> modifies (loc hash |+| loc wv) h0 h1
                         /\ state_v h1 hash == Spec.blake2_update_key al (v kk) h0.[|k|] (v ll) (state_v h0 hash)))

inline_for_extraction noextract
val blake2_update_key:
     #al:Spec.alg
  -> #ms:m_spec
  -> blake2_update_block_st al ms
  -> blake2_update_key_st al ms

inline_for_extraction noextract
let blake2_update_key #al #ms blake2_update_block wv hash kk k ll =
  let lb = size_to_limb al (size_block al) in
  assert (v lb = Spec.size_block al);
  let h0 = ST.get () in
  salloc1 h0 (size_block al) (u8 0) (Ghost.hide (loc hash |+| loc wv))
    (fun _ h1 -> live h1 hash /\ state_v h1 hash == Spec.blake2_update_key al (v kk) h0.[|k|] (v ll) (state_v h0 hash))
    (fun key_block ->
      update_sub key_block 0ul kk k;
      let h1 = ST.get() in
      if ll =. 0ul then
         blake2_update_block wv hash true lb key_block
      else
         blake2_update_block wv hash false lb key_block)

inline_for_extraction noextract
let blake2_update_st (al:Spec.alg) (ms:m_spec) =
    wv:state_p al ms
  -> hash: state_p al ms
  -> kk: size_t{v kk <= Spec.max_key al}
  -> k: lbuffer uint8 kk
  -> ll: size_t
  -> d: lbuffer uint8 ll ->
  Stack unit
    (requires (fun h -> live h wv /\ live h hash /\ live h k /\ live h d /\
                     disjoint hash k /\ disjoint wv hash /\ disjoint wv k /\
                     disjoint hash d /\ disjoint wv d /\ disjoint d k))
    (ensures  (fun h0 _ h1 -> modifies (loc hash |+| loc wv) h0 h1
                         /\ state_v h1 hash == Spec.blake2_update al (v kk) h0.[|k|] h0.[|d|] (state_v h0 hash)))


inline_for_extraction noextract
val blake2_update:
     #al:Spec.alg
  -> #ms:m_spec
  -> blake2_update_key_st al ms
  -> blake2_update_blocks_st al ms
  -> blake2_update_st al ms

inline_for_extraction noextract
let blake2_update #al #ms blake2_update_key blake2_update_blocks
                  wv hash kk k ll d =
    let lb = size_to_limb al (size_block al) in
    assert (v lb = Spec.size_block al);
    if kk >. 0ul then (
      blake2_update_key wv hash kk k ll;
      if ll =. 0ul then ()
      else blake2_update_blocks wv hash lb d)
    else blake2_update_blocks wv hash (size_to_limb al 0ul) d

inline_for_extraction noextract
let blake2_st (al:Spec.alg) (ms:m_spec) =
    output: buffer_t MUT uint8
  -> output_len: size_t{v output_len == length output /\ 1 <= v output_len /\ v output_len <= Spec.max_output al}
  -> input: buffer_t MUT uint8
  -> input_len: size_t{v input_len == length input}
  -> key: buffer_t MUT uint8
  -> key_len: size_t{v key_len == length key /\ v key_len <= Spec.max_key al} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input /\ live h key
                   /\ disjoint output input /\ disjoint output key /\ disjoint input key))
    (ensures  (fun h0 _ h1 -> modifies1 output h0 h1
                         /\ h1.[|(output <: lbuffer uint8 output_len)|] == Spec.blake2 al h0.[|(input <: lbuffer uint8 input_len)|] (Spec.blake2_default_params al) (v key_len) h0.[|(key <: lbuffer uint8 key_len)|] (v output_len)))

inline_for_extraction noextract
val blake2:
    #al:Spec.alg
  -> #ms:m_spec
  -> blake2_init_st al ms
  -> blake2_update_st al ms
  -> blake2_finish_st al ms
  -> blake2_st al ms

#push-options "--z3rlimit 100"
let blake2 #al #ms blake2_init blake2_update blake2_finish output output_len input input_len key key_len =
  [@inline_let]
  let stlen = le_sigh al ms in
  [@inline_let]
  let stzero = zero_element al ms in
  let h0 = ST.get() in
  [@inline_let]
  let spec _ h1 = h1.[|output|] == Spec.blake2 al h0.[|(input <: lbuffer uint8 input_len)|] (Spec.blake2_default_params al) (v key_len) h0.[|key|] (v output_len) in
  salloc1 h0 stlen stzero (Ghost.hide (loc output)) spec
  (fun h ->
    assert (max_size_t <= Spec.max_limb al);
    let h1 = ST.get() in
    salloc1 h1 stlen stzero (Ghost.hide (loc output |+| loc h)) spec
    (fun wv ->
      blake2_init h key_len output_len;
      blake2_update wv h key_len key input_len input;
      blake2_finish output_len output h))
#pop-options

module B = LowStar.Buffer
module M = LowStar.Modifies

// A little wrapper needed by EverCrypt.Hash
inline_for_extraction noextract
let blake2_malloc_st (al:Spec.alg) (ms:m_spec) = r:rid -> ST.ST (state_p al ms)
  (requires (fun h ->
    ST.is_eternal_region r))
  (ensures (fun h0 s h1 ->
    live h1 s /\
    M.(modifies loc_none h0 h1) /\
    B.fresh_loc (loc_addr_of_buffer s) h0 h1 /\
    (M.loc_includes (M.loc_region_only true r) (loc_addr_of_buffer s)) /\
    freeable s))

inline_for_extraction noextract
val blake2_malloc:
    al:Spec.alg
  -> ms:m_spec
  -> blake2_malloc_st al ms

#push-options "--ifuel 1"
inline_for_extraction noextract
let impl_state_len (al:Spec.alg) (ms:m_spec) : size_t = //{size_v s == impl_state_length i} =
    (**) mul_mod_lemma 4ul (row_len al ms);
    match al, ms with
    | Spec.Blake2S, M32
    | Spec.Blake2B, M32 | Spec.Blake2B, M128 -> 16ul
    | Spec.Blake2S, M128 | Spec.Blake2S, M256
    | Spec.Blake2B, M256 -> 4ul
#pop-options

let blake2_malloc a m r =
  B.malloc r (Hacl.Impl.Blake2.Core.zero_element a m) (impl_state_len a m)
