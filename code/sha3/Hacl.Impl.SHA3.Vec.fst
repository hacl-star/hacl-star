module Hacl.Impl.SHA3.Vec

open Hacl.Spec.SHA3.Vec.Common

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul
open Lib.IntTypes
open Lib.NTuple
open Lib.Sequence
open Lib.IntVector
open Lib.MultiBuffer
open Lib.LoopCombinators
open Lib.IntVector.Transpose

open LowStar.Buffer
open LowStar.BufferOps

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Spec.Hash.Definitions
open Spec.SHA3.Constants

open Hacl.Spec.SHA3.Vec

module ST = FStar.HyperStack.ST
module B = LowStar.Buffer
module LSeq = Lib.Sequence
module LB = Lib.ByteSequence
module Loop = Lib.LoopCombinators
module S = Spec.SHA3
module Equiv = Spec.SHA3.Equivalence
module V = Hacl.Spec.SHA3.Vec
module HD = Hacl.Hash.Definitions

private let keccak_rotc :x:glbuffer rotc_t 24ul{witnessed x keccak_rotc /\ recallable x}
  = createL_global rotc_list

private let keccak_piln :x:glbuffer piln_t 24ul{witnessed x keccak_piln /\ recallable x}
  = createL_global piln_list

private let keccak_rndc :x:glbuffer pub_uint64 24ul{witnessed x keccak_rndc /\ recallable x}
  = createL_global rndc_list

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(*
//TODO: remove when Spec.Hash.Definitions.word_t is fixed
inline_for_extraction
let word_t (a:hash_alg) = U64

//TODO: remove when Spec.Hash.Definitions.word is fixed
inline_for_extraction
let word (a:hash_alg) = uint_t (word_t a) SEC

//TODO: remove when Spec.Hash.Definitions.word is fixed
inline_for_extraction
let words_state' a = m:Seq.seq (word a) {Seq.length m = state_word_length a}
*)



inline_for_extraction noextract
let state_t (m:m_spec) = lbuffer (element_t m) 25ul

inline_for_extraction noextract
let ws_t (m:m_spec) = lbuffer (element_t m) 32ul

inline_for_extraction noextract
let index = n:size_t{v n < 5}

inline_for_extraction noextract
val get:
    m:m_spec
  -> s:state_t m
  -> x:index
  -> y:index
  -> Stack (element_t m)
    (requires fun h -> live h s)
    (ensures  fun h0 r h1 ->
      modifies loc_none h0 h1 /\
      r == V.get m (as_seq h0 s) (v x) (v y))
let get _ s x y = s.(x +! 5ul *! y)

inline_for_extraction noextract
val set:
    m:m_spec
  -> s:state_t m
  -> x:index
  -> y:index
  -> v:element_t m
  -> Stack unit
    (requires fun h -> live h s)
    (ensures  fun h0 _ h1 ->
      modifies (loc s) h0 h1 /\
      as_seq h1 s == V.set m (as_seq h0 s) (size_v x) (size_v y) v)
let set _ s x y v = s.(x +! 5ul *! y) <- v

inline_for_extraction noextract
val state_theta0:
    m:m_spec
  -> s:state_t m
  -> _C:lbuffer (element_t m) 5ul
  -> Stack unit
    (requires fun h -> live h s /\ live h _C /\ disjoint _C s)
    (ensures  fun h0 _ h1 ->
      modifies (loc _C) h0 h1 /\
      as_seq h1 _C == V.state_theta0 m (as_seq h0 s) (as_seq h0 _C))
let state_theta0 m s _C =
  [@ inline_let]
  let spec h0 = V.state_theta_inner_C m (as_seq h0 s) in
  let h0 = ST.get () in
  loop1 h0 5ul _C spec
  (fun x ->
    Loop.unfold_repeati 5 (spec h0) (as_seq h0 _C) (v x);
    _C.(x) <-
      get m s x 0ul ^|
      get m s x 1ul ^|
      get m s x 2ul ^|
      get m s x 3ul ^|
      get m s x 4ul
  )

inline_for_extraction noextract
val state_theta_inner_s:
    m:m_spec
  -> _C:lbuffer (element_t m) 5ul
  -> x:index
  -> s:state_t m
  -> Stack unit
    (requires fun h0 -> live h0 s /\ live h0 _C /\ disjoint _C s)
    (ensures  fun h0 _ h1 ->
      modifies (loc s) h0 h1 /\
      as_seq h1 s == V.state_theta_inner_s m (as_seq h0 _C) (v x) (as_seq h0 s))
let state_theta_inner_s m _C x s =
  let _D = _C.((x +. 4ul) %. 5ul) ^| (_C.((x +. 1ul) %. 5ul) <<<| 1ul) in
  [@ inline_let]
  let spec h0 = V.state_theta_inner_s_inner m (v x) _D in
  let h0 = ST.get () in
  loop1 h0 5ul s spec
  (fun y ->
    Loop.unfold_repeati 5 (spec h0) (as_seq h0 s) (v y);
    set m s x y (get m s x y ^| _D)
  )

inline_for_extraction noextract
val state_theta1:
    m:m_spec
  -> s:state_t m
  -> _C:lbuffer (element_t m) 5ul
  -> Stack unit
    (requires fun h0 -> live h0 s /\ live h0 _C /\ disjoint _C s)
    (ensures  fun h0 _ h1 ->
      modifies (loc s) h0 h1 /\
      as_seq h1 s == V.state_theta1 m (as_seq h0 s) (as_seq h0 _C))
let state_theta1 m s _C =
  [@ inline_let]
  let spec h0 = V.state_theta_inner_s m (as_seq h0 _C) in
  let h0 = ST.get () in
  loop1 h0 5ul s spec
  (fun x ->
    Loop.unfold_repeati 5 (spec h0) (as_seq h0 s) (v x);
    state_theta_inner_s m _C x s
  )

inline_for_extraction noextract
val state_theta:
    m:m_spec
  -> s:state_t m
  -> Stack unit
    (requires fun h -> live h s)
    (ensures  fun h0 _ h1 ->
      modifies (loc s) h0 h1 /\
      as_seq h1 s == V.state_theta m (as_seq h0 s))
let state_theta m s =
  push_frame ();
  let h0 = ST.get() in
  let _C = create 5ul (zero_element m) in 
  state_theta0 m s _C; state_theta1 m s _C;
  pop_frame()


#reset-options "--max_fuel 1 --max_ifuel 1 --z3rlimit 50"

private
val index_map: #a:Type -> #b:Type -> f:(a -> b) -> l:list a -> i:nat{i < List.Tot.length l} ->
  Lemma (List.Tot.index (List.Tot.map f l) i == f (List.Tot.index l i))
let rec index_map #a #b f l i =
  if i = 0 then ()
  else
    match l with
    | [] -> ()
    | _ :: l' -> index_map f l' (i - 1)

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

inline_for_extraction noextract
val state_pi_rho_inner:
    m:m_spec
  -> i:size_t{v i < 24}
  -> current:lbuffer (element_t m) 1ul
  -> s:state_t m
  -> Stack unit
    (requires fun h -> live h s /\ live h current /\ disjoint current s)
    (ensures  fun h0 _ h1 ->
      modifies (loc_union (loc s) (loc current)) h0 h1 /\
      (let c', s' = V.state_pi_rho_inner m (v i) (bget h0 current 0, as_seq h0 s) in
      bget h1 current 0 == c' /\
      as_seq h1 s == s'))
let state_pi_rho_inner _ i current s =
  assert_norm (List.Tot.length piln_list == 24);
  let h0 = ST.get () in
  recall_contents keccak_rotc Spec.SHA3.Constants.keccak_rotc;
  recall_contents keccak_piln Spec.SHA3.Constants.keccak_piln;
  index_map v piln_list (v i);
  let _Y = keccak_piln.(i) in
  let r = keccak_rotc.(i) in
  let temp = s.(_Y) in
  s.(_Y) <- current.(0ul) <<<| r;
  current.(0ul) <- temp

inline_for_extraction noextract
val state_pi_rho:
    m:m_spec
  -> s:state_t m
  -> Stack unit
    (requires fun h -> live h s)
    (ensures  fun h0 _ h1 ->
      modifies (loc s) h0 h1 /\
      as_seq h1 s == V.state_pi_rho m (as_seq h0 s))
let state_pi_rho m s =
  push_frame();
  let x = get m s 1ul 0ul in
  let h0 = ST.get() in
  let current = create 1ul x in
  let h1 = ST.get () in
  assert (bget h1 current 0 == V.get m (as_seq h0 s) 1 0);
  [@ inline_let]
  let refl h i : GTot ((element_t m) & (V.state m)) = bget h current 0, as_seq h s in
  [@ inline_let]
  let footprint i = loc_union (loc current) (loc s) in
  [@ inline_let]
  let spec h0 = V.state_pi_rho_inner m in
  let h0 = ST.get () in
  loop h0 24ul (V.state_pi_rho_s m) refl footprint spec
  (fun i ->
    Loop.unfold_repeat_gen 24 (V.state_pi_rho_s m) (spec h0) (refl h0 0) (v i);
    state_pi_rho_inner m i current s
  );
  pop_frame()

inline_for_extraction noextract
val state_chi_inner:
    m:m_spec
  -> st:state_t m
  -> y:index
  -> Stack unit
    (requires fun h0 -> live h0 st)
    (ensures  fun h0 _ h1 ->
      modifies (loc st) h0 h1 /\
      as_seq h1 st == V.state_chi_inner m (v y) (as_seq h0 st))
let state_chi_inner m st y =
  let h0 = ST.get() in
  let v0  = get m st 0ul y ^| ((~| (get m st 1ul y)) &| get m st 2ul y) in
  let v1  = get m st 1ul y ^| ((~| (get m st 2ul y)) &| get m st 3ul y) in
  let v2  = get m st 2ul y ^| ((~| (get m st 3ul y)) &| get m st 4ul y) in
  let v3  = get m st 3ul y ^| ((~| (get m st 4ul y)) &| get m st 0ul y) in
  let v4  = get m st 4ul y ^| ((~| (get m st 0ul y)) &| get m st 1ul y) in
  set m st 0ul y v0;
  set m st 1ul y v1;
  set m st 2ul y v2;
  set m st 3ul y v3;
  set m st 4ul y v4;
  let h1 = ST.get() in
  assert (modifies (loc st) h0 h1);
  assert (as_seq h1 st == V.state_chi_inner m (v y) (as_seq h0 st))

inline_for_extraction noextract
val state_chi:
    m:m_spec
  -> s:state_t m
  -> Stack unit
    (requires fun h -> live h s)
    (ensures  fun h0 _ h1 ->
      modifies (loc s) h0 h1 /\
      as_seq h1 s == V.state_chi m (as_seq h0 s))
let state_chi m st =
  let h0 = ST.get() in
  [@ inline_let]
  let spec h0 = V.state_chi_inner m in
  let h0 = ST.get () in
  loop1 h0 5ul st spec
  (fun y ->
     Loop.unfold_repeati 5 (spec h0) (as_seq h0 st) (v y);
     state_chi_inner m st y
   );
  let h1 = ST.get() in
  assert(as_seq h1 st == V.state_chi_equiv m (as_seq h0 st));
  V.state_chi_equivalence m (as_seq h0 st)

inline_for_extraction noextract
val state_iota:
    m:m_spec
  -> s:state_t m
  -> round:size_t{v round < 24}
  -> Stack unit
    (requires fun h -> live h s)
    (ensures  fun h0 _ h1 ->
      modifies (loc s) h0 h1 /\
      as_seq h1 s == V.state_iota m (as_seq h0 s) (v round))
let state_iota m s round =
  recall_contents keccak_rndc Spec.SHA3.Constants.keccak_rndc;
  let c = keccak_rndc.(round) in
  set m s 0ul 0ul (get m s 0ul 0ul ^| (load_element m (secret c)))

private val state_permute:
    m:m_spec
  -> s:state_t m
  -> Stack unit
    (requires fun h -> live h s)
    (ensures  fun h0 _ h1 ->
      modifies (loc s) h0 h1 /\
      as_seq h1 s == V.state_permute m (as_seq h0 s))
let state_permute m s =
  [@ inline_let]
  let spec h0 = V.state_permute1 m in
  let h0 = ST.get () in
  loop1 h0 24ul s spec
  (fun round ->
    Loop.unfold_repeati 24 (spec h0) (as_seq h0 s) (v round);
    state_theta m s;
    state_pi_rho m s;
    state_chi m s;
    state_iota m s round)

inline_for_extraction noextract
val set_wsi: #a:keccak_alg -> #m:m_spec
  -> ws:ws_t m
  -> i:size_t{v i < 32}
  -> b:lbuffer uint8 256ul
  -> bi:size_t{v bi < 32 / (lanes m)} ->
  Stack unit
  (requires fun h -> live h b /\ live h ws /\ disjoint b ws)
  (ensures  fun h0 _ h1 -> modifies (loc ws) h0 h1 /\
    as_seq h1 ws == LSeq.upd (as_seq h0 ws) (v i) (V.load_elementi #a #m (as_seq h0 b) (v bi)))

let set_wsi #a #m ws i b bi =
  [@inline_let]
  let l = lanes m in
  ws.(i) <- vec_load_be (word_t a) l (sub b (bi *! size l *! size (word_length a)) (size l *! size (word_length a)))

noextract
let load_blocks_spec1 (#a:keccak_alg) (#m:m_spec{lanes m == 1}) (b:multiblock_spec a m) : ws_spec m =
  let b = b.(|0|) in
  let ws0 = V.load_elementi #a #m b 0 in
  let ws1 = V.load_elementi #a #m b 1 in
  let ws2 = V.load_elementi #a #m b 2 in
  let ws3 = V.load_elementi #a #m b 3 in
  let ws4 = V.load_elementi #a #m b 4 in
  let ws5 = V.load_elementi #a #m b 5 in
  let ws6 = V.load_elementi #a #m b 6 in
  let ws7 = V.load_elementi #a #m b 7 in
  let ws8 = V.load_elementi #a #m b 8 in
  let ws9 = V.load_elementi #a #m b 9 in
  let ws10 = V.load_elementi #a #m b 10 in
  let ws11 = V.load_elementi #a #m b 11 in
  let ws12 = V.load_elementi #a #m b 12 in
  let ws13 = V.load_elementi #a #m b 13 in
  let ws14 = V.load_elementi #a #m b 14 in
  let ws15 = V.load_elementi #a #m b 15 in
  let ws16 = V.load_elementi #a #m b 16 in
  let ws17 = V.load_elementi #a #m b 17 in
  let ws18 = V.load_elementi #a #m b 18 in
  let ws19 = V.load_elementi #a #m b 19 in
  let ws20 = V.load_elementi #a #m b 20 in
  let ws21 = V.load_elementi #a #m b 21 in
  let ws22 = V.load_elementi #a #m b 22 in
  let ws23 = V.load_elementi #a #m b 23 in
  let ws24 = V.load_elementi #a #m b 24 in
  let ws25 = V.load_elementi #a #m b 25 in
  let ws26 = V.load_elementi #a #m b 26 in
  let ws27 = V.load_elementi #a #m b 27 in
  let ws28 = V.load_elementi #a #m b 28 in
  let ws29 = V.load_elementi #a #m b 29 in
  let ws30 = V.load_elementi #a #m b 30 in
  let ws31 = V.load_elementi #a #m b 31 in
  LSeq.create32 ws0 ws1 ws2 ws3 ws4 ws5 ws6 ws7
           ws8 ws9 ws10 ws11 ws12 ws13 ws14 ws15
           ws16 ws17 ws18 ws19 ws20 ws21 ws22 ws23
           ws24 ws25 ws26 ws27 ws28 ws29 ws30 ws31

noextract
let load_blocks_spec1_lemma (#a:keccak_alg) (#m:m_spec{lanes m == 1}) (b:multiblock_spec a m) :
  Lemma (V.load_blocks b == load_blocks_spec1 b)
 =
  LSeq.eq_intro (V.load_blocks b) (load_blocks_spec1 b)

inline_for_extraction noextract
val set_wsi_1_4: #a:keccak_alg -> #m:m_spec{lanes m == 1}
  -> ws:ws_t m
  -> i:size_t{v i < 32 /\ v (i +! 3ul) < 32}
  -> b:lbuffer uint8 256ul
  -> bi:size_t{v bi < 32 / (lanes m) /\ v (bi +! 3ul) < 32 / (lanes m)} ->
  Stack unit
  (requires fun h -> live h b /\ live h ws /\ disjoint b ws)
  (ensures  fun h0 _ h1 -> modifies (loc ws) h0 h1 /\
    as_seq h1 ws == LSeq.upd (LSeq.upd (LSeq.upd (LSeq.upd (as_seq h0 ws) 
      (v i) (V.load_elementi #a #m (as_seq h0 b) (v bi)))
      (v i + 1) (V.load_elementi #a #m (as_seq h0 b) (v bi + 1)))
      (v i + 2) (V.load_elementi #a #m (as_seq h0 b) (v bi + 2)))
      (v i + 3) (V.load_elementi #a #m (as_seq h0 b) (v bi + 3)))

let set_wsi_1_4 #a #m ws i b bi =
  set_wsi #a #m ws i b bi;
  set_wsi #a #m ws (i+!1ul) b (bi+!1ul);
  set_wsi #a #m ws (i+!2ul) b (bi+!2ul);
  set_wsi #a #m ws (i+!3ul) b (bi+!3ul)

inline_for_extraction noextract
val load_blocks1: #a:keccak_alg -> #m:m_spec{lanes m == 1}
  -> b:multibuf (lanes m) 256ul
  -> ws:ws_t m ->
  Stack unit
  (requires fun h -> live_multi h b /\ live h ws /\ disjoint_multi b ws)
  (ensures  fun h0 _ h1 -> modifies (loc ws) h0 h1 /\
    as_seq h1 ws == V.load_blocks #a #m (as_seq_multi h0 b))

let load_blocks1 #a #m ib ws =
  (*let h0 = ST.get() in
  let b = ib.(|0|) in
  set_wsi_1_4 #a #m ws 0ul b 0ul;
  set_wsi_1_4 #a #m ws 4ul b 4ul;
  set_wsi_1_4 #a #m ws 8ul b 8ul;
  set_wsi_1_4 #a #m ws 12ul b 12ul;
  set_wsi_1_4 #a #m ws 16ul b 16ul;
  set_wsi_1_4 #a #m ws 20ul b 20ul;
  set_wsi_1_4 #a #m ws 24ul b 24ul;
  set_wsi_1_4 #a #m ws 28ul b 28ul;
  let h1 = ST.get() in
  assert (modifies (loc ws) h0 h1);
  LSeq.eq_intro (as_seq h1 ws) (load_blocks_spec1 #a #m (as_seq_multi h0 ib));
  load_blocks_spec1_lemma #a #m (as_seq_multi h0 ib);
  assert (as_seq h1 ws == load_blocks_spec1 #a #m (as_seq_multi h0 ib));
  assert (as_seq h1 ws == V.load_blocks #a #m (as_seq_multi h0 ib));*)
  admit()

noextract
let load_blocks_spec4 (#a:keccak_alg) (#m:m_spec{lanes m == 4}) (b:multiblock_spec a m) : ws_spec m =
  let b0 = b.(|0|) in
  let b1 = b.(|1|) in
  let b2 = b.(|2|) in
  let b3 = b.(|3|) in
  let ws0 = V.load_elementi #a #m b0 0 in
  let ws1 = V.load_elementi #a #m b1 0 in
  let ws2 = V.load_elementi #a #m b2 0 in
  let ws3 = V.load_elementi #a #m b3 0 in
  let ws4 = V.load_elementi #a #m b0 1 in
  let ws5 = V.load_elementi #a #m b1 1 in
  let ws6 = V.load_elementi #a #m b2 1 in
  let ws7 = V.load_elementi #a #m b3 1 in
  let ws8 = V.load_elementi #a #m b0 2 in
  let ws9 = V.load_elementi #a #m b1 2 in
  let ws10 = V.load_elementi #a #m b2 2 in
  let ws11 = V.load_elementi #a #m b3 2 in
  let ws12 = V.load_elementi #a #m b0 3 in
  let ws13 = V.load_elementi #a #m b1 3 in
  let ws14 = V.load_elementi #a #m b2 3 in
  let ws15 = V.load_elementi #a #m b3 3 in
  let ws16 = V.load_elementi #a #m b0 4 in
  let ws17 = V.load_elementi #a #m b1 4 in
  let ws18 = V.load_elementi #a #m b2 4 in
  let ws19 = V.load_elementi #a #m b3 4 in
  let ws20 = V.load_elementi #a #m b0 5 in
  let ws21 = V.load_elementi #a #m b1 5 in
  let ws22 = V.load_elementi #a #m b2 5 in
  let ws23 = V.load_elementi #a #m b3 5 in
  let ws24 = V.load_elementi #a #m b0 6 in
  let ws25 = V.load_elementi #a #m b1 6 in
  let ws26 = V.load_elementi #a #m b2 6 in
  let ws27 = V.load_elementi #a #m b3 6 in
  let ws28 = V.load_elementi #a #m b0 7 in
  let ws29 = V.load_elementi #a #m b1 7 in
  let ws30 = V.load_elementi #a #m b2 7 in
  let ws31 = V.load_elementi #a #m b3 7 in
  LSeq.create32 ws0 ws1 ws2 ws3 ws4 ws5 ws6 ws7
           ws8 ws9 ws10 ws11 ws12 ws13 ws14 ws15
           ws16 ws17 ws18 ws19 ws20 ws21 ws22 ws23
           ws24 ws25 ws26 ws27 ws28 ws29 ws30 ws31

noextract
let load_blocks_spec4_lemma (#a:keccak_alg) (#m:m_spec{lanes m == 4}) (b:multiblock_spec a m) :
  Lemma (V.load_blocks b == load_blocks_spec4 b)
 =
  LSeq.eq_intro (V.load_blocks b) (load_blocks_spec4 b)

inline_for_extraction noextract
val set_wsi_4_4: #a:keccak_alg -> #m:m_spec{lanes m == 4}
  -> ws:ws_t m
  -> i:size_t{v i < 32 /\ v (i +! 3ul) < 32}
  -> b0:lbuffer uint8 256ul
  -> b1:lbuffer uint8 256ul
  -> b2:lbuffer uint8 256ul
  -> b3:lbuffer uint8 256ul
  -> bi:size_t{v bi < 32 / (lanes m)} ->
  Stack unit
  (requires fun h -> live h b0 /\ live h b1 /\ live h b2 /\ live h b3 /\
    live h ws /\ disjoint b0 ws /\ disjoint b1 ws /\ disjoint b2 ws /\ disjoint b3 ws)
  (ensures  fun h0 _ h1 -> modifies (loc ws) h0 h1 /\
    as_seq h1 ws == LSeq.upd (LSeq.upd (LSeq.upd (LSeq.upd (as_seq h0 ws) 
      (v i) (V.load_elementi #a #m (as_seq h0 b0) (v bi)))
      (v i + 1) (V.load_elementi #a #m (as_seq h0 b1) (v bi)))
      (v i + 2) (V.load_elementi #a #m (as_seq h0 b2) (v bi)))
      (v i + 3) (V.load_elementi #a #m (as_seq h0 b3) (v bi)))

let set_wsi_4_4 #a #m ws i b0 b1 b2 b3 bi =
  set_wsi #a #m ws i b0 bi;
  set_wsi #a #m ws (i+!1ul) b1 bi;
  set_wsi #a #m ws (i+!2ul) b2 bi;
  set_wsi #a #m ws (i+!3ul) b3 bi

inline_for_extraction noextract
val load_blocks4: #a:keccak_alg -> #m:m_spec{lanes m == 4}
  -> b:multibuf (lanes m) 256ul
  -> ws:ws_t m ->
  Stack unit
  (requires fun h -> live_multi h b /\ live h ws /\ disjoint_multi b ws)
  (ensures  fun h0 _ h1 -> modifies (loc ws) h0 h1 /\
    as_seq h1 ws == V.load_blocks #a #m (as_seq_multi h0 b))

let load_blocks4 #a #m ib ws =
  (*let h0 = ST.get() in
  let (b0,(b1,(b2,b3))) = tup4 ib in
  set_wsi_4_4 #a #m ws 0ul b0 b1 b2 b3 0ul;
  set_wsi_4_4 #a #m ws 4ul b0 b1 b2 b3 1ul;
  set_wsi_4_4 #a #m ws 8ul b0 b1 b2 b3 2ul;
  set_wsi_4_4 #a #m ws 12ul b0 b1 b2 b3 3ul;
  set_wsi_4_4 #a #m ws 16ul b0 b1 b2 b3 4ul;
  set_wsi_4_4 #a #m ws 20ul b0 b1 b2 b3 5ul;
  set_wsi_4_4 #a #m ws 24ul b0 b1 b2 b3 6ul;
  set_wsi_4_4 #a #m ws 28ul b0 b1 b2 b3 7ul;
  let h1 = ST.get() in
  assert (modifies (loc ws) h0 h1);
  LSeq.eq_intro (as_seq h1 ws) (load_blocks_spec4 #a #m (as_seq_multi h0 ib));
  load_blocks_spec4_lemma #a #m (as_seq_multi h0 ib);
  assert (as_seq h1 ws == load_blocks_spec4 #a #m (as_seq_multi h0 ib));
  assert (as_seq h1 ws == V.load_blocks #a #m (as_seq_multi h0 ib));*)
  admit();
  ()

inline_for_extraction noextract
val load_blocks: #a:keccak_alg -> #m:m_spec{is_supported m}
  -> b:multibuf (lanes m) 256ul
  -> ws:ws_t m ->
  Stack unit
  (requires fun h -> live_multi h b /\ live h ws /\ disjoint_multi b ws)
  (ensures  fun h0 _ h1 -> modifies (loc ws) h0 h1 /\
    as_seq h1 ws == V.load_blocks #a #m (as_seq_multi h0 b))

let load_blocks #a #m b ws =
  match lanes m with
  | 1 -> load_blocks1 #a #m b ws
  | 4 -> load_blocks4 #a #m b ws

inline_for_extraction noextract
val transpose_ws4:
    #m:m_spec{lanes m == 4}
  -> ws:ws_t m
  -> Stack unit
    (requires fun h -> live h ws)
    (ensures  fun h0 _ h1 -> modifies (loc ws) h0 h1 /\
      as_seq h1 ws == V.transpose_ws (as_seq h0 ws))

let transpose_ws4 #m ws =
  let (ws0,ws1,ws2,ws3) =
    transpose4x4 (ws.(0ul),ws.(1ul),ws.(2ul),ws.(3ul)) in
  let (ws4,ws5,ws6,ws7) =
    transpose4x4 (ws.(4ul),ws.(5ul),ws.(6ul),ws.(7ul)) in
  let (ws8,ws9,ws10,ws11) =
    transpose4x4 (ws.(8ul),ws.(9ul),ws.(10ul),ws.(11ul)) in
  let (ws12,ws13,ws14,ws15) =
    transpose4x4 (ws.(12ul),ws.(13ul),ws.(14ul),ws.(15ul)) in
  let (ws16,ws17,ws18,ws19) =
    transpose4x4 (ws.(16ul),ws.(17ul),ws.(18ul),ws.(19ul)) in
  let (ws20,ws21,ws22,ws23) =
    transpose4x4 (ws.(20ul),ws.(21ul),ws.(22ul),ws.(23ul)) in
  let (ws24,ws25,ws26,ws27) =
    transpose4x4 (ws.(24ul),ws.(25ul),ws.(26ul),ws.(27ul)) in
  let (ws28,ws29,ws30,ws31) =
    transpose4x4 (ws.(28ul),ws.(29ul),ws.(30ul),ws.(31ul)) in
  create32 ws ws0 ws1 ws2 ws3 ws4 ws5 ws6 ws7 ws8 ws9 ws10 ws11 ws12 ws13 ws14 ws15
    ws16 ws17 ws18 ws19 ws20 ws21 ws22 ws23 ws24 ws25 ws26 ws27 ws28 ws29 ws30 ws31

inline_for_extraction noextract
val transpose_ws: #m:m_spec{is_supported m} -> ws:ws_t m ->
  Stack unit
  (requires fun h -> live h ws)
  (ensures  fun h0 _ h1 -> modifies (loc ws) h0 h1 /\
    as_seq h1 ws == V.transpose_ws (as_seq h0 ws))

let transpose_ws #m ws =
  match lanes m with
  | 1 -> ()
  | 4 -> transpose_ws4 ws

inline_for_extraction noextract
val load_ws: #a:keccak_alg -> #m:m_spec{is_supported m}
  -> b:multibuf (lanes m) 256ul
  -> ws:ws_t m ->
  Stack unit
  (requires fun h -> live_multi h b /\ live h ws /\ disjoint_multi b ws)
  (ensures  fun h0 _ h1 -> modifies (loc ws) h0 h1 /\
    as_seq h1 ws == V.load_ws #a #m (as_seq_multi h0 b))

let load_ws #a #m b ws =
  load_blocks #a #m b ws;
  transpose_ws ws

inline_for_extraction noextract
val loadState: #a:keccak_alg -> #m:m_spec{is_supported m}
  -> b:multibuf (lanes m) 256ul
  -> s:state_t m ->
  Stack unit
  (requires fun h -> live_multi h b /\ live h s /\ disjoint_multi b s)
  (ensures  fun h0 _ h1 -> modifies (loc s) h0 h1 /\
    as_seq h1 s == V.loadState #a #m (as_seq_multi h0 b) (as_seq h0 s))

let loadState #a #m b s =
  let init_h0 = ST.get() in
  push_frame ();
  let ws = create 32ul (zero_element m) in
  let h0 = ST.get() in
  Lib.NTuple.eq_intro (as_seq_multi h0 b) (as_seq_multi init_h0 b);
  load_ws #a #m b ws;
  let h1 = ST.get() in
  loop1 h1 25ul s
  (fun h -> V.loadState_inner m (as_seq h1 ws))
  (fun i ->
    Lib.LoopCombinators.unfold_repeati 25 (V.loadState_inner m (as_seq h1 ws)) (as_seq h1 s) (v i);
    s.(i) <- s.(i) ^| ws.(i));
  pop_frame()

inline_for_extraction noextract
val storeState: #a:keccak_alg -> #m:m_spec{is_supported m}
  -> s:state_t m
  -> hbuf:lbuffer uint8 (size (lanes m) *! 32ul *! size (word_length a)) ->
  Stack unit
  (requires fun h -> live h hbuf /\ live h s /\ disjoint hbuf s /\
    as_seq h hbuf == LSeq.create (lanes m * 32 * word_length a) (u8 0))
  (ensures  fun h0 _ h1 -> modifies (loc hbuf) h0 h1 /\
    as_seq h1 hbuf == V.storeState #a #m (as_seq h0 s))

let storeState #a #m s hbuf =
  push_frame ();
  let ws = create 32ul (zero_element m) in
  update_sub ws 0ul 25ul s;
  transpose_ws ws;
  Lib.IntVector.Serialize.vecs_store_be hbuf ws;
  pop_frame()

inline_for_extraction noextract
val next_blocks:
  rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 256}
  -> nextBlock:lbuffer uint8 256ul ->
  Stack unit
  (requires fun h -> live h nextBlock /\
    as_seq h nextBlock == LSeq.create 256 (u8 0))
  (ensures  fun h0 _ h1 -> modifies (loc nextBlock) h0 h1 /\
    as_seq h1 nextBlock == V.next_blocks (v rateInBytes) (as_seq h0 nextBlock))

let next_blocks rateInBytes nextBlock =
  nextBlock.(rateInBytes -! 1ul) <- u8 0x80

inline_for_extraction noextract
val next_block1: #m:m_spec{lanes m == 1}
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 256}
  -> b:multibuf (lanes m) 256ul ->
  Stack unit
  (requires fun h -> live_multi h b /\
    as_seq_multi h b == next_block_seq_zero m)
  (ensures  fun h0 _ h1 ->
    as_seq_multi h1 b == V.next_block #m (v rateInBytes) (as_seq_multi h0 b))

let next_block1 #m rateInBytes b =
  let h0 = ST.get() in
  let b0 = b.(|0|) in
  next_blocks rateInBytes b0;
  let h1 = ST.get() in
  Lib.NTuple.eq_intro (as_seq_multi h1 b) 
    (V.next_block1 #m (v rateInBytes) (as_seq_multi h0 b))

inline_for_extraction noextract
val next_block4: #m:m_spec{lanes m == 4}
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 256}
  -> b:multibuf (lanes m) 256ul ->
  Stack unit
  (requires fun h -> live_multi h b /\ internally_disjoint b /\ 
    as_seq_multi h b == next_block_seq_zero m)
  (ensures  fun h0 _ h1 ->
    as_seq_multi h1 b == V.next_block #m (v rateInBytes) (as_seq_multi h0 b))

let next_block4 #m rateInBytes b =
  let h0 = ST.get() in
  let (b0,(b1,(b2,b3))) = tup4 b in
  assert (internally_disjoint4 b0 b1 b2 b3);
  next_blocks rateInBytes b0;
  next_blocks rateInBytes b1;
  next_blocks rateInBytes b2;
  next_blocks rateInBytes b3;
  let h1 = ST.get() in
  Lib.NTuple.eq_intro (as_seq_multi h1 b) 
    (V.next_block4 #m (v rateInBytes) (as_seq_multi h0 b))

inline_for_extraction noextract
val next_block: #m:m_spec{is_supported m}
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 256}
  -> b:multibuf (lanes m) 256ul ->
  Stack unit
  (requires fun h -> live_multi h b /\ internally_disjoint b /\ 
    as_seq_multi h b == next_block_seq_zero m)
  (ensures  fun h0 _ h1 ->
    as_seq_multi h1 b == V.next_block #m (v rateInBytes) (as_seq_multi h0 b))

let next_block #m rateInBytes b =
  match lanes m with
  | 1 -> next_block1 #m rateInBytes b
  | 4 -> next_block4 #m rateInBytes b

inline_for_extraction noextract
val alloc_multi1: m:m_spec{lanes m == 1} ->
  StackInline (multibuf (lanes m) 256ul)
  (requires fun h -> True)
  (ensures  fun h0 b h1 -> live_multi h1 b /\
    stack_allocated_multi b h0 h1 (Seq.create 256 (u8 0)) /\
    as_seq_multi h1 b == next_block_seq_zero m)

let alloc_multi1 m =
  let b = create 256ul (u8 0) in
  let b = ntup1 b in
  let h0 = ST.get() in
  Lib.NTuple.eq_intro (as_seq_multi h0 b) (next_block_seq_zero m);
  b

module B = LowStar.Buffer

inline_for_extraction noextract
val alloc_multi4: m:m_spec{lanes m == 4} ->
  StackInline (multibuf (lanes m) 256ul)
  (requires fun h -> True)
  (ensures  fun h0 b h1 -> live_multi h1 b /\ internally_disjoint b /\
    stack_allocated_multi b h0 h1 (Seq.create 256 (u8 0)) /\
    as_seq_multi h1 b == next_block_seq_zero m)

let alloc_multi4 m =
  let b0 = create 256ul (u8 0) in
  let b1 = create 256ul (u8 0) in
  let b2 = create 256ul (u8 0) in
  let b3 = create 256ul (u8 0) in
  let b = ntup4 (b0, (b1, (b2, b3))) in
  let h0 = ST.get() in
  Lib.NTuple.eq_intro (as_seq_multi h0 b) (next_block_seq_zero m);
  admit(); //Can't prove stack_allocated_multi b h0 h1 (Seq.create 256 (u8 0))
  b

inline_for_extraction noextract
val alloc_multi: m:m_spec{is_supported m} ->
  StackInline (multibuf (lanes m) 256ul)
  (requires fun h -> True)
  (ensures  fun h0 b h1 -> live_multi h1 b /\ internally_disjoint b /\
    stack_allocated_multi b h0 h1 (Seq.create 256 (u8 0)) /\
    as_seq_multi h1 b == next_block_seq_zero m)

let alloc_multi m =
  match lanes m with
  | 1 -> alloc_multi1 m
  | 4 -> alloc_multi4 m

inline_for_extraction noextract
val absorb_next: #a:keccak_alg -> #m:m_spec{is_supported m}
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 256}
  -> s:state_t m ->
  Stack unit
  (requires fun h -> live h s)
  (ensures  fun h0 _ h1 ->
    as_seq h1 s == V.absorb_next #a #m (v rateInBytes) (as_seq h0 s))

let absorb_next #a #m rateInBytes s =
  push_frame ();
  let b = alloc_multi m in
  next_block #m rateInBytes b;
  loadState #a #m b s;
  state_permute m s;
  pop_frame()
