module Hacl.Impl.SHA3.Vec

open FStar.Mul
open Lib.Sequence
open Lib.IntVector
open Lib.IntVector.Transpose

open LowStar.Buffer
open Lib.Buffer

open Spec.SHA3.Constants

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module Loop = Lib.LoopCombinators
module V = Hacl.Spec.SHA3.Vec

inline_for_extraction noextract
let disjoint4_4 #len1 #len2 #a (b0 b1 b2 b3: lbuffer a len1) (b4 b5 b6 b7: lbuffer a len2) =
  disjoint b0 b4 /\ disjoint b0 b5 /\ disjoint b0 b6 /\ disjoint b0 b7 /\
  disjoint b1 b4 /\ disjoint b1 b5 /\ disjoint b1 b6 /\ disjoint b1 b7 /\
  disjoint b2 b4 /\ disjoint b2 b5 /\ disjoint b2 b6 /\ disjoint b2 b7 /\
  disjoint b3 b4 /\ disjoint b3 b5 /\ disjoint b3 b6 /\ disjoint b3 b7

let keccak_rotc :x:glbuffer rotc_t 24ul{witnessed x keccak_rotc /\ recallable x}
  = createL_global rotc_list

let keccak_piln :x:glbuffer piln_t 24ul{witnessed x keccak_piln /\ recallable x}
  = createL_global piln_list

let keccak_rndc :x:glbuffer pub_uint64 24ul{witnessed x keccak_rndc /\ recallable x}
  = createL_global rndc_list

#set-options "--z3rlimit 80 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let ws_t (m:m_spec) = lbuffer (element_t m) 32ul

inline_for_extraction noextract
let index_t = n:size_t{v n < 5}

inline_for_extraction noextract
val get:
    m:m_spec
  -> s:state_t m
  -> x:index_t
  -> y:index_t
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
  -> x:index_t
  -> y:index_t
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
  -> x:index_t
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
      as_seq h1 s == V.state_theta1 m (as_seq h0 _C) (as_seq h0 s))

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

private noextract
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
  let refl h i : GTot ((element_t m) & (V.state_spec m)) = bget h current 0, as_seq h s in
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
  -> y:index_t
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

inline_for_extraction noextract
val state_permute:
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
val set_wsi: #m:m_spec
  -> ws:ws_t m
  -> i:size_t{v i < 32}
  -> b:lbuffer uint8 256ul
  -> bi:size_t{v bi < 32 / (lanes m)} ->
  Stack unit
  (requires fun h -> live h b /\ live h ws /\ disjoint b ws)
  (ensures  fun h0 _ h1 -> modifies (loc ws) h0 h1 /\
    as_seq h1 ws == LSeq.upd (as_seq h0 ws) (v i) (V.load_elementi #m (as_seq h0 b) (v bi)))

let set_wsi #m ws i b bi =
  [@inline_let]
  let l = lanes m in
  ws.(i) <- vec_load_le U64 l (sub b (bi *! size l *! 8ul) (size l *! 8ul))

noextract
let load_blocks_spec1 (#m:m_spec{m == M32}) (b:V.multiblock_spec m) : V.ws_spec m =
  let b = b.(|0|) in
  let ws0 = V.load_elementi #m b 0 in
  let ws1 = V.load_elementi #m b 1 in
  let ws2 = V.load_elementi #m b 2 in
  let ws3 = V.load_elementi #m b 3 in
  let ws4 = V.load_elementi #m b 4 in
  let ws5 = V.load_elementi #m b 5 in
  let ws6 = V.load_elementi #m b 6 in
  let ws7 = V.load_elementi #m b 7 in
  let ws8 = V.load_elementi #m b 8 in
  let ws9 = V.load_elementi #m b 9 in
  let ws10 = V.load_elementi #m b 10 in
  let ws11 = V.load_elementi #m b 11 in
  let ws12 = V.load_elementi #m b 12 in
  let ws13 = V.load_elementi #m b 13 in
  let ws14 = V.load_elementi #m b 14 in
  let ws15 = V.load_elementi #m b 15 in
  let ws16 = V.load_elementi #m b 16 in
  let ws17 = V.load_elementi #m b 17 in
  let ws18 = V.load_elementi #m b 18 in
  let ws19 = V.load_elementi #m b 19 in
  let ws20 = V.load_elementi #m b 20 in
  let ws21 = V.load_elementi #m b 21 in
  let ws22 = V.load_elementi #m b 22 in
  let ws23 = V.load_elementi #m b 23 in
  let ws24 = V.load_elementi #m b 24 in
  let ws25 = V.load_elementi #m b 25 in
  let ws26 = V.load_elementi #m b 26 in
  let ws27 = V.load_elementi #m b 27 in
  let ws28 = V.load_elementi #m b 28 in
  let ws29 = V.load_elementi #m b 29 in
  let ws30 = V.load_elementi #m b 30 in
  let ws31 = V.load_elementi #m b 31 in
  LSeq.create32 ws0 ws1 ws2 ws3 ws4 ws5 ws6 ws7
           ws8 ws9 ws10 ws11 ws12 ws13 ws14 ws15
           ws16 ws17 ws18 ws19 ws20 ws21 ws22 ws23
           ws24 ws25 ws26 ws27 ws28 ws29 ws30 ws31

noextract
let load_blocks_spec1_lemma (#m:m_spec{m == M32}) (b:V.multiblock_spec m) :
  Lemma (V.load_blocks b == load_blocks_spec1 b)
 =
  LSeq.eq_intro (V.load_blocks b) (load_blocks_spec1 b)

inline_for_extraction noextract
val set_wsi_1_4: #m:m_spec{m == M32}
  -> ws:ws_t m
  -> i:size_t{v i < 32 /\ v (i +! 3ul) < 32}
  -> b:lbuffer uint8 256ul
  -> bi:size_t{v bi < 32 / (lanes m) /\ v (bi +! 3ul) < 32 / (lanes m)} ->
  Stack unit
  (requires fun h -> live h b /\ live h ws /\ disjoint b ws)
  (ensures  fun h0 _ h1 -> modifies (loc ws) h0 h1 /\
    (let ws1 = as_seq h1 ws in
     let ws0 = as_seq h0 ws in
     ws1.[v i + 0] == V.load_elementi #m (as_seq h0 b) (v bi + 0) /\
     ws1.[v i + 1] == V.load_elementi #m (as_seq h0 b) (v bi + 1) /\
     ws1.[v i + 2] == V.load_elementi #m (as_seq h0 b) (v bi + 2) /\
     ws1.[v i + 3] == V.load_elementi #m (as_seq h0 b) (v bi + 3) /\
     (forall (j: nat). j < v i ==> ws1.[j] == ws0.[j]) /\
     (forall (j: nat). j >= v i + 4 /\ j < 32 ==> ws1.[j] == ws0.[j])))

let set_wsi_1_4 #m ws i b bi =
  set_wsi #m ws i b bi;
  set_wsi #m ws (i+!1ul) b (bi+!1ul);
  set_wsi #m ws (i+!2ul) b (bi+!2ul);
  set_wsi #m ws (i+!3ul) b (bi+!3ul)

inline_for_extraction noextract
val load_blocks1: #m:m_spec{m == M32}
  -> b:multibuf (lanes m) 256ul
  -> ws:ws_t m ->
  Stack unit
  (requires fun h -> live_multi h b /\ live h ws /\ disjoint_multi b ws)
  (ensures  fun h0 _ h1 -> modifies (loc ws) h0 h1 /\
    as_seq h1 ws == V.load_blocks #m (as_seq_multi h0 b))

#push-options "--max_fuel 1 --z3rlimit 200"
let load_blocks1 #m ib ws =
  let h0 = ST.get() in
  assert (v (0ul +! 3ul) == 3);
  assert (v (4ul +! 3ul) == 7);
  assert (v (8ul +! 3ul) == 11);
  assert (v (12ul +! 3ul) == 15);
  assert (v (16ul +! 3ul) == 19);
  assert (v (20ul +! 3ul) == 23);
  assert (v (24ul +! 3ul) == 27);
  assert (v (28ul +! 3ul) == 31);
  let b = tup1 ib in
  set_wsi_1_4 #m ws 0ul b 0ul;
  set_wsi_1_4 #m ws 4ul b 4ul;
  set_wsi_1_4 #m ws 8ul b 8ul;
  set_wsi_1_4 #m ws 12ul b 12ul;
  set_wsi_1_4 #m ws 16ul b 16ul;
  set_wsi_1_4 #m ws 20ul b 20ul;
  set_wsi_1_4 #m ws 24ul b 24ul;
  set_wsi_1_4 #m ws 28ul b 28ul;
  let h1 = ST.get() in
  assert (modifies (loc ws) h0 h1);
  LSeq.eq_intro (as_seq h1 ws) (load_blocks_spec1 #m (as_seq_multi h0 ib));
  load_blocks_spec1_lemma #m (as_seq_multi h0 ib);
  assert (as_seq h1 ws == load_blocks_spec1 #m (as_seq_multi h0 ib));
  assert (as_seq h1 ws == V.load_blocks #m (as_seq_multi h0 ib))
#pop-options

noextract
let load_blocks_spec4 (#m:m_spec{m == M256}) (b:V.multiblock_spec m) : V.ws_spec m =
  let b0 = b.(|0|) in
  let b1 = b.(|1|) in
  let b2 = b.(|2|) in
  let b3 = b.(|3|) in
  let ws0 = V.load_elementi #m b0 0 in
  let ws1 = V.load_elementi #m b1 0 in
  let ws2 = V.load_elementi #m b2 0 in
  let ws3 = V.load_elementi #m b3 0 in
  let ws4 = V.load_elementi #m b0 1 in
  let ws5 = V.load_elementi #m b1 1 in
  let ws6 = V.load_elementi #m b2 1 in
  let ws7 = V.load_elementi #m b3 1 in
  let ws8 = V.load_elementi #m b0 2 in
  let ws9 = V.load_elementi #m b1 2 in
  let ws10 = V.load_elementi #m b2 2 in
  let ws11 = V.load_elementi #m b3 2 in
  let ws12 = V.load_elementi #m b0 3 in
  let ws13 = V.load_elementi #m b1 3 in
  let ws14 = V.load_elementi #m b2 3 in
  let ws15 = V.load_elementi #m b3 3 in
  let ws16 = V.load_elementi #m b0 4 in
  let ws17 = V.load_elementi #m b1 4 in
  let ws18 = V.load_elementi #m b2 4 in
  let ws19 = V.load_elementi #m b3 4 in
  let ws20 = V.load_elementi #m b0 5 in
  let ws21 = V.load_elementi #m b1 5 in
  let ws22 = V.load_elementi #m b2 5 in
  let ws23 = V.load_elementi #m b3 5 in
  let ws24 = V.load_elementi #m b0 6 in
  let ws25 = V.load_elementi #m b1 6 in
  let ws26 = V.load_elementi #m b2 6 in
  let ws27 = V.load_elementi #m b3 6 in
  let ws28 = V.load_elementi #m b0 7 in
  let ws29 = V.load_elementi #m b1 7 in
  let ws30 = V.load_elementi #m b2 7 in
  let ws31 = V.load_elementi #m b3 7 in
  LSeq.create32 ws0 ws1 ws2 ws3 ws4 ws5 ws6 ws7
           ws8 ws9 ws10 ws11 ws12 ws13 ws14 ws15
           ws16 ws17 ws18 ws19 ws20 ws21 ws22 ws23
           ws24 ws25 ws26 ws27 ws28 ws29 ws30 ws31

noextract
let load_blocks_spec4_lemma (#m:m_spec{m == M256}) (b:V.multiblock_spec m) :
  Lemma (V.load_blocks b == load_blocks_spec4 b)
 =
  LSeq.eq_intro (V.load_blocks b) (load_blocks_spec4 b)

inline_for_extraction noextract
val set_wsi_4_4: #m:m_spec{m == M256}
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
    (let ws1 = as_seq h1 ws in
     let ws0 = as_seq h0 ws in
     ws1.[v i + 0] == V.load_elementi #m (as_seq h0 b0) (v bi) /\
     ws1.[v i + 1] == V.load_elementi #m (as_seq h0 b1) (v bi) /\
     ws1.[v i + 2] == V.load_elementi #m (as_seq h0 b2) (v bi) /\
     ws1.[v i + 3] == V.load_elementi #m (as_seq h0 b3) (v bi) /\
     (forall (j: nat). j < v i ==> ws1.[j] == ws0.[j]) /\
     (forall (j: nat). j >= v i + 4 /\ j < 32 ==> ws1.[j] == ws0.[j])))

let set_wsi_4_4 #m ws i b0 b1 b2 b3 bi =
  set_wsi #m ws i b0 bi;
  set_wsi #m ws (i+!1ul) b1 bi;
  set_wsi #m ws (i+!2ul) b2 bi;
  set_wsi #m ws (i+!3ul) b3 bi

inline_for_extraction noextract
val load_blocks4: #m:m_spec{m == M256}
  -> b:multibuf (lanes m) 256ul
  -> ws:ws_t m ->
  Stack unit
  (requires fun h -> live_multi h b /\ live h ws /\ disjoint_multi b ws)
  (ensures  fun h0 _ h1 -> modifies (loc ws) h0 h1 /\
    as_seq h1 ws == V.load_blocks #m (as_seq_multi h0 b))

#push-options "--max_fuel 1 --z3rlimit 200"
let load_blocks4 #m ib ws =
  let h0 = ST.get() in
  assert (v (0ul +! 3ul) == 3);
  assert (v (4ul +! 3ul) == 7);
  assert (v (8ul +! 3ul) == 11);
  assert (v (12ul +! 3ul) == 15);
  assert (v (16ul +! 3ul) == 19);
  assert (v (20ul +! 3ul) == 23);
  assert (v (24ul +! 3ul) == 27);
  assert (v (28ul +! 3ul) == 31);
  let (b0,(b1,(b2,b3))) = tup4 ib in
  set_wsi_4_4 #m ws 0ul b0 b1 b2 b3 0ul;
  set_wsi_4_4 #m ws 4ul b0 b1 b2 b3 1ul;
  set_wsi_4_4 #m ws 8ul b0 b1 b2 b3 2ul;
  set_wsi_4_4 #m ws 12ul b0 b1 b2 b3 3ul;
  set_wsi_4_4 #m ws 16ul b0 b1 b2 b3 4ul;
  set_wsi_4_4 #m ws 20ul b0 b1 b2 b3 5ul;
  set_wsi_4_4 #m ws 24ul b0 b1 b2 b3 6ul;
  set_wsi_4_4 #m ws 28ul b0 b1 b2 b3 7ul;
  let h1 = ST.get() in
  assert (modifies (loc ws) h0 h1);
  LSeq.eq_intro (as_seq h1 ws) (load_blocks_spec4 #m (as_seq_multi h0 ib));
  load_blocks_spec4_lemma #m (as_seq_multi h0 ib);
  assert (as_seq h1 ws == load_blocks_spec4 #m (as_seq_multi h0 ib));
  assert (as_seq h1 ws == V.load_blocks #m (as_seq_multi h0 ib));
  ()
#pop-options

inline_for_extraction noextract
val load_blocks: #m:m_spec
  -> b:multibuf (lanes m) 256ul
  -> ws:ws_t m ->
  Stack unit
  (requires fun h -> live_multi h b /\ live h ws /\ disjoint_multi b ws)
  (ensures  fun h0 _ h1 -> modifies (loc ws) h0 h1 /\
    as_seq h1 ws == V.load_blocks #m (as_seq_multi h0 b))

let load_blocks #m b ws =
  match m with
  | M32 -> load_blocks1 #m b ws
  | M256 -> load_blocks4 #m b ws

inline_for_extraction noextract
val transpose_ws4:
    #m:m_spec{m == M256}
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
val transpose_ws: #m:m_spec -> ws:ws_t m ->
  Stack unit
  (requires fun h -> live h ws)
  (ensures  fun h0 _ h1 -> modifies (loc ws) h0 h1 /\
    as_seq h1 ws == V.transpose_ws (as_seq h0 ws))

let transpose_ws #m ws =
  match m with
  | M32 -> ()
  | M256 -> transpose_ws4 ws

inline_for_extraction noextract
val load_ws: #m:m_spec
  -> b:multibuf (lanes m) 256ul
  -> ws:ws_t m ->
  Stack unit
  (requires fun h -> live_multi h b /\ live h ws /\ disjoint_multi b ws)
  (ensures  fun h0 _ h1 -> modifies (loc ws) h0 h1 /\
    as_seq h1 ws == V.load_ws #m (as_seq_multi h0 b))

let load_ws #m b ws =
  load_blocks #m b ws;
  transpose_ws ws

inline_for_extraction noextract
val loadState: #m:m_spec
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> b:multibuf (lanes m) 256ul
  -> s:state_t m ->
  Stack unit
  (requires fun h -> live_multi h b /\ live h s /\ disjoint_multi b s /\
    (forall l. l < lanes m ==> (forall i. (i >= v rateInBytes /\ i < 256) ==>
      Seq.index (as_seq_multi h b).(|l|) i == u8 0)))
  (ensures  fun h0 _ h1 -> modifies (loc s) h0 h1 /\
    as_seq h1 s == V.loadState #m (v rateInBytes) (as_seq_multi h0 b) (as_seq h0 s))

let loadState #m rateInBytes b s =
  let init_h0 = ST.get() in
  push_frame ();
  let h0_f = ST.get() in
  let ws = create 32ul (zero_element m) in
  let h0 = ST.get() in
  Lib.NTuple.eq_intro (as_seq_multi h0 b) (as_seq_multi init_h0 b);
  load_ws #m b ws;
  let h1 = ST.get() in
  loop1 h1 25ul s
  (fun h -> V.loadState_inner m (as_seq h1 ws))
  (fun i ->
    Lib.LoopCombinators.unfold_repeati 25 (V.loadState_inner m (as_seq h1 ws)) (as_seq h1 s) (v i);
    s.(i) <- s.(i) ^| ws.(i));
  let h1_f = ST.get() in
  pop_frame();
  let h1 = ST.get() in
  fresh_frame_modifies init_h0 h0_f;
  popped_modifies h1_f h1;
  modifies_remove_fresh_frame init_h0 h0_f h1 (loc s)

inline_for_extraction noextract
val transpose_s_ws4:
    #m:m_spec{m == M256}
  -> ws:ws_t m
  -> Stack unit
    (requires fun h -> live h ws)
    (ensures  fun h0 _ h1 -> modifies (loc ws) h0 h1 /\
      as_seq h1 ws == V.transpose_s_ws (as_seq h0 ws))

let transpose_s_ws4 #m ws =
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
  create32 ws ws0 ws4 ws8 ws12 ws16 ws20 ws24 ws28 ws1 ws5 ws9 ws13 ws17 ws21 ws25
    ws29 ws2 ws6 ws10 ws14 ws18 ws22 ws26 ws30 ws3 ws7 ws11 ws15 ws19 ws23 ws27 ws31

inline_for_extraction noextract
val transpose_s_ws: #m:m_spec -> ws:ws_t m ->
  Stack unit
  (requires fun h -> live h ws)
  (ensures  fun h0 _ h1 -> modifies (loc ws) h0 h1 /\
    as_seq h1 ws == V.transpose_s_ws (as_seq h0 ws))

let transpose_s_ws #m ws =
  match m with
  | M32 -> ()
  | M256 -> transpose_s_ws4 ws

inline_for_extraction noextract
val storeState: #m:m_spec
  -> s:state_t m
  -> hbuf:lbuffer uint8 (size (lanes m) *! 32ul *! 8ul) ->
  Stack unit
  (requires fun h -> live h hbuf /\ live h s /\ disjoint hbuf s /\
    as_seq h hbuf == LSeq.create (lanes m * 32 * 8) (u8 0))
  (ensures  fun h0 _ h1 -> modifies (loc hbuf) h0 h1 /\
    as_seq h1 hbuf == V.storeState #m (as_seq h0 s))

let storeState #m s hbuf =
  push_frame ();
  let ws = create 32ul (zero_element m) in
  update_sub ws 0ul 25ul s;
  transpose_s_ws ws;
  Lib.IntVector.Serialize.vecs_store_le hbuf ws;
  pop_frame()

inline_for_extraction noextract
val next_blocks:
  rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> nextBlock:lbuffer uint8 256ul ->
  Stack unit
  (requires fun h -> live h nextBlock /\
    as_seq h nextBlock == LSeq.create 256 (u8 0))
  (ensures  fun h0 _ h1 -> modifies (loc nextBlock) h0 h1 /\
    as_seq h1 nextBlock == V.next_blocks (v rateInBytes) (as_seq h0 nextBlock))

let next_blocks rateInBytes nextBlock =
  nextBlock.(rateInBytes -! 1ul) <- u8 0x80

inline_for_extraction noextract
val next_block1: #m:m_spec{m == M32}
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> b:multibuf (lanes m) 256ul ->
  Stack unit
  (requires fun h -> live_multi h b /\
    as_seq_multi h b == next_block_seq_zero m)
  (ensures  fun h0 _ h1 -> modifies_multi b h0 h1 /\
    as_seq_multi h1 b == V.next_block #m (v rateInBytes) (as_seq_multi h0 b))

let next_block1 #m rateInBytes b =
  let h0 = ST.get() in
  let b0 = b.(|0|) in
  next_blocks rateInBytes b0;
  let h1 = ST.get() in
  Lib.NTuple.eq_intro (as_seq_multi h1 b)
    (V.next_block1 #m (v rateInBytes) (as_seq_multi h0 b))

inline_for_extraction noextract
val next_block4: #m:m_spec{m == M256}
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> b:multibuf (lanes m) 256ul ->
  Stack unit
  (requires fun h -> live_multi h b /\ internally_disjoint b /\
    as_seq_multi h b == next_block_seq_zero m)
  (ensures  fun h0 _ h1 -> modifies_multi b h0 h1 /\
    as_seq_multi h1 b == V.next_block #m (v rateInBytes) (as_seq_multi h0 b))

let next_block4 #m rateInBytes b =
  let h0 = ST.get() in
  let (b0,(b1,(b2,b3))) = tup4 b in
  assert (internally_disjoint4 b0 b1 b2 b3);
  next_blocks rateInBytes b0;
  next_blocks rateInBytes b1;
  next_blocks rateInBytes b2;
  next_blocks rateInBytes b3;
  loc_multi4 b;
  let h1 = ST.get() in
  Lib.NTuple.eq_intro (as_seq_multi h1 b)
    (V.next_block4 #m (v rateInBytes) (as_seq_multi h0 b))

inline_for_extraction noextract
val next_block: #m:m_spec
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> b:multibuf (lanes m) 256ul ->
  Stack unit
  (requires fun h -> live_multi h b /\ internally_disjoint b /\
    as_seq_multi h b == next_block_seq_zero m)
  (ensures  fun h0 _ h1 -> modifies_multi b h0 h1 /\
    as_seq_multi h1 b == V.next_block #m (v rateInBytes) (as_seq_multi h0 b))

let next_block #m rateInBytes b =
  match m with
  | M32 -> next_block1 #m rateInBytes b
  | M256 -> next_block4 #m rateInBytes b

inline_for_extraction noextract
val alloc_multi1: m:m_spec{m == M32} ->
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

inline_for_extraction noextract
val alloc_multi4: m:m_spec{m == M256} ->
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
  b

inline_for_extraction noextract
val alloc_multi: m:m_spec ->
  StackInline (multibuf (lanes m) 256ul)
  (requires fun h -> True)
  (ensures  fun h0 b h1 -> live_multi h1 b /\ internally_disjoint b /\
    stack_allocated_multi b h0 h1 (Seq.create 256 (u8 0)) /\
    as_seq_multi h1 b == next_block_seq_zero m)

let alloc_multi m =
  match m with
  | M32 -> alloc_multi1 m
  | M256 -> alloc_multi4 m

let absorb_inner #m rateInBytes b s =
  loadState #m rateInBytes b s;
  state_permute m s

inline_for_extraction noextract
let absorb_next_t (m:m_spec) =
    rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> s:state_t m ->
  Stack unit
  (requires fun h -> live h s)
  (ensures  fun h0 _ h1 -> modifies (loc s) h0 h1 /\
    as_seq h1 s == V.absorb_next #m (v rateInBytes) (as_seq h0 s))

inline_for_extraction noextract
val absorb_next: #m:m_spec -> absorb_inner:absorb_inner_t m -> absorb_next_t m

let absorb_next #m absorb_inner rateInBytes s =
  let h0_init = ST.get() in
  push_frame ();
  let b = alloc_multi m in
  next_block #m rateInBytes b;
  if (lanes m = 1) then loc_multi1 b else loc_multi4 b;
  let h0 = ST.get() in
  assert (forall l. l < lanes m ==> (forall i. (i >= v rateInBytes /\ i < 256) ==>
    Seq.index (as_seq_multi h0 b).(|l|) i == u8 0));
  absorb_inner rateInBytes b s;
  pop_frame();
  let h1 = ST.get() in
  LSeq.eq_intro (as_seq h1 s) (V.absorb_next #m (v rateInBytes) (as_seq h0_init s))

inline_for_extraction noextract
val load_last_blocks:
  rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> rem:size_t{v rem < v rateInBytes}
  -> delimitedSuffix:byte_t
  -> lastBlock:lbuffer uint8 256ul ->
  Stack unit
  (requires fun h -> live h lastBlock /\ (forall i. (i >= v rem /\ i < 256) ==>
    Seq.index (as_seq h lastBlock) i == u8 0))
  (ensures  fun h0 _ h1 -> modifies (loc lastBlock) h0 h1 /\
    as_seq h1 lastBlock ==
      V.load_last_blocks (v rateInBytes) (v rem) delimitedSuffix (as_seq h0 lastBlock))

let load_last_blocks _ rem delimitedSuffix lastBlock =
  lastBlock.(rem) <- byte_to_uint8 delimitedSuffix

inline_for_extraction noextract
val load_last_block1: #m:m_spec{m == M32}
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> rem:size_t{v rem < v rateInBytes}
  -> delimitedSuffix:byte_t
  -> b:multibuf (lanes m) 256ul ->
  Stack unit
  (requires fun h -> live_multi h b /\
    (forall l. l < lanes m ==> (forall i. (i >= v rem /\ i < 256) ==>
      Seq.index (as_seq_multi h b).(|l|) i == u8 0)))
  (ensures  fun h0 _ h1 -> modifies_multi b h0 h1 /\
    as_seq_multi h1 b ==
      V.load_last_block #m (v rateInBytes) (v rem) delimitedSuffix (as_seq_multi h0 b))

let load_last_block1 #m rateInBytes rem delimitedSuffix b =
  let h0 = ST.get() in
  let b0 = b.(|0|) in
  load_last_blocks rateInBytes rem delimitedSuffix b0;
  let h1 = ST.get() in
  Lib.NTuple.eq_intro (as_seq_multi h1 b)
    (V.load_last_block #m (v rateInBytes) (v rem) delimitedSuffix (as_seq_multi h0 b))

inline_for_extraction noextract
val load_last_block4: #m:m_spec{m == M256}
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> rem:size_t{v rem < v rateInBytes}
  -> delimitedSuffix:byte_t
  -> b:multibuf (lanes m) 256ul ->
  Stack unit
  (requires fun h -> live_multi h b /\ internally_disjoint b /\
    (forall l. l < lanes m ==> (forall i. (i >= v rem /\ i < 256) ==>
      Seq.index (as_seq_multi h b).(|l|) i == u8 0)))
  (ensures  fun h0 _ h1 -> modifies_multi b h0 h1 /\
    as_seq_multi h1 b ==
      V.load_last_block #m (v rateInBytes) (v rem) delimitedSuffix (as_seq_multi h0 b))

let load_last_block4 #m rateInBytes rem delimitedSuffix b =
  let h0 = ST.get() in
  let (b0,(b1,(b2,b3))) = tup4 b in
  assert (internally_disjoint4 b0 b1 b2 b3);
  load_last_blocks rateInBytes rem delimitedSuffix b0;
  load_last_blocks rateInBytes rem delimitedSuffix b1;
  load_last_blocks rateInBytes rem delimitedSuffix b2;
  load_last_blocks rateInBytes rem delimitedSuffix b3;
  loc_multi4 b;
  let h1 = ST.get() in
  Lib.NTuple.eq_intro (as_seq_multi h1 b)
    (V.load_last_block #m (v rateInBytes) (v rem) delimitedSuffix (as_seq_multi h0 b))

inline_for_extraction noextract
val load_last_block: #m:m_spec
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> rem:size_t{v rem < v rateInBytes}
  -> delimitedSuffix:byte_t
  -> b:multibuf (lanes m) 256ul ->
  Stack unit
  (requires fun h -> live_multi h b /\ internally_disjoint b /\
    (forall l. l < lanes m ==> (forall i. (i >= v rem /\ i < 256) ==>
      Seq.index (as_seq_multi h b).(|l|) i == u8 0)))
  (ensures  fun h0 _ h1 -> modifies_multi b h0 h1 /\
    as_seq_multi h1 b ==
      V.load_last_block #m (v rateInBytes) (v rem) delimitedSuffix (as_seq_multi h0 b))

let load_last_block #m rateInBytes rem delimitedSuffix b =
  match m with
  | M32 -> load_last_block1 #m rateInBytes rem delimitedSuffix b
  | M256 -> load_last_block4 #m rateInBytes rem delimitedSuffix b

inline_for_extraction noextract
let absorb_last_t (m:m_spec) =
    rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> rem:size_t{v rem < v rateInBytes}
  -> delimitedSuffix:byte_t
  -> b:multibuf (lanes m) 256ul
  -> s:state_t m ->
  Stack unit
  (requires fun h -> live_multi h b /\ live h s /\ disjoint_multi b s /\ internally_disjoint b /\
    (forall l. l < lanes m ==> (forall i. (i >= v rem /\ i < 256) ==>
      Seq.index (as_seq_multi h b).(|l|) i == u8 0)))
  (ensures  fun h0 _ h1 -> modifies (loc s |+| loc_multi b) h0 h1 /\
    as_seq h1 s == V.absorb_last #m delimitedSuffix (v rateInBytes) (v rem) (as_seq_multi h0 b) (as_seq h0 s))

inline_for_extraction noextract
val absorb_last: #m:m_spec -> absorb_inner:absorb_inner_t m -> absorb_last_t m

let absorb_last #m absorb_inner rateInBytes rem delimitedSuffix b s =
  logand_spec delimitedSuffix (byte 0x80);
  assert (v (delimitedSuffix &. byte 0x80) == UInt.logand #8 (v delimitedSuffix) 0x80);
  eq_lemma (delimitedSuffix &. byte 0x80) (byte 0);
  assert (((delimitedSuffix &. byte 0x80) =. byte 0) == (v (delimitedSuffix &. byte 0x80) = 0));
  assert (v (rateInBytes -! 1ul) == v rateInBytes - 1);
  eq_lemma rem (rateInBytes -! 1ul);
  assert ((rem =. (rateInBytes -! 1ul)) == (v rem = v (rateInBytes -! 1ul)));
  load_last_block #m rateInBytes rem delimitedSuffix b;
  if (lanes m = 1) then loc_multi1 b else loc_multi4 b;
  let h0 = ST.get() in
  assert (forall l. l < lanes m ==> (forall j. (j >= (v rem + 1) /\ j < 256) ==>
    Seq.index (as_seq_multi h0 b).(|l|) j == u8 0));
  loadState #m rateInBytes b s;
  if not ((delimitedSuffix &. byte 0x80) =. byte 0) &&
       (rem =. (rateInBytes -! 1ul)) then state_permute m s;
  absorb_next absorb_inner rateInBytes s

inline_for_extraction noextract
let get_multiblock_t (m:m_spec) =
    rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> len:size_t
  -> b:multibuf (lanes m) len
  -> i:size_t{v i < v len / v rateInBytes}
  -> b':multibuf (lanes m) 256ul ->
  Stack unit
  (requires fun h -> live_multi h b /\ live_multi h b' /\
    internally_disjoint b' /\ disjoint_multi_multi b b' /\
    as_seq_multi h b' == next_block_seq_zero m)
  (ensures  fun h0 _ h1 -> modifies_multi b' h0 h1 /\
    as_seq_multi h1 b' == V.get_multiblock_spec (v rateInBytes) (v len) (as_seq_multi h0 b) (v i))

inline_for_extraction noextract
val get_multiblock_1: #m:m_spec{m == M32} -> get_multiblock_t m

#push-options "--z3rlimit 200"
let get_multiblock_1 #m rateInBytes len b i b' =
  let h0 = ST.get() in
  assert (v (i *! rateInBytes) == v i * v rateInBytes);
  assert (v i * v rateInBytes < v len);
  assert (v i + 1 <= v len / v rateInBytes);
  assert ((v i + 1) * v rateInBytes <= v len);
  assert (v i * v rateInBytes + v rateInBytes <= v len);
  let b0 = tup1 b in
  let bl0 = tup1 b' in
  assert (disjoint b0 bl0);
  update_sub bl0 0ul rateInBytes (sub b0 (i *! rateInBytes) rateInBytes);
  let h1 = ST.get() in
  Lib.NTuple.eq_intro (as_seq_multi h1 b') (V.get_multiblock_spec #m (v rateInBytes) (v len) (as_seq_multi h0 b) (v i))
#pop-options

inline_for_extraction noextract
val get_multiblock_4: #m:m_spec{m == M256} -> get_multiblock_t m

#push-options "--ifuel 1 --fuel 1 --z3rlimit 200"
let get_multiblock_4 #m rateInBytes len b i b' =
  let h0 = ST.get() in
  assert (v (i *! rateInBytes) == v i * v rateInBytes);
  assert (v i * v rateInBytes < v len);
  assert (v i + 1 <= v len / v rateInBytes);
  assert ((v i + 1) * v rateInBytes <= v len);
  assert (v i * v rateInBytes + v rateInBytes <= v len);
  let (b0,(b1,(b2,b3))) = tup4 b in
  let (bl0,(bl1,(bl2,bl3))) = tup4 b' in
  assert (internally_disjoint4 bl0 bl1 bl2 bl3);
  assert (disjoint4_4 b0 b1 b2 b3 bl0 bl1 bl2 bl3);
  loc_multi4 b;
  update_sub bl0 0ul rateInBytes (sub b0 (i *! rateInBytes) rateInBytes);
  update_sub bl1 0ul rateInBytes (sub b1 (i *! rateInBytes) rateInBytes);
  update_sub bl2 0ul rateInBytes (sub b2 (i *! rateInBytes) rateInBytes);
  update_sub bl3 0ul rateInBytes (sub b3 (i *! rateInBytes) rateInBytes);
  loc_multi4 b';
  let h1 = ST.get() in
  Lib.NTuple.eq_intro (as_seq_multi h1 b') (V.get_multiblock_spec #m (v rateInBytes) (v len) (as_seq_multi h0 b) (v i))
#pop-options

inline_for_extraction noextract
val get_multiblock: #m:m_spec -> get_multiblock_t m

let get_multiblock #m rateInBytes len b i b' =
  match m with
  | M32 -> get_multiblock_1 #m rateInBytes len b i b'
  | M256 -> get_multiblock_4 #m rateInBytes len b i b'

inline_for_extraction noextract
let get_multilast_t (m:m_spec) =
    rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> len:size_t
  -> b:multibuf (lanes m) len
  -> b':multibuf (lanes m) 256ul ->
  Stack unit
  (requires fun h -> live_multi h b /\ live_multi h b' /\
    internally_disjoint b' /\ disjoint_multi_multi b b' /\
    as_seq_multi h b' == next_block_seq_zero m)
  (ensures  fun h0 _ h1 -> modifies_multi b' h0 h1 /\
    as_seq_multi h1 b' == V.get_multilast_spec (v rateInBytes) (v len) (as_seq_multi h0 b))

inline_for_extraction noextract
val get_multilast_1: #m:m_spec{m == M32} -> get_multilast_t m

let get_multilast_1 #m rateInBytes len b b' =
  let h0 = ST.get() in
  Lib.NTuple.eq_intro (as_seq_multi h0 b') (next_block_seq_zero m);
  let rem = len %. rateInBytes in
  assert (v (len %. rateInBytes) == v len % v rateInBytes);
  Math.Lemmas.lemma_mod_lt (v len) (v rateInBytes);
  assert (v rem <= v len);
  assert (v (len -! rem) == v len - v rem);
  let b0 = tup1 b in
  let bl0 = tup1 b' in
  assert (disjoint b0 bl0);
  update_sub bl0 0ul rem (sub b0 (len -! rem) rem);
  let h1 = ST.get() in
  Lib.NTuple.eq_intro (as_seq_multi h1 b') (V.get_multilast_spec #m (v rateInBytes) (v len) (as_seq_multi h0 b))

inline_for_extraction noextract
val get_multilast_4: #m:m_spec{m == M256} -> get_multilast_t m

#push-options "--max_ifuel 1"
let get_multilast_4 #m rateInBytes len b b' =
  let h0 = ST.get() in
  Lib.NTuple.eq_intro (as_seq_multi h0 b') (next_block_seq_zero m);
  let rem = len %. rateInBytes in
  assert (v (len %. rateInBytes) == v len % v rateInBytes);
  Math.Lemmas.lemma_mod_lt (v len) (v rateInBytes);
  assert (v rem <= v len);
  assert (v (len -! rem) == v len - v rem);
  let (b0,(b1,(b2,b3))) = tup4 b in
  let (bl0,(bl1,(bl2,bl3))) = tup4 b' in
  assert (internally_disjoint4 bl0 bl1 bl2 bl3);
  assert (disjoint4_4 b0 b1 b2 b3 bl0 bl1 bl2 bl3);
  let h0' = ST.get() in
  Lib.NTuple.eq_intro (as_seq_multi h0' b) (as_seq_multi h0 b);
  Lib.NTuple.eq_intro (as_seq_multi h0' b') (next_block_seq_zero m);
  update_sub bl0 0ul rem (sub b0 (len -! rem) rem);
  update_sub bl1 0ul rem (sub b1 (len -! rem) rem);
  update_sub bl2 0ul rem (sub b2 (len -! rem) rem);
  update_sub bl3 0ul rem (sub b3 (len -! rem) rem);
  loc_multi4 b';
  let h1 = ST.get() in
  Lib.NTuple.eq_intro (as_seq_multi h1 b') (V.get_multilast_spec #m (v rateInBytes) (v len) (as_seq_multi h0 b))
#pop-options

inline_for_extraction noextract
val get_multilast: #m:m_spec -> get_multilast_t m

let get_multilast #m rateInBytes len b b' =
  match m with
  | M32 -> get_multilast_1 #m rateInBytes len b b'
  | M256 -> get_multilast_4 #m rateInBytes len b b'

inline_for_extraction noextract
let absorb_inner_block_core_t (m:m_spec) =
    rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> len:size_t
  -> b:multibuf (lanes m) len
  -> b':multibuf (lanes m) 256ul
  -> i:size_t{v i < v len / v rateInBytes}
  -> s:state_t m ->
  Stack unit
  (requires fun h -> live_multi h b /\ live_multi h b' /\ live h s /\
    disjoint_multi b s /\ disjoint_multi b' s /\
    internally_disjoint b' /\ disjoint_multi_multi b b' /\
    as_seq_multi h b' == next_block_seq_zero m)
  (ensures  fun h0 _ h1 -> modifies (loc s |+| loc_multi b') h0 h1 /\
    as_seq h1 s == V.absorb_inner_block #m (v rateInBytes) (v len) (as_seq_multi h0 b) (v i) (as_seq h0 s))

inline_for_extraction noextract
val absorb_inner_block_core: #m:m_spec -> absorb_inner:absorb_inner_t m -> absorb_inner_block_core_t m

let absorb_inner_block_core #m absorb_inner rateInBytes len b b' i s =
  if (lanes m = 1) then loc_multi1 b' else loc_multi4 b';
  get_multiblock #m rateInBytes len b i b';
  absorb_inner rateInBytes b' s

let absorb_inner_block #m absorb_inner rateInBytes len b i s =
  let h0 = ST.get() in
  assert (v (len /. rateInBytes) == v len / v rateInBytes);
  push_frame ();
  let h0_f = ST.get() in
  if (lanes m = 1) then loc_multi1 b else loc_multi4 b;
  let b' = alloc_multi m in
  let h0' = ST.get() in
  Lib.NTuple.eq_intro (as_seq_multi h0' b) (as_seq_multi h0 b);
  if (lanes m = 1) then loc_multi1 b' else loc_multi4 b';
  absorb_inner_block_core #m absorb_inner rateInBytes len b b' i s;
  let h1_f = ST.get() in
  assert (as_seq h1_f s ==
    V.absorb_inner_block #m (v rateInBytes) (v len) (as_seq_multi h0 b) (v i) (as_seq h0 s));
  pop_frame ();
  let h1 = ST.get() in
  assert (as_seq h1 s == as_seq h1_f s);
  fresh_frame_modifies h0 h0_f;
  popped_modifies h1_f h1;
  modifies_remove_fresh_frame h0 h0_f h1 (loc s);
  assert (modifies (loc s) h0 h1);
  assert (modifies (loc s) h0 h1 /\
    as_seq h1 s ==
      V.absorb_inner_block #m (v rateInBytes) (v len) (as_seq_multi h0 b) (v i) (as_seq h0 s))

let absorb_inner_nblocks #m absorb_inner rateInBytes len b s =
  let h0 = ST.get() in
  loop1 h0 (len /. rateInBytes) s
  (fun h -> V.absorb_inner_block #m (v rateInBytes) (v len) (as_seq_multi h0 b))
  (fun i ->
    Lib.LoopCombinators.unfold_repeati (v len / v rateInBytes) (V.absorb_inner_block #m (v rateInBytes) (v len) (as_seq_multi h0 b)) (as_seq h0 s) (v i);
    let h0' = ST.get() in
    Lib.NTuple.eq_intro (as_seq_multi h0' b) (as_seq_multi h0 b);
    absorb_inner_block #m absorb_inner rateInBytes len b i s)

inline_for_extraction noextract
let absorb_final_core_t (m:m_spec) =
    rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> len:size_t
  -> b:multibuf (lanes m) len
  -> b':multibuf (lanes m) 256ul
  -> delimitedSuffix:byte_t
  -> s:state_t m ->
  Stack unit
  (requires fun h -> live_multi h b /\ live_multi h b' /\ live h s /\
    internally_disjoint b' /\ disjoint_multi b' s /\ disjoint_multi_multi b b' /\
    as_seq_multi h b' == next_block_seq_zero m)
  (ensures  fun h0 _ h1 -> modifies (loc s |+| loc_multi b') h0 h1 /\
    as_seq h1 s == V.absorb_final #m (as_seq h0 s) (v rateInBytes)
      (v len) (as_seq_multi h0 b) delimitedSuffix)

inline_for_extraction noextract
val absorb_final_core: #m:m_spec -> absorb_inner:absorb_inner_t m -> absorb_final_core_t m

let absorb_final_core #m absorb_inner rateInBytes len b b' delimitedSuffix s =
  if (lanes m = 1) then loc_multi1 b' else loc_multi4 b';
  assert (v (len %. rateInBytes) == v len % v rateInBytes);
  get_multilast #m rateInBytes len b b';
  absorb_last #m absorb_inner rateInBytes (len %. rateInBytes) delimitedSuffix b' s

#push-options "--z3rlimit 200"
let absorb_final #m absorb_inner rateInBytes len b delimitedSuffix s =
  let h0 = ST.get() in
  assert (v (len %. rateInBytes) == v len % v rateInBytes);
  Math.Lemmas.lemma_mod_lt (v len) (v rateInBytes);
  push_frame ();
  let h0_f = ST.get() in
  if (lanes m = 1) then loc_multi1 b else loc_multi4 b;
  let b' = alloc_multi m in
  let h0' = ST.get() in
  Lib.NTuple.eq_intro (as_seq_multi h0' b) (as_seq_multi h0 b);
  if (lanes m = 1) then loc_multi1 b' else loc_multi4 b';
  absorb_final_core #m absorb_inner rateInBytes len b b' delimitedSuffix s;
  let h1_f = ST.get() in
  assert (as_seq h1_f s ==
    V.absorb_final #m (as_seq h0 s) (v rateInBytes) (v len) (as_seq_multi h0 b) delimitedSuffix);
  pop_frame ();
  let h1 = ST.get() in
  assert (as_seq h1 s == as_seq h1_f s);
  fresh_frame_modifies h0 h0_f;
  popped_modifies h1_f h1;
  modifies_remove_fresh_frame h0 h0_f h1 (loc s);
  assert (modifies (loc s) h0 h1);
  assert (modifies (loc s) h0 h1 /\
    as_seq h1 s ==
      V.absorb_final #m (as_seq h0 s) (v rateInBytes) (v len) (as_seq_multi h0 b) delimitedSuffix)
#pop-options

let absorb #m absorb_inner rateInBytes len b delimitedSuffix s =
  let h0 = ST.get() in
  if (lanes m = 1) then loc_multi1 b else loc_multi4 b;
  absorb_inner_nblocks #m absorb_inner rateInBytes len b s;
  absorb_final #m absorb_inner rateInBytes len b delimitedSuffix s;
  let h1 = ST.get() in
  assert (as_seq h1 s ==
    V.absorb #m (as_seq h0 s) (v rateInBytes) (v len) (as_seq_multi h0 b) delimitedSuffix);
  assert (modifies (loc s) h0 h1 /\ as_seq h1 s ==
    V.absorb #m (as_seq h0 s) (v rateInBytes) (v len) (as_seq_multi h0 b) delimitedSuffix)

inline_for_extraction noextract
val update_output1:
  #m:m_spec{m == M32}
  -> block:lbuffer uint8 (size (lanes m) *! 256ul)
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> outputByteLen:size_t
  -> i:size_t{v i < v outputByteLen / v rateInBytes}
  -> b:multibuf (lanes m) outputByteLen ->
  Stack unit
  (requires fun h -> live h block /\ live_multi h b /\ internally_disjoint b /\
    disjoint_multi b block)
  (ensures  fun h0 _ h1 -> modifies_multi b h0 h1 /\ as_seq_multi h1 b ==
      V.update_b #m (as_seq h0 block) (v rateInBytes) (v outputByteLen) (v i) (as_seq_multi h0 b))

#push-options "--z3rlimit 200"
let update_output1 #m block rateInBytes outputByteLen i b =
  let h0 = ST.get() in
  loc_multi1 b;
  let b0 = tup1 b in
  assert (disjoint b0 block);
  assert (v (i *! rateInBytes) == v i * v rateInBytes);
  assert (v i * v rateInBytes < v outputByteLen);
  assert (v i + 1 <= v outputByteLen / v rateInBytes);
  assert ((v i + 1) * v rateInBytes <= v outputByteLen);
  assert (v i * v rateInBytes + v rateInBytes <= v outputByteLen);
  update_sub b0 (i *! rateInBytes) rateInBytes (sub block 0ul rateInBytes);
  let h1 = ST.get() in
  Lib.NTuple.eq_intro (as_seq_multi h1 b)
    (V.update_b #m (as_seq h0 block) (v rateInBytes) (v outputByteLen) (v i) (as_seq_multi h0 b))
#pop-options

inline_for_extraction noextract
val update_output4:
  #m:m_spec{m == M256}
  -> block:lbuffer uint8 (size (lanes m) *! 256ul)
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> outputByteLen:size_t
  -> i:size_t{v i < v outputByteLen / v rateInBytes}
  -> b:multibuf (lanes m) outputByteLen ->
  Stack unit
  (requires fun h -> live h block /\ live_multi h b /\ internally_disjoint b /\
    disjoint_multi b block)
  (ensures  fun h0 _ h1 -> modifies_multi b h0 h1 /\ as_seq_multi h1 b ==
      V.update_b #m (as_seq h0 block) (v rateInBytes) (v outputByteLen) (v i) (as_seq_multi h0 b))

#push-options "--z3rlimit 200"
let update_output4 #m block rateInBytes outputByteLen i b =
  let h0 = ST.get() in
  loc_multi4 b;
  let (b0,(b1,(b2,b3))) = tup4 b in
  assert (internally_disjoint4 b0 b1 b2 b3);
  assert (disjoint b0 block);
  assert (disjoint b1 block);
  assert (disjoint b2 block);
  assert (disjoint b3 block);
  assert (v (i *! rateInBytes) == v i * v rateInBytes);
  assert (v i * v rateInBytes < v outputByteLen);
  assert (v i + 1 <= v outputByteLen / v rateInBytes);
  assert ((v i + 1) * v rateInBytes <= v outputByteLen);
  assert (v i * v rateInBytes + v rateInBytes <= v outputByteLen);
  update_sub b0 (i *! rateInBytes) rateInBytes (sub block 0ul rateInBytes);
  update_sub b1 (i *! rateInBytes) rateInBytes (sub block 256ul rateInBytes);
  update_sub b2 (i *! rateInBytes) rateInBytes (sub block 512ul rateInBytes);
  update_sub b3 (i *! rateInBytes) rateInBytes (sub block 768ul rateInBytes);
  let h1 = ST.get() in
  Lib.NTuple.eq_intro (as_seq_multi h1 b)
    (V.update_b #m (as_seq h0 block) (v rateInBytes) (v outputByteLen) (v i) (as_seq_multi h0 b))
#pop-options

inline_for_extraction noextract
val update_output:
  #m:m_spec
  -> block:lbuffer uint8 (size (lanes m) *! 256ul)
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> outputByteLen:size_t
  -> i:size_t{v i < v outputByteLen / v rateInBytes}
  -> b:multibuf (lanes m) outputByteLen ->
  Stack unit
  (requires fun h -> live h block /\ live_multi h b /\ internally_disjoint b /\
    disjoint_multi b block)
  (ensures  fun h0 _ h1 -> modifies_multi b h0 h1 /\ as_seq_multi h1 b ==
      V.update_b #m (as_seq h0 block) (v rateInBytes) (v outputByteLen) (v i) (as_seq_multi h0 b))

let update_output #m block rateInBytes outputByteLen i b =
  match m with
  | M32 -> update_output1 #m block rateInBytes outputByteLen i b
  | M256 -> update_output4 #m block rateInBytes outputByteLen i b

inline_for_extraction noextract
val update_output_last1:
  #m:m_spec{m == M32}
  -> block:lbuffer uint8 (size (lanes m) *! 256ul)
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> outputByteLen:size_t
  -> outRem:size_t{v outRem == v outputByteLen % v rateInBytes}
  -> b:multibuf (lanes m) outputByteLen ->
  Stack unit
  (requires fun h -> live h block /\ live_multi h b /\ internally_disjoint b /\
    disjoint_multi b block)
  (ensures  fun h0 _ h1 -> modifies_multi b h0 h1 /\ as_seq_multi h1 b ==
      V.update_b_last #m (as_seq h0 block) (v rateInBytes) (v outputByteLen) (v outRem) (as_seq_multi h0 b))

let update_output_last1 #m block rateInBytes outputByteLen outRem b =
  let h0 = ST.get() in
  assert (v (outputByteLen -! outRem) == v outputByteLen - v outRem);
  update_sub b.(|0|) (outputByteLen -! outRem) outRem (sub block 0ul outRem);
  let h1 = ST.get() in
  Lib.NTuple.eq_intro (as_seq_multi h1 b)
    (V.update_b_last #m (as_seq h0 block) (v rateInBytes) (v outputByteLen) (v outRem) (as_seq_multi h0 b))

inline_for_extraction noextract
val update_output_last4:
  #m:m_spec{m == M256}
  -> block:lbuffer uint8 (size (lanes m) *! 256ul)
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> outputByteLen:size_t
  -> outRem:size_t{v outRem == v outputByteLen % v rateInBytes}
  -> b:multibuf (lanes m) outputByteLen ->
  Stack unit
  (requires fun h -> live h block /\ live_multi h b /\ internally_disjoint b /\
    disjoint_multi b block)
  (ensures  fun h0 _ h1 -> modifies_multi b h0 h1 /\ as_seq_multi h1 b ==
      V.update_b_last #m (as_seq h0 block) (v rateInBytes) (v outputByteLen) (v outRem) (as_seq_multi h0 b))

let update_output_last4 #m block rateInBytes outputByteLen outRem b =
  let h0 = ST.get() in
  loc_multi4 b;
  let (b0,(b1,(b2,b3))) = tup4 b in
  assert (internally_disjoint4 b0 b1 b2 b3);
  assert (v (outputByteLen -! outRem) == v outputByteLen - v outRem);
  update_sub b0 (outputByteLen -! outRem) outRem (sub block 0ul outRem);
  update_sub b1 (outputByteLen -! outRem) outRem (sub block 256ul outRem);
  update_sub b2 (outputByteLen -! outRem) outRem (sub block 512ul outRem);
  update_sub b3 (outputByteLen -! outRem) outRem (sub block 768ul outRem);
  let h1 = ST.get() in
  Lib.NTuple.eq_intro (as_seq_multi h1 b)
    (V.update_b_last #m (as_seq h0 block) (v rateInBytes) (v outputByteLen) (v outRem) (as_seq_multi h0 b))

inline_for_extraction noextract
val update_output_last:
  #m:m_spec
  -> block:lbuffer uint8 (size (lanes m) *! 256ul)
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> outputByteLen:size_t
  -> outRem:size_t{v outRem == v outputByteLen % v rateInBytes}
  -> b:multibuf (lanes m) outputByteLen ->
  Stack unit
  (requires fun h -> live h block /\ live_multi h b /\ internally_disjoint b /\
    disjoint_multi b block)
  (ensures  fun h0 _ h1 -> modifies_multi b h0 h1 /\ as_seq_multi h1 b ==
      V.update_b_last #m (as_seq h0 block) (v rateInBytes) (v outputByteLen) (v outRem) (as_seq_multi h0 b))

let update_output_last #m block rateInBytes outputByteLen outRem b =
  match m with
  | M32 -> update_output_last1 #m block rateInBytes outputByteLen outRem b
  | M256 -> update_output_last4 #m block rateInBytes outputByteLen outRem b

inline_for_extraction noextract
val squeeze_inner: #m:m_spec
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> outputByteLen:size_t
  -> i:size_t{v i < v outputByteLen / v rateInBytes}
  -> s:state_t m
  -> b:multibuf (lanes m) outputByteLen ->
  Stack unit
  (requires fun h -> live_multi h b /\ live h s /\ internally_disjoint b /\
    disjoint_multi b s)
  (ensures  fun h0 _ h1 -> modifies (loc s |+| loc_multi b) h0 h1 /\
    (let s', b' =
      V.squeeze_inner #m (v rateInBytes) (v outputByteLen) (v i) (as_seq h0 s, as_seq_multi h0 b) in
      as_seq h1 s == s' /\
      as_seq_multi h1 b == b'))

let squeeze_inner #m rateInBytes outputByteLen i s b =
  let h0 = ST.get() in
  push_frame();
  let hbuf = create (size (lanes m) *. 32ul *. 8ul) (u8 0) in
  storeState #m s hbuf;
  let h1 = ST.get() in
  Lib.NTuple.eq_intro (as_seq_multi h1 b) (as_seq_multi h0 b);
  update_output #m hbuf rateInBytes outputByteLen i b;
  if (lanes m = 1) then loc_multi1 b else loc_multi4 b;
  state_permute m s;
  pop_frame();
  let h1 = ST.get() in
  let s', b' =
    V.squeeze_inner #m (v rateInBytes) (v outputByteLen) (v i) (as_seq h0 s, as_seq_multi h0 b) in
  LSeq.eq_intro (as_seq h1 s) s';
  Lib.NTuple.eq_intro (as_seq_multi h1 b) b'

let squeeze_nblocks #m s rateInBytes outputByteLen b =
  [@ inline_let]
  let refl h i : GTot ((V.state_spec m) & (V.multiseq (lanes m) (v outputByteLen))) = as_seq h s, as_seq_multi h b in
  if (lanes m = 1) then loc_multi1 b else loc_multi4 b;
  [@ inline_let]
  let footprint i = loc_union (loc s) (loc_multi b) in
  [@ inline_let]
  let spec h0 = V.squeeze_inner #m (v rateInBytes) (v outputByteLen) in
  let h0 = ST.get () in
  loop h0 (outputByteLen /. rateInBytes) (V.squeeze_s m (v rateInBytes) (v outputByteLen)) refl footprint spec
  (fun i ->
    Loop.unfold_repeat_gen (v outputByteLen / v rateInBytes)
      (V.squeeze_s m (v rateInBytes) (v outputByteLen)) (spec h0) (refl h0 0) (v i);
    squeeze_inner #m rateInBytes outputByteLen i s b
  )

let squeeze_last #m s rateInBytes outputByteLen b =
  let h0 = ST.get () in
  assert (v (outputByteLen %. rateInBytes) == v outputByteLen % v rateInBytes);
  push_frame();
  let remOut = outputByteLen %. rateInBytes in
  let hbuf = create (size (lanes m) *. 32ul *. 8ul) (u8 0) in
  storeState #m s hbuf;
  let h1 = ST.get() in
  Lib.NTuple.eq_intro (as_seq_multi h1 b) (as_seq_multi h0 b);
  update_output_last #m hbuf rateInBytes outputByteLen remOut b;
  pop_frame();
  let h1 = ST.get() in
  Lib.NTuple.eq_intro (as_seq_multi h1 b) (V.squeeze_last #m (as_seq h0 s) (v rateInBytes) (v outputByteLen) (as_seq_multi h0 b))

let squeeze #m s rateInBytes outputByteLen b =
  squeeze_nblocks #m s rateInBytes outputByteLen b;
  squeeze_last #m s rateInBytes outputByteLen b

inline_for_extraction noextract
let keccak_core_t (m:m_spec) =
    rate:size_t{v rate % 8 == 0 /\ v rate / 8 > 0 /\ v rate <= 1600}
  -> inputByteLen:size_t
  -> input:multibuf (lanes m) inputByteLen
  -> delimitedSuffix:byte_t
  -> outputByteLen:size_t
  -> output:multibuf (lanes m) outputByteLen
  -> s:state_t m ->
  Stack unit
    (requires fun h -> live_multi h input /\ live_multi h output /\ live h s /\
      internally_disjoint output /\ disjoint_multi_multi input output /\
      disjoint_multi input s /\ disjoint_multi output s)
    (ensures  fun h0 _ h1 ->
      modifies (loc s |+| loc_multi output) h0 h1 /\
      as_seq_multi h1 output ==
        V.squeeze #m (V.absorb #m (as_seq h0 s) (v rate / 8) (v inputByteLen) (as_seq_multi h0 input) delimitedSuffix)
          (v rate / 8) (v outputByteLen) (as_seq_multi h0 output))

inline_for_extraction noextract
val keccak_core: #m:m_spec -> absorb_inner:absorb_inner_t m -> keccak_core_t m

let keccak_core #m absorb_inner rate inputByteLen input delimitedSuffix outputByteLen output s =
  let h0 = ST.get () in
  assert (v (rate /. 8ul) == v rate / 8);
  let rateInBytes = rate /. 8ul in
  absorb #m absorb_inner rateInBytes inputByteLen input delimitedSuffix s;
  let h0' = ST.get () in
  Lib.NTuple.eq_intro (as_seq_multi h0' output) (as_seq_multi h0 output);
  squeeze #m s rateInBytes outputByteLen output

let keccak #m absorb_inner rate inputByteLen input delimitedSuffix outputByteLen output =
  let h0 = ST.get () in
  assert (v (rate /. 8ul) == v rate / 8);
  if (lanes m = 1) then loc_multi1 output else loc_multi4 output;
  push_frame();
  let h0_f = ST.get() in
  let rateInBytes = rate /. 8ul in
  let s = create 25ul (zero_element m) in
  let h0' = ST.get () in
  Lib.NTuple.eq_intro (as_seq_multi h0' input) (as_seq_multi h0 input);
  Lib.NTuple.eq_intro (as_seq_multi h0' output) (as_seq_multi h0 output);
  keccak_core #m absorb_inner rate inputByteLen input delimitedSuffix outputByteLen output s;
  let h1_f = ST.get() in
  assert (as_seq_multi h1_f output ==
    V.keccak #m (v rate) (v inputByteLen) (as_seq_multi h0 input) delimitedSuffix
    (v outputByteLen) (as_seq_multi h0 output));
  pop_frame();
  let h1 = ST.get() in
  Lib.NTuple.eq_intro (as_seq_multi h1 output) (as_seq_multi h1_f output);
  fresh_frame_modifies h0 h0_f;
  popped_modifies h1_f h1;
  modifies_remove_fresh_frame h0 h0_f h1 (loc_multi output)
