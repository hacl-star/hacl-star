module Hacl.Spec.AES.BitSlice16xN


open Lib.IntTypes
open Lib.FixedSequence
open FStar.Mul

type bitlen = n:nat{n == 1 \/ n == 8 \/ n == 16}
type u1xN (n:bitlen) = fseq uint1 n
type uint8 = u1xN 8
type uint16 = u1xN 16
let to_uint16 (u:Lib.IntTypes.pub_uint16) : uint16 =
  createi 16 (fun i -> cast U1 SEC (u >>. (size i)))
type lanes = n:nat{n == 1 \/ n == 4}
type u1xNxL (n:bitlen) (l:lanes) = fseq (u1xN n) l

let ( ^| ) (#n:bitlen) (#l:lanes) (x:u1xNxL n l) (y:u1xNxL n l) : u1xNxL n l = map2 (map2 ( ^. )) x y
let ( &| ) (#n:bitlen) (#l:lanes) (x:u1xNxL n l) (y:u1xNxL n l) : u1xNxL n l = map2 (map2 ( ^. )) x y
let ( || ) (#n:bitlen) (#l:lanes) (x:u1xNxL n l) (y:u1xNxL n l) : u1xNxL n l = map2 (map2 ( ^. )) x y
let ( ~| ) (#n:bitlen) (#l:lanes) (x:u1xNxL n l) : u1xNxL n l = map (map (lognot #U1 #SEC)) x
let ( >>| ) (#n:bitlen) (#l:lanes) (x:u1xNxL n l) (y:nat{y < n}) : u1xNxL n l =
	    map (fun xi -> createi n (fun j -> xi.[(j + y) % n])) x
let ( <<| )  (#n:bitlen) (#l:lanes) (x:u1xNxL n l) (y:nat{y < n}) : u1xNxL n l =
	    map (fun xi -> createi n (fun j -> xi.[(j + n - y) % n])) x


type state (l: lanes) = fseq (u1xNxL 16 l) 8

let rotate_row_right (#l:lanes) (x:u1xNxL 16 l) (i:nat{i < 4}) (r:nat{r < 4}) =
  if r = 0 then x else
  let row_mask16 = to_uint16 (0x1111us <<. size i) in
  let row_mask = create l row_mask16 in
  let xm = x &| row_mask in
  (xm >>| (4*r)) || (xm <<| (16-(4*r)))

let rotate_cols_right (#l:lanes) (x:u1xNxL 16 l) (r:nat{r < 4}) =
  if r = 0 then x
  else if r = 1 then
    let mr = create l (to_uint16 0xeeeeus) in
    let ml = create l (to_uint16 0x1111us) in
    ((x &| mr) >>| 1) || ((x &| ml) <<| 3)
  else if r = 2 then
    let mr = create l (to_uint16 0xccccus) in
    let ml = create l (to_uint16 0x3333us) in
    ((x &| mr) >>| 2) || ((x &| ml) <<| 2)
  else
    let mr = create l (to_uint16 0x3333us) in
    let ml = create l (to_uint16 0xccccus) in
    ((x &| mr) >>| 3) || ((x &| ml) <<| 1)

type blocks (l: lanes) = fseq (fseq uint8 16) l

let transpose (#l:lanes) (s:state l) : blocks l =
    createi l (fun i -> createi 16 (fun j -> createi 8 (fun k -> s.[k].[i].[j])))


val subBytes: #n:bitlen -> #l: lanes -> s: fseq (u1xNxL n l) 8 -> fseq (u1xNxL n l) 8
let subBytes #n #l (st0, (st1, (st2, (st3, (st4, (st5, (st6, st7)))))))  =
  let u0: u1xNxL n l = st7 in
  let u1: u1xNxL n l = st6 in
  let u2: u1xNxL n l = st5 in
  let u3: u1xNxL n l = st4 in
  let u4: u1xNxL n l = st3 in
  let u5: u1xNxL n l = st2 in
  let u6: u1xNxL n l = st1 in
  let u7: u1xNxL n l = st0 in

  let t1 = u6 ^| u4 in
  let t2 = u3 ^| u0 in
  let t3 = u1 ^| u2 in
  let t6 = u1 ^| u5 in
  let t7 = u0 ^| u6 in
  let t13 = u2 ^| u5 in
  let t16 = u0 ^| u5 in
  let t18 = u6 ^| u5 in

  let t4 = u7 ^| t3 in
  let t5 = t1 ^| t2 in
  let t8 = t1 ^| t6 in
  let t9 = u6 ^| t4 in

  let t10 = u3 ^| t4 in
  let t11 = u7 ^| t5 in
  let t12 = t5 ^| t6 in
  let t14 = t3 ^| t5 in
  let t15 = u5 ^| t7 in
  let t17 = u7 ^| t8 in
  let t19 = t2 ^| t18 in
  let t22 = u0 ^| t4 in
  let t54 = t2 &| t8 in
  let t50 = t9 &| t4 in

  let t20 = t4 ^| t15 in
  let t21 = t1 ^| t13 in
  let t39 = t21 ^| t5 in
  let t40 = t21 ^| t7 in
  let t41 = t7 ^| t19 in
  let t42 = t16 ^| t14 in
  let t43 = t22 ^| t17 in
  let t44 = t19 &| t5 in
  let t45 = t20 &| t11 in
  let t47 = t10 &| u7 in
  let t57 = t16 &| t14 in

  let t46 = t12 ^| t44 in
  let t48 = t47 ^| t44 in
  let t49 = t7 &| t21 in
  let t51 = t40 ^| t49 in
  let t52 = t22 &| t17 in
  let t53 = t52 ^| t49 in

  let t55 = t41 &| t39 in
  let t56 = t55 ^| t54 in
  let t58 = t57 ^| t54 in
  let t59 = t46 ^| t45 in
  let t60 = t48 ^| t42 in
  let t61 = t51 ^| t50 in
  let t62 = t53 ^| t58 in
  let t63 = t59 ^| t56 in
  let t64 = t60 ^| t58 in
  let t65 = t61 ^| t56 in
  let t66 = t62 ^| t43 in
  let t67 = t65 ^| t66 in
  let t68 = t65 &| t63 in
  let t69 = t64 ^| t68 in
  let t70 = t63 ^| t64 in
  let t71 = t66 ^| t68 in
  let t72 = t71 &| t70 in
  let t73 = t69 &| t67 in
  let t74 = t63 &| t66 in
  let t75 = t70 &| t74 in
  let t76 = t70 ^| t68 in
  let t77 = t64 &| t65 in
  let t78 = t67 &| t77 in
  let t79 = t67 ^| t68 in
  let t80 = t64 ^| t72 in
  let t81 = t75 ^| t76 in
  let t82 = t66 ^| t73 in
  let t83 = t78 ^| t79 in
  let t84 = t81 ^| t83 in
  let t85 = t80 ^| t82 in
  let t86 = t80 ^| t81 in
  let t87 = t82 ^| t83 in
  let t88 = t85 ^| t84 in
  let t89 = t87 &| t5 in
  let t90 = t83 &| t11 in
  let t91 = t82 &| u7 in
  let t92 = t86 &| t21 in
  let t93 = t81 &| t4 in
  let t94 = t80 &| t17 in
  let t95 = t85 &| t8 in
  let t96 = t88 &| t39 in
  let t97 = t84 &| t14 in
  let t98 = t87 &| t19 in
  let t99 = t83 &| t20 in
  let t100 = t82 &| t10 in
  let t101 = t86 &| t7 in
  let t102 = t81 &| t9 in
  let t103 = t80 &| t22 in
  let t104 = t85 &| t2 in
  let t105 = t88 &| t41 in
  let t106 = t84 &| t16 in
  let t107 = t104 ^| t105 in
  let t108 = t93 ^| t99 in
  let t109 = t96 ^| t107 in
  let t110 = t98 ^| t108 in
  let t111 = t91 ^| t101 in
  let t112 = t89 ^| t92 in
  let t113 = t107 ^| t112 in
  let t114 = t90 ^| t110 in
  let t115 = t89 ^| t95 in
  let t116 = t94 ^| t102 in
  let t117 = t97 ^| t103  in
  let t118 = t91 ^| t114 in
  let t119 = t111 ^| t117 in
  let t120 = t100 ^| t108 in
  let t121 = t92 ^| t95 in
  let t122 = t110 ^| t121 in
  let t123 = t106 ^| t119 in
  let t124 = t104 ^| t115 in
  let t125 = t111 ^| t116 in
  let st7 = t109 ^| t122 in
  let st5 = ~| (t123 ^| t124) in
  let t128 = t94 ^| t107 in
  let st4 = t113 ^| t114 in
  let st3 = t118 ^| t128 in
  let t131 = t93 ^| t101 in
  let t132 = t112 ^| t120 in
  let st0 = ~| (t113 ^| t125) in
  let t134 = t97 ^| t116 in
  let t135 = t131 ^| t134 in
  let t136 = t93 ^| t115 in
  let st1 = ~| (t109 ^| t135) in
  let t138 = t119 ^| t132 in
  let st2 = t109 ^| t138 in
  let t140 = t114 ^| t136 in
  let st6 = ~| (t109 ^| t140) in
  (st0,(st1,(st2,(st3,(st4,(st5,(st6,st7)))))))

(* The result of subbytes is the same as calling the sbox for each uint8
   in the transpose of the state *)
val subBytesVecLemma: #n:bitlen -> #l: lanes -> s: fseq (u1xNxL n l) 8 ->
		   i:nat{i < 8} -> j:nat{j < l} -> k:nat{k < n} ->
		   Lemma (let r = subBytes #n #l s in
			  let s': fseq (u1xNxL 1 1) 8 = map (fun u -> create 1 u.[j].[k]) s in
			  let r' = subBytes #1 #1 s' in
			  r.[i].[j].[k] == r'.[i].[0].[0])
let subBytesVecLemma #n #l s i j k = admit()

assume val sbox: uint8 -> uint8
val subBytesLemma: #l:lanes -> s: state l ->
		   i:nat{i < 8} -> j:nat{j < l} -> k:nat{k < 16} ->
		   Lemma (let r = subBytes #16 #l s in
			  let t = transpose #l s in
			  let r' = sbox t.[j].[k] in
			  r.[i].[j].[k] == r'.[i])
let subBytesLemma #l s i j k = admit()

val mix_columns: #l:lanes -> s:state l -> state l
let mix_columns #l s =
  let cols = map (fun u -> u ^| rotate_cols_right u 1) s in
  (* At this point each row is:
    (c0 + c1, c1 + c2, c2 + c3, c3 + c0) *)
  let s' = map2 (fun x y -> x ^| y ^| (rotate_cols_right y 2)) s cols in
  (* At this point each row is:
     (c1 + c2 + c3, c2 + c3 + c0, c3 + c0 + c1, c0 + c1 + c2) *)
  let s' = createi 8 (fun i -> if i = 0 then s'.[0]
			    else s'.[i] ^| cols.[i-1]) in
  (* At this point each row is the unreduced form of:
     (2c0 + 3c1 + c2 + c3, 2c1 + 3c2 + c3 + c0,
      2c2 + 3c3 + c0 + c1, 2c3 + 3c0 + c1 + c2)
     with an additional carry bit stored in cols.[7] *)
  let s' = s'.[0] <- s'.[0] ^| cols.[7] in
  let s' = s'.[1] <- s'.[1] ^| cols.[7] in
  let s' = s'.[3] <- s'.[3] ^| cols.[7] in
  let s' = s'.[4] <- s'.[4] ^| cols.[7] in
  (* We multiply the carry bit in cols.[7] with 0x1b = 0x11011 (irred) and
     add to each column to obtain the unreduced form of each row:
     (2c0 + 3c1 + c2 + c3, 2c1 + 3c2 + c3 + c0,
      2c2 + 3c3 + c0 + c1, 2c3 + 3c0 + c1 + c2) *)
  s'


val shift_rows: #l:lanes -> s:state l -> state l
let shift_rows #l s =
  map (fun u -> u ||
	 (rotate_row_right #l u 1 1) ||
	 (rotate_row_right #l u 2 2) ||
	 (rotate_row_right #l u 3 3)) s
