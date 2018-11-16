module Hacl.Impl.Aes

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open LowStar.Buffer
  
type lbuffer a len = b:buffer a{length b == len}
type bytes = buffer FStar.UInt8.t
type lbytes l = b:bytes {length b == l} 

inline_for_extraction 
val blit: #a:Type -> src:buffer a -> start1:size_t -> dst:buffer a -> start2:size_t -> len:size_t -> ST unit
               (requires (fun h -> live h src /\ live h dst)) (ensures (fun h0 _ h1 -> live h1 src /\ live h1 dst /\ modifies (loc_buffer dst) h0 h1))
let blit #a src start1 dst start2 len = 
    blit src (Lib.RawIntTypes.size_to_UInt32 start1) dst (Lib.RawIntTypes.size_to_UInt32 start2) (Lib.RawIntTypes.size_to_UInt32 len) 

inline_for_extraction 
val load64_le: b:lbytes 8 -> ST uint64 
               (requires (fun h -> live h b)) (ensures (fun h0 _ h1 -> h0 == h1))
let load64_le b = 
    let u = C.Endianness.load64_le b in
    Lib.RawIntTypes.u64_from_UInt64 u

inline_for_extraction 
val store64_le: b:lbytes 8 -> u:uint64 -> ST unit
               (requires (fun h -> live h b)) (ensures (fun h0 _ h1 -> live h1 b /\ modifies (loc_buffer b) h0 h1))
let store64_le b u = 
    C.Endianness.store64_le b (Lib.RawIntTypes.u64_to_UInt64 u)

inline_for_extraction 
val store32_be: b:lbytes 4 -> u:uint32 -> ST unit
               (requires (fun h -> live h b)) (ensures (fun h0 _ h1 -> live h1 b /\ modifies (loc_buffer b) h0 h1))
let store32_be b u = 
    C.Endianness.store32_be b (Lib.RawIntTypes.u32_to_UInt32 u)

inline_for_extraction 
val gcreateL: #a:Type -> l:list a -> ST (buffer a)
	      (requires (fun h -> True))
	      (ensures (fun h0 b h1 -> recallable b /\ length b == List.Tot.length l))
let gcreateL #a l = 
    gcmalloc_of_list FStar.HyperStack.root l


inline_for_extraction
val sub: #a:Type -> b:buffer a -> i:size_t -> j:size_t -> ST (buffer a) 
         (requires (fun h -> live h b)) (ensures (fun h0 _ h1 -> h0 == h1))
let sub #a b i j = Lib.RawIntTypes.(sub b (size_to_UInt32 i) (size_to_UInt32 j))

inline_for_extraction 
val loop_nospec: #h0:mem -> #a:Type -> n:size_t -> buf:buffer a -> 
		 impl:(size_t -> ST unit (requires (fun h -> live h buf)) (ensures (fun h0 _ h1 -> modifies (loc_buffer buf) h0 h1 /\ live h1 buf))) -> ST unit 
         (requires (fun h -> live h buf)) (ensures (fun h0 _ h1 -> live h1 buf /\ modifies (loc_buffer buf) h0 h1))
inline_for_extraction 
let loop_nospec #h0 #a (n:size_t) (buf:buffer a) impl =
  let inv (h1:mem) (j:nat) = True in
  let f' (j:UInt32.t{0 <= UInt32.v j /\ UInt32.v j <= size_v n}) : Stack unit
      (requires (fun h -> inv h (UInt32.v j)))
      (ensures (fun h1 _ h2 -> inv h2 (UInt32.v j + 1))) =
      impl (Lib.RawIntTypes.size_from_UInt32 j) in
  C.Loops.for 0ul (Lib.RawIntTypes.size_to_UInt32 n) inv f'

inline_for_extraction
let op_Array_Assignment #a #b #c buf i v = upd #a #b #c buf (Lib.RawIntTypes.size_to_UInt32 i) v
inline_for_extraction
let op_Array_Access #a #b #c buf i  = index #a #b #c buf (Lib.RawIntTypes.size_to_UInt32 i)

(* Parameters for AES-128 *)
noextract inline_for_extraction let nb =  4
noextract inline_for_extraction let nk =  4 // 4, 6, or 8 for 128/192/256
noextract inline_for_extraction let nr =  10 // 10, 12, or 14 for 128/192/256

noextract inline_for_extraction let blocklen =  16 // 4 * nb
noextract inline_for_extraction let keylen   =  16 // 4 * nk
noextract inline_for_extraction let xkeylen  =  176 // 4 * nb * (nr + 1)

type block = lbytes blocklen
type skey  = lbytes keylen

type state = lbuffer uint64 8
type key1 =  lbuffer uint64 8
type keyr =  lbuffer uint64 72
type keyex = lbuffer uint64 88

inline_for_extraction 
let transpose64 (x:uint64) : Tot uint64 = 
     (x &. u64 0x8040201008040201)    |.
    ((x &. u64 0x4020100804020100) >>. u32 7) |.
    ((x &. u64 0x2010080402010000) >>. u32 14) |.
    ((x &. u64 0x1008040201000000) >>. u32 21) |.
    ((x &. u64 0x0804020100000000) >>. u32 28) |.
    ((x &. u64 0x0402010000000000) >>. u32 35) |.
    ((x &. u64 0x0201000000000000) >>. u32 42) |.
    ((x &. u64 0x0100000000000000) >>. u32 49) |.
    ((x <<. u32  7) &. u64 0x4020100804020100) |.
    ((x <<. u32 14) &. u64 0x2010080402010000) |.
    ((x <<. u32 21) &. u64 0x1008040201000000) |.
    ((x <<. u32 28) &. u64 0x0804020100000000) |.
    ((x <<. u32 35) &. u64 0x0402010000000000) |.
    ((x <<. u32 42) &. u64 0x0201000000000000) |.
    ((x <<. u32 49) &. u64 0x0100000000000000)


val to_transpose_block: out:state -> inp:block -> ST unit 
			        (requires (fun h -> live h out /\ live h inp))
				(ensures (fun h0 _ h1 -> live h1 out /\ live h1 inp /\ modifies (loc_buffer out) h0 h1))
let to_transpose_block (out:state) (inp:block) = 
  let b1 : lbytes 8 = sub inp (size 0) (size 8) in
  let b2 : lbytes 8 = sub inp (size 8) (size 8) in
  let fst = load64_le b1 in
  let snd = load64_le b2 in 
  let fst = transpose64 fst in
  let snd = transpose64 snd in
  let h0 = ST.get() in
  loop_nospec #h0 #uint64 (size 8) out 
    (fun i -> 
      let sh = size_to_uint32 (i *. size 8) in
      let u = (fst >>. sh) &. u64 0xff in
      let u = u ^. (((snd >>. sh) &. u64 0xff) <<. u32 8) in
      out.(i) <- u)

inline_for_extraction
val transpose_state: i0:uint64 -> i1:uint64 -> i2: uint64 -> i3:uint64 ->
		     i4:uint64 -> i5:uint64 -> i6: uint64 -> i7:uint64 ->
		     Tot (uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64)
let transpose_state i0 i1 i2 i3 i4 i5 i6 i7 = 
  let t0 = (i0 &. u64 0xffffffff) ^. (i4 <<. u32 32) in
  let t1 = (i1 &. u64 0xffffffff) ^. (i5 <<. u32 32) in
  let t2 = (i2 &. u64 0xffffffff) ^. (i6 <<. u32 32) in
  let t3 = (i3 &. u64 0xffffffff) ^. (i7 <<. u32 32) in
  let t4 = (i4 &. u64 0xffffffff00000000) ^. (i0 >>. u32  32) in
  let t5 = (i5 &. u64 0xffffffff00000000) ^. (i1 >>. u32  32) in
  let t6 = (i6 &. u64 0xffffffff00000000) ^. (i2 >>. u32  32) in
  let t7 = (i7 &. u64 0xffffffff00000000) ^. (i3 >>. u32  32) in

  let t0_ = t0 in
  let t1_ = t1 in
  let t2_ = t3 in
  let t3_ = t3 in
  let t4_ = t4 in
  let t5_ = t5 in
  let t6_ = t6 in
  let t7_ = t7 in
  
  let t0 = (t0 &. u64 0x0000ffff0000ffff) ^. ((t2 &. u64 0x0000ffff0000ffff) <<. u32 16) in
  let t1 = (t1 &. u64 0x0000ffff0000ffff) ^. ((t3 &. u64 0x0000ffff0000ffff) <<. u32 16) in
  let t2 = (t2 &. u64 0xffff0000ffff0000) ^. ((t0_ &. u64 0xffff0000ffff0000) >>. u32  16) in
  let t3 = (t3 &. u64 0xffff0000ffff0000) ^. ((t1_ &. u64 0xffff0000ffff0000) >>. u32  16) in
  let t4 = (t4 &. u64 0x0000ffff0000ffff) ^. ((t6 &. u64 0x0000ffff0000ffff) <<. u32 16) in
  let t5 = (t5 &. u64 0x0000ffff0000ffff) ^. ((t7 &. u64 0x0000ffff0000ffff) <<. u32 16) in
  let t6 = (t6 &. u64 0xffff0000ffff0000) ^. ((t4_ &. u64 0xffff0000ffff0000) >>. u32  16) in
  let t7 = (t7 &. u64 0xffff0000ffff0000) ^. ((t5_ &. u64 0xffff0000ffff0000) >>. u32  16) in

  let t0_ = t0 in
  let t1_ = t1 in
  let t2_ = t2 in
  let t3_ = t3 in
  let t4_ = t4 in
  let t5_ = t5 in
  let t6_ = t6 in
  let t7_ = t7 in

  let t0 = (t0 &. u64 0x00ff00ff00ff00ff) ^. ((t1 &. u64 0x00ff00ff00ff00ff) <<. u32 8) in
  let t1 = (t1 &. u64 0xff00ff00ff00ff00) ^. ((t0_ &. u64 0xff00ff00ff00ff00) >>. u32  8) in
  let t2 = (t2 &. u64 0x00ff00ff00ff00ff) ^. ((t3 &. u64 0x00ff00ff00ff00ff) <<. u32 8) in
  let t3 = (t3 &. u64 0xff00ff00ff00ff00) ^. ((t2_ &. u64 0xff00ff00ff00ff00) >>. u32  8) in
  let t4 = (t4 &. u64 0x00ff00ff00ff00ff) ^. ((t5 &. u64 0x00ff00ff00ff00ff) <<. u32 8) in
  let t5 = (t5 &. u64 0xff00ff00ff00ff00) ^. ((t4_ &. u64 0xff00ff00ff00ff00) >>. u32  8) in
  let t6 = (t6 &. u64 0x00ff00ff00ff00ff) ^. ((t7 &. u64 0x00ff00ff00ff00ff) <<. u32 8) in
  let t7 = (t7 &. u64 0xff00ff00ff00ff00) ^. ((t6_ &. u64 0xff00ff00ff00ff00) >>. u32  8) in

  let t0 = transpose64(t0) in
  let t1 = transpose64(t1) in
  let t2 = transpose64(t2) in
  let t3 = transpose64(t3) in
  let t4 = transpose64(t4) in
  let t5 = transpose64(t5) in
  let t6 = transpose64(t6) in
  let t7 = transpose64(t7) in

  (t0,t1,t2,t3,t4,t5,t6,t7)


val from_transpose: out:lbytes 64 -> inp:state -> ST unit 
			        (requires (fun h -> live h out /\ live h inp))
				(ensures (fun h0 _ h1 -> live h1 out /\ live h1 inp /\ modifies (loc_buffer out) h0 h1))
let from_transpose out (inp:state) = 
  let i0 = inp.(size 0) in
  let i1 = inp.(size 1) in
  let i2 = inp.(size 2) in
  let i3 = inp.(size 3) in
  let i4 = inp.(size 4) in
  let i5 = inp.(size 5) in
  let i6 = inp.(size 6) in
  let i7 = inp.(size 7) in  
  let (t0,t1,t2,t3,t4,t5,t6,t7) = 
    transpose_state i0 i1 i2 i3 i4 i5 i6 i7 in
  store64_le (sub out (size 0) (size 8)) t0;
  store64_le (sub out (size 8) (size 8)) t1;
  store64_le (sub out (size 16) (size 8)) t2;
  store64_le (sub out (size 24) (size 8)) t3;
  store64_le (sub out (size 32) (size 8)) t4;
  store64_le (sub out (size 40) (size 8)) t5;
  store64_le (sub out (size 48) (size 8)) t6;
  store64_le (sub out (size 56) (size 8)) t7


val from_transpose_block: out:block -> inp:state -> ST unit 
			        (requires (fun h -> live h out /\ live h inp))
				(ensures (fun h0 _ h1 -> live h1 out /\ live h1 inp /\ modifies (loc_buffer out) h0 h1))
let from_transpose_block out (inp:state) = 
  let (t0,t1,t2,t3,t4,t5,t6,t7) = transpose_state
				  inp.(size 0)
				  inp.(size 1)
				  inp.(size 2)
				  inp.(size 3)
				  inp.(size 4)
				  inp.(size 5)
				  inp.(size 6)
				  inp.(size 7) in
  store64_le (sub out (size 0) (size 8)) t0;
  store64_le (sub out (size 8) (size 8)) t1


val transpose_nonce: out:state -> nonce:block -> ST unit 
			        (requires (fun h -> live h out /\ live h nonce))
				(ensures (fun h0 _ h1 -> live h1 out /\ live h1 nonce /\ modifies (loc_buffer out) h0 h1))
let transpose_nonce (out:state) (nonce:block) = 
  to_transpose_block out nonce;
  let h0 = ST.get() in
  loop_nospec #h0 (size 8) out 
    (fun i -> 
      let u = out.(i) in
      let u = u ^. (u <<. u32 16) in
      let u = u ^. (u <<. u32 32) in
      out.(i) <- u)

val transpose_counters: out:state -> counters:block -> ST unit 
			        (requires (fun h -> live h out /\ live h counters))
				(ensures (fun h0 _ h1 -> live h1 out /\ live h1 counters /\ modifies (loc_buffer out) h0 h1))
let transpose_counters (out:state) (counters:block) = 
  to_transpose_block out counters;
  let h0 = ST.get() in
  loop_nospec #h0 (size 8) out 
    (fun i -> 
      let u = out.(i) in
      let u = (u <<. u32 12) |. (u <<. u32 24) |. (u <<. u32 36) |. (u <<. u32 48) in 
      let u = u &. u64 0xf000f000f000f000 in
      out.(i) <- u)


inline_for_extraction 
val sub_bytes: uint64 -> uint64 -> uint64 -> uint64 -> uint64 -> uint64 -> uint64 -> uint64 -> Tot (uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64)
let sub_bytes (st0:uint64) (st1:uint64) (st2:uint64) (st3:uint64) (st4:uint64) (st5:uint64) (st6:uint64) (st7:uint64) = 
  let u0 = st7 in
  let u1 = st6 in
  let u2 = st5 in
  let u3 = st4 in
  let u4 = st3 in
  let u5 = st2 in
  let u6 = st1 in
  let u7 = st0 in

  let t1 = u6 ^. u4 in 
  let t2 = u3 ^. u0 in
  let t3 = u1 ^. u2 in
  let t6 = u1 ^. u5 in 
  let t7 = u0 ^. u6 in 
  let t13 = u2 ^. u5 in 
  let t16 = u0 ^. u5 in
  let t18 = u6 ^. u5 in
  
  let t4 = u7 ^. t3 in
  let t5 = t1 ^. t2 in 
  let t8 = t1 ^. t6 in
  let t9 = u6 ^. t4 in
    
  let t10 = u3 ^. t4 in
  let t11 = u7 ^. t5 in
  let t12 = t5 ^. t6 in
  let t14 = t3 ^. t5 in
  let t15 = u5 ^. t7 in 
  let t17 = u7 ^. t8 in  
  let t19 = t2 ^. t18 in
  let t22 = u0 ^. t4 in
  let t54 = t2 &. t8 in
  let t50 = t9 &. t4 in
    
  let t20 = t4 ^. t15 in 
  let t21 = t1 ^. t13 in
  let t39 = t21 ^. t5 in
  let t40 = t21 ^. t7 in  
  let t41 = t7 ^. t19 in
  let t42 = t16 ^. t14 in
  let t43 = t22 ^. t17 in
  let t44 = t19 &. t5 in
  let t45 = t20 &. t11 in
  let t47 = t10 &. u7 in
  let t57 = t16 &. t14 in
  
  let t46 = t12 ^. t44 in  
  let t48 = t47 ^. t44 in
  let t49 = t7 &. t21 in
  let t51 = t40 ^. t49 in
  let t52 = t22 &. t17 in
  let t53 = t52 ^. t49 in

  let t55 = t41 &. t39 in
  let t56 = t55 ^. t54 in
  let t58 = t57 ^. t54 in
  let t59 = t46 ^. t45 in
  let t60 = t48 ^. t42 in
  let t61 = t51 ^. t50 in
  let t62 = t53 ^. t58 in
  let t63 = t59 ^. t56 in
  let t64 = t60 ^. t58 in
  let t65 = t61 ^. t56 in
  let t66 = t62 ^. t43 in
  let t67 = t65 ^. t66 in 
  let t68 = t65 &. t63 in
  let t69 = t64 ^. t68 in
  let t70 = t63 ^. t64 in
  let t71 = t66 ^. t68 in 
  let t72 = t71 &. t70 in
  let t73 = t69 &. t67 in
  let t74 = t63 &. t66 in
  let t75 = t70 &. t74 in
  let t76 = t70 ^. t68 in
  let t77 = t64 &. t65 in
  let t78 = t67 &. t77 in
  let t79 = t67 ^. t68 in
  let t80 = t64 ^. t72 in
  let t81 = t75 ^. t76 in
  let t82 = t66 ^. t73 in
  let t83 = t78 ^. t79 in
  let t84 = t81 ^. t83 in
  let t85 = t80 ^. t82 in
  let t86 = t80 ^. t81 in
  let t87 = t82 ^. t83 in
  let t88 = t85 ^. t84 in
  let t89 = t87 &. t5 in
  let t90 = t83 &. t11 in
  let t91 = t82 &. u7 in
  let t92 = t86 &. t21 in
  let t93 = t81 &. t4 in
  let t94 = t80 &. t17 in
  let t95 = t85 &. t8 in
  let t96 = t88 &. t39 in
  let t97 = t84 &. t14 in
  let t98 = t87 &. t19 in
  let t99 = t83 &. t20 in
  let t100 = t82 &. t10 in
  let t101 = t86 &. t7 in
  let t102 = t81 &. t9 in
  let t103 = t80 &. t22 in
  let t104 = t85 &. t2 in
  let t105 = t88 &. t41 in
  let t106 = t84 &. t16 in
  let t107 = t104 ^. t105 in
  let t108 = t93 ^. t99 in
  let t109 = t96 ^. t107 in
  let t110 = t98 ^. t108 in
  let t111 = t91 ^. t101 in
  let t112 = t89 ^. t92 in
  let t113 = t107 ^. t112 in
  let t114 = t90 ^. t110 in
  let t115 = t89 ^. t95 in
  let t116 = t94 ^. t102 in
  let t117 = t97 ^. t103  in
  let t118 = t91 ^. t114 in
  let t119 = t111 ^. t117 in
  let t120 = t100 ^. t108 in
  let t121 = t92 ^. t95 in
  let t122 = t110 ^. t121 in
  let t123 = t106 ^. t119 in
  let t124 = t104 ^. t115 in
  let t125 = t111 ^. t116 in
  let st7 = t109 ^. t122 in
  let st5 = lognot (t123 ^. t124) in
  let t128 = t94 ^. t107 in
  let st4 = t113 ^. t114 in
  let st3 = t118 ^. t128 in
  let t131 = t93 ^. t101 in
  let t132 = t112 ^. t120 in
  let st0 = lognot (t113 ^. t125) in
  let t134 = t97 ^. t116 in
  let t135 = t131 ^. t134 in
  let t136 = t93 ^. t115 in
  let st1 = lognot (t109 ^. t135) in
  let t138 = t119 ^. t132 in
  let st2 = t109 ^. t138 in
  let t140 = t114 ^. t136 in
  let st6 = lognot (t109 ^. t140) in 
  (st0,st1,st2,st3,st4,st5,st6,st7)

val sub_bytes_state: st:state -> ST unit
			     (requires (fun h -> live h st))
			     (ensures (fun h0 _ h1 -> live h1 st /\ modifies (loc_buffer st) h0 h1))
let sub_bytes_state (st:state) = 
  let (st0,st1,st2,st3,st4,st5,st6,st7) = sub_bytes st.(size 0) st.(size 1)
					           st.(size 2) st.(size 3)
						   st.(size 4) st.(size 5)
						   st.(size 6) st.(size 7) in
  st.(size 0) <- st0;
  st.(size 1) <- st1;
  st.(size 2) <- st2;
  st.(size 3) <- st3;
  st.(size 4) <- st4;
  st.(size 5) <- st5;
  st.(size 6) <- st6;
  st.(size 7) <- st7




inline_for_extraction 
let shift_row (u:uint64) = 
    let u = (u &. u64 0x1111111111111111) |.
      ((u &. u64 0x2220222022202220) >>. u32 4) |. 
      ((u &. u64 0x0002000200020002) <<. u32 12) |.
      ((u &. u64 0x4400440044004400) >>. u32 8) |. 
      ((u &. u64 0x0044004400440044) <<. u32 8) |.
      ((u &. u64 0x8000800080008000) >>. u32 12) |. 
      ((u &. u64 0x0888088808880888) <<. u32 4) in
    u


val shift_rows_state: st:state -> ST unit
			     (requires (fun h -> live h st))
			     (ensures (fun h0 _ h1 -> live h1 st /\ modifies (loc_buffer st) h0 h1))
let shift_rows_state st = 
    let h0 = ST.get() in
    loop_nospec #h0 (size 8) st 
      (fun i -> st.(i) <- let rowi = st.(i) in shift_row rowi)


inline_for_extraction 
let mix_column (col:uint64) (rot:uint64) = 
    let col01 = col ^. (((col &. u64 0xeeeeeeeeeeeeeeee) >>. u32 1) 
                |. ((col &. u64 0x1111111111111111) <<. u32 3)) in
    let col0123 = col01 ^. (((col01 &. u64 0xcccccccccccccccc ) >>. u32  2) 
		  |. ((col01 &. u64 0x3333333333333333) <<. u32  2)) in
    (col ^. col0123 ^. rot, col01)


val mix_columns_state: st:state -> ST unit
			     (requires (fun h -> live h st))
			     (ensures (fun h0 _ h1 -> live h1 st /\ modifies (loc_buffer st) h0 h1))
let mix_columns_state st = 
    push_frame () ;
    let rot_prev = alloca (u64 0) 1ul in
    let h0 = ST.get() in
    loop_nospec #h0 (size 8) st 
      (fun i -> 
	 let col = st.(i) in
	 let rot = rot_prev.(size 0) in
	 let (col',rot') = mix_column col rot in
	 st.(i) <- col';
	 rot_prev.(size 0) <- rot');
    st.(size 0) <- st.(size 0) ^. rot_prev.(size 0);
    st.(size 1) <- st.(size 1) ^. rot_prev.(size 0);
    st.(size 3) <- st.(size 3) ^. rot_prev.(size 0);
    st.(size 4) <- st.(size 4) ^. rot_prev.(size 0);
    pop_frame()


val xor_state: st:state -> ost:state -> ST unit
	     (requires (fun h -> live h st /\ live h ost))
	     (ensures (fun h0 _ h1 -> live h1 st /\ live h1 ost /\ modifies (loc_buffer st) h0 h1))
let xor_state st ost =
    let h0 = ST.get() in
    loop_nospec #h0 (size 8) st 
      (fun i -> st.(i) <- st.(i) ^. ost.(i))

inline_for_extraction
val add_round_key: st:state -> key:key1 -> ST unit
			     (requires (fun h -> live h st /\ live h key))
			     (ensures (fun h0 _ h1 -> live h1 st /\ live h1 key /\ modifies (loc_buffer st) h0 h1))
let add_round_key st key = xor_state st key

val aes_enc: st:state -> key:key1 -> ST unit
			     (requires (fun h -> live h st /\ live h key))
			     (ensures (fun h0 _ h1 -> live h1 st /\ live h1 key /\ modifies (loc_buffer st) h0 h1))
let aes_enc st key = 
    sub_bytes_state st;
    shift_rows_state st;
    mix_columns_state st;
    add_round_key st key


val aes_enc_last: st:state -> key:key1 -> ST unit
			     (requires (fun h -> live h st /\ live h key))
			     (ensures (fun h0 _ h1 -> live h1 st /\ live h1 key /\ modifies (loc_buffer st) h0 h1))
let aes_enc_last st key = 
    sub_bytes_state st;
    shift_rows_state st;
    add_round_key st key

val enc_rounds: st:state -> key:keyr -> ST unit
	     (requires (fun h -> live h st /\ live h key))
	     (ensures (fun h0 _ h1 -> live h1 st /\ live h1 key /\ modifies (loc_buffer st) h0 h1))
let enc_rounds st key = 
    let h0 = ST.get() in
    loop_nospec #h0 (size 9) st 
      (fun i -> aes_enc st (sub key (i *. size 8) (size 8)))


val block_cipher: st:state -> key:keyex -> ST unit
	     (requires (fun h -> live h st /\ live h key))
	     (ensures (fun h0 _ h1 -> live h1 st /\ live h1 key /\ modifies (loc_buffer st) h0 h1))
let block_cipher st key = 
    let k0 = sub key (size 0) (size 8) in
    let kr = sub key (size 8) (size 72) in
    let kn = sub key (size 80) (size 8) in
    add_round_key st k0;
    enc_rounds st kr;
    aes_enc_last st kn
   
let rcon =  gcreateL [u8(0x8d); u8(0x01); u8(0x02); u8(0x04); u8(0x08); u8(0x10); u8(0x20); u8(0x40); u8(0x80); u8(0x1b); u8(0x36)]


inline_for_extraction 
val aes_keygen_assisti: rcon:uint8 -> i:size_t -> u:uint64 -> uint64
let aes_keygen_assisti rcon i u = 
    let n = (u &. u64 0xf000f000f000f000) >>. u32 12 in
    let n = ((n >>. u32 1) |. (n <<. u32 3)) &. u64  0x000f000f000f000f in
    let ri = to_u64 ((rcon >>. size_to_uint32 i) &. u8 1) in
    let ri = ri ^. (ri <<. u32 16) in
    let ri = ri ^. (ri <<. u32 32) in
    let n = n ^. ri in
    let n = n ^. (n <<. u32 4) in
    let n = n ^. (n <<. u32 8 ) in
    n

val aes_keygen_assist: st:state -> rcon:uint8 -> ST unit
			     (requires (fun h -> live h st))
			     (ensures (fun h0 _ h1 -> live h1 st /\ modifies (loc_buffer st) h0 h1))
let aes_keygen_assist st rcon = 
    sub_bytes_state st;
    let h0 = ST.get() in
    loop_nospec #h0 (size 8) st 
      (fun i -> st.(i) <- aes_keygen_assisti rcon i st.(i))

inline_for_extraction 
let key_expand1 (p:uint64) (n:uint64) = 
      let p = p ^. ((p &. u64 0x0fff0fff0fff0fff) <<. u32 4) ^. ((p &. u64 0x00ff00ff00ff00ff) <<. u32 8)
      ^. ((p &. u64 0x000f000f000f000f) <<. u32 12) in
      n ^. p

inline_for_extraction 
val key_expansion_step: next:state -> prev:state -> ST unit
			     (requires (fun h -> live h prev /\ live h next))
			     (ensures (fun h0 _ h1 -> live h1 prev /\ live h1 next /\ modifies (loc_buffer next) h0 h1))
let key_expansion_step next prev = 
    let h0 = ST.get() in
    loop_nospec #h0 (size 8) next 
      (fun i -> next.(i) <- let p = prev.(i) in let n = next.(i) in key_expand1 p n)

inline_for_extraction
val copy_state: next:state -> prev:state -> ST unit
			     (requires (fun h -> live h prev /\ live h next))
			     (ensures (fun h0 _ h1 -> live h1 prev /\ live h1 next /\ modifies (loc_buffer next) h0 h1))
let copy_state next prev = 
    blit prev (size 0) next (size 0) (size 8)
//    let h0 = ST.get() in
//    loop_nospec #h0 (size 8) next 
//      (fun i -> next.(i) <- prev.(i))


val key_expansion: keyx:keyex -> key:skey -> ST unit
			     (requires (fun h -> live h keyx /\ live h key))
			     (ensures (fun h0 _ h1 -> live h1 keyx /\ live h1 key /\ modifies (loc_buffer keyx) h0 h1))
let key_expansion keyx key = 
    transpose_nonce (sub keyx (size 0) (size 8)) key;
    let h0 = ST.get() in
    loop_nospec #h0 (size 10) keyx 
    (fun i -> 
       let prev = sub keyx (i *. size 8) (size 8) in
       let next = sub keyx ((i *. size 8) +. size 8) (size 8) in
       copy_state next prev;
       aes_keygen_assist next rcon.(i +. size 1);
       key_expansion_step next prev)
		     

val encipher: out:block -> inp:block -> keyx:keyex -> ST unit
			     (requires (fun h -> live h out /\ live h inp /\ live h keyx))
			     (ensures (fun h0 _ h1 -> live h1 out /\ live h1 inp /\ live h1 keyx /\ modifies (loc_buffer out) h0 h1))
let encipher out inp keyx = 
    push_frame();
    let st = alloca (u64 0) 8ul in
    to_transpose_block st inp;
    block_cipher st keyx;
    from_transpose_block out st;
    pop_frame()


val aes128_block: kb:lbytes 64 -> keyx:keyex -> nonce:state -> counter:size_t -> ST unit
			     (requires (fun h -> live h kb /\ live h keyx /\ live h nonce))
			     (ensures (fun h0 _ h1 -> live h1 kb /\ live h1 nonce /\ live h1 keyx /\ modifies (loc_buffer kb) h0 h1))
let aes128_block kb keyx nonce counter = 
    push_frame();
    let counter = size_to_uint32 counter in
    let ctr = alloca 0uy 16ul in
    let st = alloca (u64 0) 8ul in
    store32_be  (sub ctr (size 0) (size 4)) counter;
    store32_be  (sub ctr (size 4) (size 4)) (counter +. u32 1);
    store32_be  (sub ctr (size 8) (size 4)) (counter +. u32 2);
    store32_be  (sub ctr (size 12) (size 4)) (counter +. u32 3);
    transpose_counters st ctr;
    xor_state st nonce;
    block_cipher st keyx;
    from_transpose kb st;
    pop_frame()

val aes128_ctr: out:bytes -> inp:bytes -> len:size_t -> key:skey -> nonce:lbytes 12 -> counter:size_t -> ST unit
			     (requires (fun h -> live h out /\ live h inp /\ live h key /\ live h nonce))
			     (ensures (fun h0 _ h1 -> modifies (loc_buffer out) h0 h1))
let aes128_ctr out inp len key nonce counter = 
  push_frame();
  let kex = alloca (u64 0) 88ul in
  let nb = alloca 0uy 16ul in
  let nt = alloca (u64 0) 8ul in
  let kb = alloca 0uy 64ul in
  key_expansion kex key;
  blit nonce (size 0) nb (size 0) (size 12);
  transpose_nonce nt nb;
  let blocks64 = len /. size 64 in
  let h0 = ST.get() in
  loop_nospec #h0 blocks64 out 
    (fun i -> 
      aes128_block kb kex nt (counter +. (i *. size 4));
      loop_nospec #h0 (size 64) out
	(fun j -> out.(j +. (i *. size 64)) <- FStar.UInt8.(inp.(j +. (i *. size 64)) ^^ kb.(j))));
  let rem = len %. size 64 in
  if (rem >. size 0) then (
    aes128_block kb kex nt (counter +. (blocks64 *. size 4));
    loop_nospec #h0 rem out
	(fun j -> out.(j +. (blocks64 *. size 64)) <- FStar.UInt8.(inp.(j +. (blocks64 *. size 64)) ^^ kb.(j)))
	);
  pop_frame()

let aes128_encrypt out inp in_len k n c = aes128_ctr out inp in_len k n c
let aes128_decrypt out inp in_len k n c = aes128_ctr out inp in_len k n c

(* DECRYPTION *)


inline_for_extraction 
val inv_sub_bytes: uint64 -> uint64 -> uint64 -> uint64 -> uint64 -> uint64 -> uint64 -> uint64 -> Tot (uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64)
let inv_sub_bytes (st0:uint64) (st1:uint64) (st2:uint64) (st3:uint64) 
	     (st4:uint64) (st5:uint64) (st6:uint64) (st7:uint64) = 
  let u0 = st7 in
  let u1 = st6 in
  let u2 = st5 in
  let u3 = st4 in
  let u4 = st3 in
  let u5 = st2 in
  let u6 = st1 in
  let u7 = st0 in

  let t23 = u0 +. u3 in
  let t22 = lognot (u1 ^. u3) in
  let t2 = lognot (u0 ^. u1) in
  let t1 = u3 +. u4 in
  let t24 = lognot (u4 ^. u7) in
  let r5 = u6 +. u7 in
  let t8 = lognot (u1 ^. t23) in
  let t19 = t22 +. r5 in
  let t9 = lognot (u7 ^. t1) in
  let t10 = t2 +. t24 in
  let t13 = t2 +. r5 in
  let t3 = t1 +. r5 in
  let t25 = lognot (u2 ^. t1) in
  let r13 = u1 +. u6 in
  let t17 = lognot (u2 ^. t19) in
  let t20 = t24 +. r13 in
  let t4 = u4 +. t8 in
  let r17 = lognot (u2 ^. u5) in
  let r18 = lognot (u5 ^. u6) in
  let r19 = lognot (u2 ^. u4) in
  let y5 = u0 +. r17 in
  let t6 = t22 +. r17 in
  let t16 = r13 +. r19 in
  let t27 = t1 +. r18 in
  let t15 = t10 +. t27 in
  let t14 = t10 +. r18 in
  let t26 = t3 +. t16 in
  let m1 = t13 &. t6 in
  let m2 = t23 &. t8 in
  let m3 = t14 +. m1 in
  let m4 = t19 &. y5 in
  let m5 = m4 +. m1 in
  let m6 = t3 &. t16 in
  let m7 = t22 &. t9 in
  let m8 = t26 +. m6 in
  let m9 = t20 &. t17 in
  let m10 = m9 +. m6 in
  let m11 = t1 &. t15 in
  let m12 = t4 &. t27 in
  let m13 = m12 +. m11 in
  let m14 = t2 &. t10 in
  let m15 = m14 +. m11 in
  let m16 = m3 +. m2 in
  let m17 = m5 +. t24 in
  let m18 = m8 +. m7 in
  let m19 = m10 +. m15 in
  let m20 = m16 +. m13 in
  let m21 = m17 +. m15 in
  let m22 = m18 +. m13 in
  let m23 = m19 +. t25 in
  let m24 = m22 +. m23 in
  let m25 = m22 &. m20 in
  let m26 = m21 +. m25 in
  let m27 = m20 +. m21 in
  let m28 = m23 +. m25 in
  let m29 = m28 &. m27 in
  let m30 = m26 &. m24 in
  let m31 = m20 &. m23 in
  let m32 = m27 &. m31 in
  let m33 = m27 +. m25 in
  let m34 = m21 &. m22 in
  let m35 = m24 &. m34 in
  let m36 = m24 +. m25 in
  let m37 = m21 +. m29 in
  let m38 = m32 +. m33 in
  let m39 = m23 +. m30 in
  let m40 = m35 +. m36 in
  let m41 = m38 +. m40 in
  let m42 = m37 +. m39 in
  let m43 = m37 +. m38 in
  let m44 = m39 +. m40 in
  let m45 = m42 +. m41 in
  let m46 = m44 &. t6 in
  let m47 = m40 &. t8 in
  let m48 = m39 &. y5 in
  let m49 = m43 &. t16 in
  let m50 = m38 &. t9 in
  let m51 = m37 &. t17 in
  let m52 = m42 &. t15 in
  let m53 = m45 &. t27 in
  let m54 = m41 &. t10 in
  let m55 = m44 &. t13 in
  let m56 = m40 &. t23 in
  let m57 = m39 &. t19 in
  let m58 = m43 &. t3 in
  let m59 = m38 &. t22 in
  let m60 = m37 &. t20 in
  let m61 = m42 &. t1 in
  let m62 = m45 &. t4 in
  let m63 = m41 &. t2 in
  let p0 = m52 +. m61 in
  let p1 = m58 +. m59 in
  let p2 = m54 +. m62 in
  let p3 = m47 +. m50 in
  let p4 = m48 +. m56 in
  let p5 = m46 +. m51 in
  let p6 = m49 +. m60 in
  let p7 = p0 +. p1 in
  let p8 = m50 +. m53 in
  let p9 = m55 +. m63 in
  let p10 = m57 +. p4 in
  let p11 = p0 +. p3 in
  let p12 = m46 +. m48 in
  let p13 = m49 +. m51 in
  let p14 = m49 +. m62 in
  let p15 = m54 +. m59 in
  let p16 = m57 +. m61 in
  let p17 = m58 +. p2 in
  let p18 = m63 +. p5 in
  let p19 = p2 +. p3 in
  let p20 = p4 +. p6 in
  let p22 = p2 +. p7 in
  let p23 = p7 +. p8 in
  let p24 = p5 +. p7 in
  let p25 = p6 +. p10 in
  let p26 = p9 +. p11 in
  let p27 = p10 +. p18 in
  let p28 = p11 +. p25 in
  let p29 = p15 +. p20 in
  let w0 = p13 +. p22 in
  let w1 = p26 +. p29 in
  let w2 = p17 +. p28 in
  let w3 = p12 +. p22 in
  let w4 = p23 +. p27 in
  let w5 = p19 +. p24 in
  let w6 = p14 +. p23 in
  let w7 = p9 +. p16  in
  (w7,w6,w5,w4,w3,w2,w1,w0)


val inv_sub_bytes_state: st:state -> ST unit
			     (requires (fun h -> live h st))
			     (ensures (fun h0 _ h1 -> live h1 st /\ modifies (loc_buffer st) h0 h1))
let inv_sub_bytes_state (st:state) = 
  let (st0,st1,st2,st3,st4,st5,st6,st7) = inv_sub_bytes 
                                                   st.(size 0) st.(size 1)
					           st.(size 2) st.(size 3)
						   st.(size 4) st.(size 5)
						   st.(size 6) st.(size 7) in
  st.(size 0) <- st0;
  st.(size 1) <- st1;
  st.(size 2) <- st2;
  st.(size 3) <- st3;
  st.(size 4) <- st4;
  st.(size 5) <- st5;
  st.(size 6) <- st6;
  st.(size 7) <- st7

inline_for_extraction 
let inv_shift_row (u:uint64) = 
    let u = (u &. u64 0x1111111111111111) |.
      ((u &. u64 0x0222022202220222) <<. u32 4) |. 
      ((u &. u64 0x2000200020002000) >>. u32 12) |.
      ((u &. u64 0x4400440044004400) >>. u32 8) |. 
      ((u &. u64 0x0044004400440044) <<. u32 8) |.
      ((u &. u64 0x0008000800080008) <<. u32 12) |. 
      ((u &. u64 0x8880888088808880) >>. u32 4) in
    u

val inv_shift_rows_state: st:state -> ST unit
			     (requires (fun h -> live h st))
			     (ensures (fun h0 _ h1 -> live h1 st /\ modifies (loc_buffer st) h0 h1))
let inv_shift_rows_state st = 
    let h0 = ST.get() in
    loop_nospec #h0 (size 8) st 
      (fun i -> st.(i) <- inv_shift_row (st.(i)))

val inv_mix_columns_state: st:state -> ST unit
			     (requires (fun h -> live h st))
			     (ensures (fun h0 _ h1 -> live h1 st /\ modifies (loc_buffer st) h0 h1))
let inv_mix_columns_state st = 
    push_frame ();
    let t = alloca (u64 0) 8ul in
    mix_columns_state st;
    let h0 = ST.get() in
    loop_nospec #h0 (size 8) t
      (fun i -> 
	 let col  = st.(i) in 
	 let col = col ^. (((col &. u64 0xcccccccccccccccc ) >>. u32  2) |. ((col &. u64 0x3333333333333333) <<. u32  2)) in
         t.(i) <- col);
    st.(size 0) <- st.(size 0) ^. t.(size 6);
    st.(size 1) <- st.(size 1) ^. t.(size 6) ^. t.(size 7);
    st.(size 2) <- st.(size 2) ^. t.(size 0) ^. t.(size 7);
    st.(size 3) <- st.(size 3) ^. t.(size 1) ^. t.(size 6);
    st.(size 4) <- st.(size 4) ^. t.(size 2) ^. t.(size 6) ^. t.(size 7);
    st.(size 5) <- st.(size 5) ^. t.(size 3) ^. t.(size 7);
    st.(size 6) <- st.(size 6) ^. t.(size 4);
    st.(size 7) <- st.(size 7) ^. t.(size 5);
    pop_frame()

val aes_dec: st:state -> key:key1 -> ST unit
			     (requires (fun h -> live h st /\ live h key))
			     (ensures (fun h0 _ h1 -> live h1 st /\ live h1 key /\ modifies (loc_buffer st) h0 h1))
let aes_dec st key = 
    inv_shift_rows_state st;
    inv_sub_bytes_state st;
    add_round_key st key;
    inv_mix_columns_state st



val aes_dec_last: st:state -> key:key1 -> ST unit
			     (requires (fun h -> live h st /\ live h key))
			     (ensures (fun h0 _ h1 -> live h1 st /\ live h1 key /\ modifies (loc_buffer st) h0 h1))
let aes_dec_last st key = 
    inv_shift_rows_state st;
    inv_sub_bytes_state st;
    add_round_key st key

val dec_rounds: st:state -> key:keyr -> ST unit
	     (requires (fun h -> live h st /\ live h key))
	     (ensures (fun h0 _ h1 -> live h1 st /\ live h1 key /\ modifies (loc_buffer st) h0 h1))
let dec_rounds st key = 
    let h0 = ST.get() in
    loop_nospec #h0 (size 9) st 
      (fun i -> aes_dec st (sub key (i *. size 8) (size 8)))


val block_decipher: st:state -> key:keyex -> ST unit
	     (requires (fun h -> live h st /\ live h key))
	     (ensures (fun h0 _ h1 -> live h1 st /\ live h1 key /\ modifies (loc_buffer st) h0 h1))
let block_decipher st key = 
    let k0 = sub key (size 0) (size 8) in
    let kr = sub key (size 8) (size 72) in
    let kn = sub key (size 80) (size 8) in
    add_round_key st k0;
    dec_rounds st kr;
    aes_dec_last st kn


val decipher: out:block -> inp:block -> keyx:keyex -> ST unit
			     (requires (fun h -> live h out /\ live h inp /\ live h keyx))
			     (ensures (fun h0 _ h1 -> live h1 out /\ live h1 inp /\ live h1 keyx /\ modifies (loc_buffer out) h0 h1))
let decipher out inp keyx = 
    push_frame();
    let st = alloca (u64 0) 8ul in
    to_transpose_block st inp;
    block_decipher st keyx;
    from_transpose_block out st;
    pop_frame()
