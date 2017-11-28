module Hacl.Impl.Chacha20

open FStar.HyperStack
open FStar.HyperStack.ST
open Spec.Lib.IntTypes

open Spec.Lib.IntBuf
open Spec.Chacha20

module ST = FStar.HyperStack.ST
module LSeq = Spec.Lib.IntSeq
module Spec = Spec.Chacha20

<<<<<<< HEAD
=======
module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32 = Hacl.UInt32

let u32 = U32.t
let h32 = H32.t
let uint8_p = buffer H8.t

type state = b:Buffer.buffer h32{length b = 16}

[@ "c_inline"]
private let rotate_left (a:h32) (s:u32{0 < U32.v s && U32.v s < 32}) : Tot h32 =
  (a <<^ s) |^ (a >>^ (FStar.UInt32.(32ul -^ s)))

private inline_for_extraction let ( <<< ) = rotate_left

#reset-options "--max_fuel 0 --z3rlimit 100"

[@ "substitute"]
private
val constant_setup_:
  c:Buffer.buffer H32.t{length c = 4} ->
  Stack unit
    (requires (fun h -> live h c))
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_1 c h0 h1
      /\ (let s = as_seq h1 c in
         v (Seq.index s 0) = 0x61707865 /\
         v (Seq.index s 1) = 0x3320646e /\
         v (Seq.index s 2) = 0x79622d32 /\
         v (Seq.index s 3) = 0x6b206574)))
[@ "substitute"]
let constant_setup_ st =
  st.(0ul)  <- (uint32_to_sint32 0x61707865ul);
  st.(1ul)  <- (uint32_to_sint32 0x3320646eul);
  st.(2ul)  <- (uint32_to_sint32 0x79622d32ul);
  st.(3ul)  <- (uint32_to_sint32 0x6b206574ul)


[@ "substitute"]
private
val constant_setup:
  c:Buffer.buffer H32.t{length c = 4} ->
  Stack unit
    (requires (fun h -> live h c))
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_1 c h0 h1
      /\ reveal_h32s (as_seq h1 c) == Seq.Create.create_4 c0 c1 c2 c3))
[@ "substitute"]
let constant_setup st =
  constant_setup_ st;
  let h = ST.get() in
  Seq.lemma_eq_intro (reveal_h32s (as_seq h st)) (Seq.Create.create_4 c0 c1 c2 c3)


[@ "substitute"]
private
val keysetup:
  st:Buffer.buffer H32.t{length st = 8} ->
  k:uint8_p{length k = 32 /\ disjoint st k} ->
  Stack unit
    (requires (fun h -> live h st /\ live h k))
    (ensures  (fun h0 _ h1 -> live h0 st /\ live h0 k /\ live h1 st /\ modifies_1 st h0 h1
      /\ (let s = reveal_h32s (as_seq h1 st) in
         let k = reveal_sbytes (as_seq h0 k) in
         s == Spec.Lib.uint32s_from_le 8 k)))
[@ "substitute"]
let keysetup st k =
  uint32s_from_le_bytes st k 8ul


[@ "substitute"]
private
val ivsetup:
  st:buffer H32.t{length st = 3} ->
  iv:uint8_p{length iv = 12 /\ disjoint st iv} ->
  Stack unit
    (requires (fun h -> live h st /\ live h iv))
    (ensures  (fun h0 _ h1 -> live h1 st /\ modifies_1 st h0 h1 /\ live h0 iv
      /\ (let s = reveal_h32s (as_seq h1 st) in
         let iv = reveal_sbytes (as_seq h0 iv) in
         s == Spec.Lib.uint32s_from_le 3 iv) ))
[@ "substitute"]
let ivsetup st iv =
  uint32s_from_le_bytes st iv 3ul
>>>>>>> master

(* Definition of the state *)
type state = lbuffer uint32 16

[@ "substitute"]
private
val line: st:state -> a:idx -> b:idx -> d:idx -> s:rotval U32 ->
  Stack unit
    (requires (fun h -> live h st))
<<<<<<< HEAD
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st h0 h1 /\
			   as_lseq st h1 == Spec.line a b d s (as_lseq st h0)))
=======
    (ensures  (fun h0 _ h1 -> live h1 st /\ modifies_1 st h0 h1
      /\ (let s = as_seq h1 st in
         s == Spec.Lib.singleton (uint32_to_sint32 ctr)) ))
[@ "substitute"]
let ctrsetup st ctr =
  st.(0ul) <- uint32_to_sint32 ctr;
  let h = ST.get() in
  Seq.lemma_eq_intro (Spec.Lib.singleton (uint32_to_sint32 ctr)) (as_seq h st)


private val lemma_setup: h:mem -> st:state{live h st} -> Lemma
  (as_seq h st == FStar.Seq.(as_seq h (Buffer.sub st 0ul 4ul) @| as_seq h (Buffer.sub st 4ul 8ul)
                           @| as_seq h (Buffer.sub st 12ul 1ul) @| as_seq h (Buffer.sub st 13ul 3ul)))
private let lemma_setup h st =
  let s = as_seq h st in
  Seq.lemma_eq_intro (Seq.slice s 0 4) (as_seq h (Buffer.sub st 0ul 4ul));
  Seq.lemma_eq_intro (Seq.slice s 4 12) (as_seq h (Buffer.sub st 4ul 8ul));
  Seq.lemma_eq_intro (Seq.slice s 12 13) (as_seq h (Buffer.sub st 12ul 1ul));
  Seq.lemma_eq_intro (Seq.slice s 13 16) (as_seq h (Buffer.sub st 13ul 3ul));
  Seq.lemma_eq_intro s (FStar.Seq.(slice s 0 4 @| slice s 4 12 @| slice s 12 13 @| slice s 13 16))

#reset-options "--max_fuel 0 --z3rlimit 100"

[@ "substitute"]
val setup:
  st:state ->
  k:uint8_p{length k = 32 /\ disjoint st k} ->
  n:uint8_p{length n = 12 /\ disjoint st n} ->
  c:U32.t ->
  Stack unit
    (requires (fun h -> live h st /\ live h k /\ live h n))
    (ensures (fun h0 _ h1 -> live h0 k /\ live h0 n /\ live h1 st /\ modifies_1 st h0 h1
      /\ (let s = reveal_h32s (as_seq h1 st) in
         let k = reveal_sbytes (as_seq h0 k) in
         let n = reveal_sbytes (as_seq h0 n) in
         s == setup k n (U32.v c))))
[@ "substitute"]
let setup st k n c =
  let h0 = ST.get() in
  let stcst = Buffer.sub st 0ul 4ul in
  let stk   = Buffer.sub st 4ul 8ul in
  let stc   = Buffer.sub st 12ul 1ul in
  let stn   = Buffer.sub st 13ul 3ul in
  constant_setup stcst;
  let h1 = ST.get() in
  keysetup stk k;
  let h2 = ST.get() in
  ctrsetup stc c;
  let h3 = ST.get() in
  ivsetup stn n;
  let h4 = ST.get() in
  no_upd_lemma_1 h0 h1 stcst stk;
  no_upd_lemma_1 h0 h1 stcst stn;
  no_upd_lemma_1 h0 h1 stcst stc;
  no_upd_lemma_1 h1 h2 stk stcst;
  no_upd_lemma_1 h1 h2 stk stn;
  no_upd_lemma_1 h1 h2 stk stc;
  no_upd_lemma_1 h2 h3 stc stcst;
  no_upd_lemma_1 h2 h3 stc stk;
  no_upd_lemma_1 h2 h3 stc stn;
  no_upd_lemma_1 h3 h4 stn stcst;
  no_upd_lemma_1 h3 h4 stn stk;
  no_upd_lemma_1 h3 h4 stn stc;
  lemma_setup h4 st;
  Seq.lemma_eq_intro (reveal_h32s (as_seq h4 st)) (Spec.setup (reveal_sbytes (as_seq h0 k)) (reveal_sbytes (as_seq h0 n)) (U32.v c))


let idx = a:U32.t{U32.v a < 16}

[@ "substitute"]
private
val line:
  st:state ->
  a:idx -> b:idx -> d:idx -> s:U32.t{0 < U32.v s && U32.v s < 32} ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h1 st /\ modifies_1 st h0 h1 /\ live h0 st
      /\ (let st1 = reveal_h32s (as_seq h1 st) in
         let st0 = reveal_h32s (as_seq h0 st) in
         st1 == line (U32.v a) (U32.v b) (U32.v d) s st0)))
>>>>>>> master
[@ "substitute"]
let line st a b d s =
  let sa = st.(a) in let sb = st.(b) in
  st.(a) <- sa +. sb;
  let sd = st.(d) in let sa = st.(a) in
  let sda = sd ^. sa in
  st.(d) <- sda <<<. s


[@ "c_inline"]
private
val quarter_round: st:state -> a:idx -> b:idx -> c:idx -> d:idx ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st h0 h1 /\
			  as_lseq st h1 == Spec.quarter_round a b c d (as_lseq  st h0 )))
		  
[@ "c_inline"]
let quarter_round st a b c d =
  line st a b d (u32 16);
  line st c d b (u32 12);
  line st a b d (u32 8) ;
  line st c d b (u32 7)

[@ "substitute"]
private
val column_round:
  st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st h0 h1 /\
	     as_lseq st h1 == Spec.column_round (as_lseq st h0)))
[@ "substitute"]
let column_round st =
  quarter_round st 0 4 8  12;
  quarter_round st 1 5 9  13;
  quarter_round st 2 6 10 14;
  quarter_round st 3 7 11 15

[@ "substitute"]
private
val diagonal_round: st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st h0 h1 /\
       as_lseq st h1 == Spec.diagonal_round (as_lseq st h0)))
[@ "substitute"]
let diagonal_round st =
  quarter_round st 0 5 10 15;
  quarter_round st 1 6 11 12;
  quarter_round st 2 7 8  13;
  quarter_round st 3 4 9  14


[@ "c_inline"]
private
val double_round: st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st h0 h1 /\
		 as_lseq st h1 == Spec.double_round (as_lseq st h0)))
[@ "c_inline"]
let double_round st =
  column_round st;
  diagonal_round st


[@ "c_inline"]
val rounds: st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st h0 h1 /\
		 as_lseq st h1 == Spec.rounds (as_lseq st h0)))
let rounds st =
  iter 10 Spec.double_round double_round st


val copy_state: o:state -> i:state -> Stack unit 
		(requires (fun h -> live h o /\ live h i))
		(ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 o h0 h1 /\
			       as_lseq o h1 == as_lseq i h0))
let copy_state o i = 
  admit();
  blit i 0 o 0 16

[@ "c_inline"]
private
val chacha20_core:
  k:state ->
  st:state ->
  ctr:size_t ->
  Stack unit
    (requires (fun h -> live h k /\ live h st /\ disjoint st k))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies2 st k h0 h1 /\
			  (let s = as_lseq st h0 in
			   let s = Spec.Lib.IntSeq.(s.[12] <- (u32 ctr)) in
			   as_lseq k h1 == Spec.chacha20_core s)))
[@ "c_inline"]
let chacha20_core k st ctr =
  st.(12) <- u32 ctr;
  copy_state k st;
  rounds k;
  map2 (fun x y -> x +. y) k st

[@ "c_inline"]
val setup:
  st:state ->
  k:lbuffer uint8 32 ->
  n:lbuffer uint8 12 ->
  c:size_t ->
  Stack unit
    (requires (fun h -> live h st /\ live h k /\ live h n
                    /\ disjoint k st /\ disjoint n st))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st h0 h1
                       /\ as_lseq st h1 == 
			 Spec.setup (as_lseq k h0) (as_lseq n h0) c (as_lseq st h0)))

#reset-options "--z3rlimit 50 --max_fuel 0"
[@ "c_inline"]
let setup st k n c =
  st.(0) <- u32 Spec.c0;
  st.(1) <- u32 Spec.c1;
  st.(2) <- u32 Spec.c2;
  st.(3) <- u32 Spec.c3;
  let st_k = sub st 4 8 in
  uint32s_from_bytes_le #8 st_k k;
  st.(12) <- u32 c;
  let st_n = sub st 13 3 in
  uint32s_from_bytes_le #3 st_n n 


[@ "c_inline"]
val chacha20_block:
  stream_block:lbuffer uint8 64 ->
  st:state ->
  ctr:size_t ->
  Stack unit
    (requires (fun h -> live h stream_block /\ 
		     live h st /\ 
		     disjoint stream_block st))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies2 st stream_block h0 h1))

#reset-options "--z3rlimit 100"
[@ "c_inline"]
let chacha20_block stream_block st ctr =
  let bufs = [BufItem st; BufItem stream_block] in
  let spec h0 r h1 = True in
  let impl st' : Stack unit
    (requires (fun h -> live h st' /\ live_list h bufs /\ disjoint_list st' bufs))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies3 st' st stream_block h0 h1))
  = 
    chacha20_core st' st ctr;
    uint32s_to_bytes_le #16 stream_block st' in
  alloc 16 (u32 0) bufs spec impl
    


(*
[@ "c_inline"]
val init:
  st:state ->
  k:lbuffer uint8 32 ->
  n:lbuffer uint8 12 ->
  Stack log_t
    (requires (fun h -> live h k /\ live h n /\ live h st /\ disjoint st k /\ disjoint st n /\ disjoint k n))
    (ensures  (fun h0 log h1 -> preserves_live h0 h1 /\ modifies1 st h0 h1))
      // /\ invariant log h1 st
      // /\ (match Ghost.reveal log with MkLog k' n' -> k' == reveal_sbytes (as_seq h0 k)
      //      /\ n' == reveal_sbytes (as_seq h0 n))))

[@ "c_inline"]
let init st k n =
  setup st k n 0;
  let h = ST.get() in
  Ghost.elift2 (fun (k:lbuffer uint8 32) (n:lbuffer uint8 12) -> MkLog (as_lseq k h) (as_lseq n h)) (Ghost.hide k) (Ghost.hide n)


(*
#reset-options " --max_fuel 0 --z3rlimit 100"

val lemma_chacha20_counter_mode_1:
  ho:mem -> output:uint8_p{live ho output} ->
  hi:mem -> input:uint8_p{live hi input} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length input /\ U32.v len < 64 /\ U32.v len > 0} ->
  k:Spec.key -> n:Spec.nonce -> ctr:UInt32.t{UInt32.v ctr + (length input / 64) < pow2 32} -> Lemma
    (Spec.CTR.counter_mode chacha20_ctx chacha20_cipher k n (UInt32.v ctr) (reveal_sbytes (as_seq hi input))
     == Spec.CTR.xor #(UInt32.v len) (reveal_sbytes (as_seq hi input)) (Seq.slice (Spec.chacha20_block k n (UInt32.v ctr)) 0 (U32.v len)))
#reset-options "--max_fuel 0 --z3rlimit 100"
let lemma_chacha20_counter_mode_1 ho output hi input len k n ctr =
  Math.Lemmas.lemma_div_mod (UInt32.v len) 64;
  Math.Lemmas.modulo_lemma (UInt32.v len) 64;
  assert(UInt32.v len / (Spec.CTR.(chacha20_ctx.blocklen * chacha20_ctx.incr)) = 0);
  let open Spec.CTR in
  assert((xor #(UInt32.v len) (reveal_sbytes (as_seq hi input)) (Seq.slice (Spec.chacha20_block k n (UInt32.v ctr)) 0 (UInt32.v len))) == seq_map2 (fun x y -> FStar.UInt8.(x ^^ y)) (reveal_sbytes (as_seq hi input)) (Seq.slice (Spec.chacha20_block k n (UInt32.v ctr)) 0 (UInt32.v len)));
  let ctx = chacha20_ctx in
  let len:nat = UInt32.v len in
  let counter = UInt32.v ctr in
  let blocks_len = (ctx.incr * ctx.blocklen) * (len / (ctx.blocklen * ctx.incr)) in
  let part_len   = len % (ctx.blocklen * ctx.incr) in
    (* TODO: move to a single lemma for clarify *)
    Math.Lemmas.lemma_div_mod len (ctx.blocklen * ctx.incr);
    Math.Lemmas.multiple_modulo_lemma (len / (ctx.blocklen * ctx.incr)) (ctx.blocklen * ctx.incr);
    Math.Lemmas.lemma_div_le (blocks_len) len ctx.blocklen;
    (* End TODO *)
  let blocks, last_block = Seq.split (as_seq hi input) blocks_len in
  let cipher_blocks = counter_mode_blocks ctx chacha20_cipher k n counter (reveal_sbytes blocks) in
  Seq.lemma_eq_intro cipher_blocks Seq.createEmpty;
  assert(ctx.incr * (Seq.length (as_seq hi input) / ctx.blocklen) = 0);
  Seq.lemma_eq_intro (Seq.append Seq.createEmpty (xor #len (reveal_sbytes (as_seq hi input)) (Seq.slice (Spec.chacha20_block k n (UInt32.v ctr)) 0 len))) (xor #len (reveal_sbytes (as_seq hi input)) (Seq.slice (Spec.chacha20_block k n (UInt32.v ctr)) 0 len));
  Seq.lemma_eq_intro (Spec.CTR.counter_mode chacha20_ctx chacha20_cipher k n (UInt32.v ctr) (reveal_sbytes (as_seq hi input)))
                     (Spec.CTR.xor #(len) (reveal_sbytes (as_seq hi input)) (Seq.slice (Spec.chacha20_block k n (UInt32.v ctr)) 0 (len)))


#reset-options " --max_fuel 0 --z3rlimit 100"

val lemma_chacha20_counter_mode_2:
  ho:mem -> output:uint8_p{live ho output} ->
  hi:mem -> input:uint8_p{live hi input} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length input /\ U32.v len >= 64
    /\ UInt32.v len % 64 = 0} ->
  k:Spec.key -> n:Spec.nonce -> ctr:UInt32.t{UInt32.v ctr + (length input / 64) < pow2 32} -> Lemma
    (Spec.CTR.counter_mode_blocks chacha20_ctx chacha20_cipher k n (UInt32.v ctr)
                                  (reveal_sbytes (as_seq hi input))
    == (let prefix, block = Seq.split (as_seq hi input) (UInt32.v len - 64) in
      Math.Lemmas.lemma_mod_plus (Seq.length prefix) 1 (64);
      Math.Lemmas.lemma_div_le (Seq.length prefix) (UInt32.v len) 64;
      Spec.CTR.Lemmas.lemma_div (UInt32.v len) (64);
    let cipher        = Spec.CTR.counter_mode_blocks chacha20_ctx chacha20_cipher k n (UInt32.v ctr) (reveal_sbytes prefix) in
    let mask          = chacha20_cipher k n (UInt32.v ctr + (UInt32.v len / 64 - 1) ) in
    let eb            = Spec.CTR.xor (reveal_sbytes block) mask in
    Seq.append cipher eb))
#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 100"
let lemma_chacha20_counter_mode_2 ho output hi input len k n ctr = ()


#reset-options " --max_fuel 0 --z3rlimit 100"

val lemma_chacha20_counter_mode_0:
  ho:mem -> output:uint8_p{live ho output} ->
  hi:mem -> input:uint8_p{live hi input} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length input /\ U32.v len = 0} ->
  k:Spec.key -> n:Spec.nonce -> ctr:UInt32.t{UInt32.v ctr + (length input / 64) < pow2 32} -> Lemma
    (Spec.CTR.counter_mode_blocks chacha20_ctx chacha20_cipher k n (UInt32.v ctr)
                                  (reveal_sbytes (as_seq hi input))
     == Seq.createEmpty)
#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 100"
let lemma_chacha20_counter_mode_0 ho output hi input len k n ctr =
  Seq.lemma_eq_intro (as_seq ho output) Seq.createEmpty
*)

#reset-options " --max_fuel 0 --z3rlimit 400"

<<<<<<< HEAD
val update_last:
  len:size_t{0 < len /\ len < 64} ->
  output:lbuffer uint8 len ->
  plain:lbuffer uint8 len ->
  log:log_t ->
  st:state ->
  ctr:size_t{ctr + (len / 64) <= max_size_t} ->
  Stack log_t
    (requires (fun h -> live h output /\ live h plain /\ disjoint output plain /\ disjoint st output /\ disjoint st plain)) //invariant log h st))
    (ensures (fun h0 updated_log h1 -> preserves_live h0 h1 /\ modifies2 output st h0 h1))
      // live h1 output /\ live h0 plain /\ invariant updated_log h1 st
      // /\ (let o = reveal_sbytes (as_seq h1 output) in
      //    let plain = reveal_sbytes (as_seq h0 plain) in
      //    match Ghost.reveal log with | MkLog k n ->
      //    o == (let mask = chacha20_cipher k n (UInt32.v ctr+(UInt32.v len / 64)) in
      //          let mask = Seq.slice mask 0 (UInt32.v len) in
      //          Spec.CTR.xor #(UInt32.v len) plain mask))))

let update_last len output plain log st ctr =
  (**) let h0 = ST.get() in
  push_frame();
  (**) let h1 = ST.get() in
  // BB. Fix this temporary bypass
  assume(modifies0 h0 h1);
  let block = create 64 (u8 0) in
  (**) let h2 = ST.get() in
  (**) assume(disjoint block st);
  (**) assume(live h2 st);
  (**) assume(disjoint block plain);
  (**) assume(live h2 plain);
  (**) assume(disjoint block output);
  (**) assume(live h2 output);
  let l = chacha20_block log block st ctr in
  (**) let h3 = ST.get() in
  let mask = sub block 0 len in
  (**) let h4 = ST.get () in
  // BB. This is highly unlikely to work !
  // map2 has to be changed
  map2 (fun x y -> x ^. y) output plain;
  map2 (fun x y -> x ^. y) output mask;
  (**) let h5 = ST.get() in
  pop_frame();
  (**) let h6 = ST.get() in
  (**) assume(modifies0 h5 h6);
  (**) assume (modifies0 h0 h1 /\ modifies1 block h1 h2 /\ modifies2 block st h2 h3 /\ modifies0 h3 h4 /\ modifies1 output h4 h5 /\ modifies0 h5 h6 ==> modifies2 output st h0 h6);
  l

=======
>>>>>>> master

val update:
  output:lbuffer uint8 64 ->
  plain:lbuffer uint8 64->
  log:log_t ->
  st:state ->
  ctr:size_t{ctr + 1 <= max_size_t} ->
  Stack log_t
    (requires (fun h -> live h output /\ live h plain /\ disjoint st output /\ disjoint st plain)) //invariant log h st))
    (ensures (fun h0 updated_log h1 -> live h1 output /\ live h0 plain /\ modifies2 output st h0 h1))
      // /\ invariant updated_log h1 st
      // /\ modifies_2 output st h0 h1
      // /\ updated_log == log
      // /\ (let o = reveal_sbytes (as_seq h1 output) in
      //    let plain = reveal_sbytes (as_seq h0 plain) in
      //    match Ghost.reveal log with | MkLog k n ->
      //    o == seq_map2 (fun x y -> FStar.UInt8.(x ^^ y)) plain (chacha20_cipher k n (U32.v ctr)))))

let update output plain log st ctr =
  (**) let h0 = ST.get() in
  push_frame();
  (**) let h1 = ST.get() in
  let b  = create 48 (u32 0) in
  (**) let h2 = ST.get() in
  let k  = sub b 0  16 in
  let ib = sub b 16 16 in
  let ob = sub b 32 16 in
  let l  = chacha20_core log k st ctr in
  (**) let h3 = ST.get() in
  // (**) modifies_subbuffer_2 h2 h3 k st b;
  uint32s_from_bytes_le 16 ib plain;
  (**) let h  = ST.get() in
  // (**) modifies_subbuffer_1 h3 h ib b;
  map2 (fun x y -> x ^. y) ob ib;
  map2 (fun x y -> x ^. y) ob k;
  // map2 ob ib k 16 (fun x y -> x ^. y);
  (**) let h4  = ST.get() in
  // (**) modifies_subbuffer_1 h h4 ob b;
  // (**) lemma_modifies_1_trans b h3 h h4;
  // (**) lemma_modifies_2_1' b st h2 h3 h4;
  // (**) lemma_modifies_0_2 st b h1 h2 h4;
  uint32s_to_bytes_le 16 output ob;
  (**) let h5  = ST.get() in
  // (**) lemma_modifies_2_1'' st output h1 h4 h5;
  // Hacl.Impl.Xor.Lemmas.lemma_xor_uint32s_to_bytes (reveal_sbytes (as_seq h0 plain))
  //                                                      (reveal_h32s (as_seq h k));
  pop_frame();
  (**) let h6 = ST.get() in
  // (**) modifies_popped_3_2 st output h0 h1 h5 hfin;
  l

<<<<<<< HEAD
(*
=======
val update_last:
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length plain /\ U32.v len < 64 /\ UInt32.v len > 0} ->
  log:log_t ->
  st:state{disjoint st output /\ disjoint st plain} ->
  ctr:UInt32.t{UInt32.v ctr + (length plain / 64) < pow2 32} ->
  Stack log_t
    (requires (fun h -> live h output /\ live h plain /\ invariant log h st))
    (ensures (fun h0 updated_log h1 -> live h1 output /\ live h0 plain /\ invariant updated_log h1 st
      /\ modifies_2 output st h0 h1
      /\ (let o = reveal_sbytes (as_seq h1 output) in
         let plain = reveal_sbytes (as_seq h0 plain) in
         match Ghost.reveal log with | MkLog k n ->
         o == (let mask = chacha20_cipher k n (UInt32.v ctr+(UInt32.v len / 64)) in
               let mask = Seq.slice mask 0 (UInt32.v len) in
               Spec.CTR.xor #(UInt32.v len) plain mask))))
let update_last output plain len log st ctr =
  (**) let h0 = ST.get() in
  push_frame();
  (**) let h = ST.get() in
  let block = create (uint8_to_sint8 0uy) 64ul in
  (**) let h' = ST.get() in
  let l = chacha20_block log block st ctr in
  (**) let h'' = ST.get() in
  (**) lemma_modifies_0_2' st block h h' h'';
  let mask = Buffer.sub block 0ul len in
  map2 output plain mask len (fun x y -> H8.(x ^^ y));
  (**) let h1 = ST.get() in
  (**) lemma_modifies_2_1'' st output h h'' h1;
  (**) lemma_chacha20_counter_mode_1 h1 output h0 plain len (Ghost.reveal log).k (Ghost.reveal log).n ctr;
  pop_frame();
  (**) let hfin = ST.get() in
  (**) modifies_popped_3_2 st output h0 h h1 hfin;
  l


>>>>>>> master
#reset-options " --max_fuel 0 --z3rlimit 100"

private
val lemma_aux_modifies_2: #a:Type -> #a':Type -> h:mem -> b:buffer a{live h b} -> b':buffer a'{live h b'} -> Lemma
  (requires (True))
  (ensures (modifies_2 b b' h h))
let lemma_aux_modifies_2 #a #a' h b b' =
  lemma_intro_modifies_2 b b' h h

private
val lemma_chacha20_counter_mode_def_0:
  s:Seq.seq Hacl.UInt8.t{Seq.length s = 0} ->
  k:Spec.key -> n:Spec.nonce -> ctr:UInt32.t{UInt32.v ctr < pow2 32} -> Lemma
    (Spec.CTR.counter_mode_blocks chacha20_ctx chacha20_cipher k n (UInt32.v ctr)
                                  (reveal_sbytes s)
     == Seq.createEmpty)
#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 100"
let lemma_chacha20_counter_mode_def_0 s k n ctr =
  Seq.lemma_eq_intro s Seq.createEmpty

*)
#reset-options "--max_fuel 0  --z3rlimit 200"

private
val chacha20_counter_mode_blocks:
<<<<<<< HEAD
  len:size_t ->
  output:lbuffer uint8 len ->
  plain:lbuffer uint8 len ->
=======
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  num_blocks:UInt32.t{64 * UInt32.v num_blocks = length output /\ length output = length plain} ->
>>>>>>> master
  log:log_t ->
  st:state ->
  ctr:size_t{ctr + (len / 64) <= max_size_t} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain
              /\ disjoint output plain /\ disjoint st output /\ disjoint st plain)) ///\ invariant log h st))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies2 output st h0 h1))
      // live h1 output /\ live h0 plain /\ live h1 st
      // /\ modifies_2 output st h0 h1 /\ invariant log h1 st
      // /\ (let o = reveal_sbytes (as_seq h1 output) in
      //    let plain = reveal_sbytes (as_seq h0 plain) in
      //    match Ghost.reveal log with | MkLog k n ->
      //    o == Spec.CTR.counter_mode_blocks chacha20_ctx chacha20_cipher k n (UInt32.v ctr) plain)))
#reset-options "--max_fuel 0 --z3rlimit 200"
let chacha20_counter_mode_blocks output plain num_blocks log st ctr =
  let h0 = ST.get() in
<<<<<<< HEAD
  let inv (h1: mem) (i: nat): Type0 = preserves_live h0 h1 /\ modifies2 output st h0 h1 /\ 0 <= i /\ i <= len in
  //   live h1 output /\ invariant log h1 st /\ modifies_2 output st h0 h1 /\ 0 <= i /\ i <= UInt32.v len
  //   /\ (match Ghost.reveal log with | MkLog k n ->
  //     reveal_sbytes (Seq.slice (as_seq h1 output) 0 (64 * i))
  //     == Spec.CTR.counter_mode_blocks chacha20_ctx chacha20_cipher k n (UInt32.v ctr) (reveal_sbytes (Seq.slice (as_seq h0 plain) 0 (64 * i))))
  // in
  let f' (i:size_t{0 <= i /\ i < len}): Stack unit
    (requires (fun h -> inv h i))
    (ensures (fun h1 _ h2 -> inv h2 (i + 1)))
  =
    // let h = ST.get() in
    // let open FStar.UInt32 in
    let o'' = sub output 0 (64 * i + 64) in
    let b'' = sub plain  0 (64 * i + 64) in
    let b  = sub plain (64 * i) 64 in
    let b' = sub plain 0 (64 * i)  in
    let o  = sub output (64 * i) 64 in
    let o' = sub output 0 (64 * i)  in
    let log' = update o b log st (ctr + i) in
    // let h' = ST.get() in
    // (**) modifies_subbuffer_2 h h' o st output;
    // (**) lemma_modifies_2_trans output st h0 h h';
    // no_upd_lemma_2 h h' o st b;
    // no_upd_lemma_2 h h' o st b';
    // no_upd_lemma_2 h h' o st o';
    // Seq.lemma_eq_intro (Seq.slice (as_seq h' output) 0 (64 * v i + 64))
    //                    (as_seq h' (Buffer.sub output 0ul (64ul *^ i +^ 64ul)));
    // Seq.lemma_eq_intro (Seq.slice (as_seq h0 plain) 0 (64 * v i + 64))
    //                    (as_seq h0 (Buffer.sub plain 0ul (64ul *^ i +^ 64ul)));
    // Seq.lemma_eq_intro (Seq.slice (as_seq h' output) 0 (64 * v i))
    //                    (Seq.slice (Seq.slice (as_seq h' output) 0 (64 * v i + 64)) 0 (64 * v i));
    // Seq.lemma_eq_intro (Seq.slice (as_seq h' output) (64 * v i) (64 * v i + 64))
    //                    (Seq.slice (Seq.slice (as_seq h' output) 0 (64 * v i + 64)) (64 * v i) (64 * v i + 64));
    // Seq.lemma_eq_intro (Seq.slice (as_seq h0 plain) 0 (64 * v i))
    //                    (Seq.slice (Seq.slice (as_seq h0 plain) 0 (64 * v i + 64)) 0 (64 * v i));
    // Seq.lemma_eq_intro (Seq.slice (as_seq h0 plain) (64 * v i) (64 * v i + 64))
    //                    (Seq.slice (Seq.slice (as_seq h0 plain) 0 (64 * v i + 64)) (64 * v i) (64 * v i + 64));
    // Seq.lemma_eq_intro (Seq.slice (as_seq h0 plain) 0 (64 * v i + 64))
    //                    (Seq.append (Seq.slice (as_seq h0 plain) 0 (64 * v i)) (Seq.slice (as_seq h0 plain) (64 * v i) (64 * v i + 64)));
    // Seq.lemma_eq_intro (Seq.slice (as_seq h' output) 0 (64 * v i + 64))
    //                    (Seq.append (Seq.slice (as_seq h' output) 0 (64 * v i)) (Seq.slice (as_seq h' output) (64 * v i) (64 * v i + 64)));
    // lemma_chacha20_counter_mode_2 h o'' h0 b'' (64ul *^ i +^ 64ul) (MkLog?.k (Ghost.reveal log)) (MkLog?.n (Ghost.reveal log)) ctr
  // in
  let o0 = sub output 0 0 in
  let i0 = sub plain  0 0 in
  // Seq.lemma_eq_intro (as_seq h0 o0) (Seq.slice (as_seq h0 output) 0 0);
  // Seq.lemma_eq_intro (as_seq h0 i0) (Seq.slice (as_seq h0 plain) 0 0);
  // lemma_aux_modifies_2 h0 output st;
  // lemma_chacha20_counter_mode_def_0 (Seq.slice (as_seq h0 plain) 0 0) (Ghost.reveal log).k (Ghost.reveal log).n ctr;
  // Seq.lemma_eq_intro (Seq.slice (as_seq h0 plain) 0 0) Seq.createEmpty;
  // Seq.lemma_eq_intro (Seq.slice (as_seq h0 output) 0 0) Seq.createEmpty;
  repeati 0 len inv f';
  // let h = ST.get() in
  // Seq.lemma_eq_intro (Seq.slice (as_seq h output) 0 (64 * UInt32.v len)) (as_seq h output);
  // Seq.lemma_eq_intro (Seq.slice (as_seq h0 plain) 0 (64 * UInt32.v len)) (as_seq h plain)
  ()
=======
  let inv (h1: mem) (i: nat): Type0 =
    live h1 output /\ invariant log h1 st /\ modifies_2 output st h0 h1 /\ 0 <= i /\ i <= UInt32.v num_blocks
    /\ (match Ghost.reveal log with | MkLog k n ->
      reveal_sbytes (Seq.slice (as_seq h1 output) 0 (64 * i))
      == Spec.CTR.counter_mode_blocks chacha20_ctx chacha20_cipher k n (UInt32.v ctr) (reveal_sbytes (Seq.slice (as_seq h0 plain) 0 (64 * i))))
  in
  let f' (i:UInt32.t{ FStar.UInt32.( 0 <= v i /\ v i < v num_blocks ) }): Stack unit
    (requires (fun h -> inv h (UInt32.v i)))
    (ensures (fun h_1 _ h_2 -> FStar.UInt32.(inv h_2 (v i + 1))))
  = let h = ST.get() in
    let open FStar.UInt32 in
    let o'' = Buffer.sub output 0ul (64ul *^ i +^ 64ul) in
    let b'' = Buffer.sub plain  0ul (64ul *^ i +^ 64ul) in
    let b  = Buffer.sub plain (64ul *^ i) 64ul in
    let b' = Buffer.sub plain 0ul (64ul *^ i)  in
    let o  = Buffer.sub output (64ul *^ i) 64ul in
    let o' = Buffer.sub output 0ul (64ul *^ i)  in
    let log' = update o b log st FStar.UInt32.(ctr+^ i) in
    let h' = ST.get() in
    (**) modifies_subbuffer_2 h h' o st output;
    (**) lemma_modifies_2_trans output st h0 h h';
    no_upd_lemma_2 h h' o st b;
    no_upd_lemma_2 h h' o st b';
    no_upd_lemma_2 h h' o st o';
    Seq.lemma_eq_intro (Seq.slice (as_seq h' output) 0 (64 * v i + 64))
                       (as_seq h' (Buffer.sub output 0ul (64ul *^ i +^ 64ul)));
    Seq.lemma_eq_intro (Seq.slice (as_seq h0 plain) 0 (64 * v i + 64))
                       (as_seq h0 (Buffer.sub plain 0ul (64ul *^ i +^ 64ul)));
    Seq.lemma_eq_intro (Seq.slice (as_seq h' output) 0 (64 * v i))
                       (Seq.slice (Seq.slice (as_seq h' output) 0 (64 * v i + 64)) 0 (64 * v i));
    Seq.lemma_eq_intro (Seq.slice (as_seq h' output) (64 * v i) (64 * v i + 64))
                       (Seq.slice (Seq.slice (as_seq h' output) 0 (64 * v i + 64)) (64 * v i) (64 * v i + 64));
    Seq.lemma_eq_intro (Seq.slice (as_seq h0 plain) 0 (64 * v i))
                       (Seq.slice (Seq.slice (as_seq h0 plain) 0 (64 * v i + 64)) 0 (64 * v i));
    Seq.lemma_eq_intro (Seq.slice (as_seq h0 plain) (64 * v i) (64 * v i + 64))
                       (Seq.slice (Seq.slice (as_seq h0 plain) 0 (64 * v i + 64)) (64 * v i) (64 * v i + 64));
    Seq.lemma_eq_intro (Seq.slice (as_seq h0 plain) 0 (64 * v i + 64))
                       (Seq.append (Seq.slice (as_seq h0 plain) 0 (64 * v i)) (Seq.slice (as_seq h0 plain) (64 * v i) (64 * v i + 64)));
    Seq.lemma_eq_intro (Seq.slice (as_seq h' output) 0 (64 * v i + 64))
                       (Seq.append (Seq.slice (as_seq h' output) 0 (64 * v i)) (Seq.slice (as_seq h' output) (64 * v i) (64 * v i + 64)));
    lemma_chacha20_counter_mode_2 h o'' h0 b'' (64ul *^ i +^ 64ul) (MkLog?.k (Ghost.reveal log)) (MkLog?.n (Ghost.reveal log)) ctr
  in
  let o0 = Buffer.sub output 0ul 0ul in
  let i0 = Buffer.sub plain  0ul 0ul in
  Seq.lemma_eq_intro (as_seq h0 o0) (Seq.slice (as_seq h0 output) 0 0);
  Seq.lemma_eq_intro (as_seq h0 i0) (Seq.slice (as_seq h0 plain) 0 0);
  lemma_aux_modifies_2 h0 output st;
  lemma_chacha20_counter_mode_def_0 (Seq.slice (as_seq h0 plain) 0 0) (Ghost.reveal log).k (Ghost.reveal log).n ctr;
  Seq.lemma_eq_intro (Seq.slice (as_seq h0 plain) 0 0) Seq.createEmpty;
  Seq.lemma_eq_intro (Seq.slice (as_seq h0 output) 0 0) Seq.createEmpty;
  C.Loops.for 0ul num_blocks inv f';
  let h = ST.get() in
  Seq.lemma_eq_intro (Seq.slice (as_seq h output) 0 (64 * UInt32.v num_blocks)) (as_seq h output);
  Seq.lemma_eq_intro (Seq.slice (as_seq h0 plain) 0 (64 * UInt32.v num_blocks)) (as_seq h plain)

>>>>>>> master

(*
val chacha20_counter_mode:
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length plain} ->
  log:log_t ->
  st:state{disjoint st output /\ disjoint st plain} ->
  ctr:UInt32.t{UInt32.v ctr + (length plain / 64) < pow2 32} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain /\ invariant log h st))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h0 plain /\ live h1 st
      /\ modifies_2 output st h0 h1
      /\ (let o = reveal_sbytes (as_seq h1 output) in
         let plain = reveal_sbytes (as_seq h0 plain) in
         match Ghost.reveal log with | MkLog k n ->
         o == Spec.CTR.counter_mode chacha20_ctx chacha20_cipher k n (UInt32.v ctr) plain)))
#reset-options "--max_fuel 0 --z3rlimit 100"
let chacha20_counter_mode output plain len log st ctr =
  assert_norm(pow2 6 = 64);
  let open FStar.UInt32 in
  let blocks_len = (len >>^ 6ul) in
  let part_len   = len &^ 0x3ful in
  UInt.logand_mask (UInt32.v len) 6;
  Math.Lemmas.lemma_div_mod (UInt32.v len) 64;
  (**) let h0 = ST.get() in
  let output' = Buffer.sub output 0ul (64ul *^ blocks_len) in
  let plain'  = Buffer.sub plain  0ul (64ul *^ blocks_len) in
  let output'' = Buffer.sub output (64ul *^ blocks_len) part_len in
  let plain''  = Buffer.sub plain  (64ul *^ blocks_len) part_len in
  chacha20_counter_mode_blocks output' plain' blocks_len log st ctr;
  (**) let h1 = ST.get() in
  (**) modifies_subbuffer_2 h0 h1 output' st output;
  if FStar.UInt32.(part_len >^ 0ul) then (
    let _ = update_last output'' plain'' part_len log st FStar.UInt32.(ctr +^ blocks_len) in
    (**) let h' = ST.get() in
    (**) modifies_subbuffer_2 h1 h' output'' st output)
  else
    (**) lemma_modifies_sub_2 h1 h1 output st;
  let h = ST.get() in
  (**) lemma_modifies_2_trans output st h0 h1 h;
  Seq.lemma_eq_intro (Seq.append (as_seq h output') Seq.createEmpty) (as_seq h output');
  Seq.lemma_eq_intro (as_seq h output) (Seq.append (as_seq h output') (as_seq h output''));
  Seq.lemma_eq_intro (as_seq h0 plain) (Seq.append (as_seq h0 plain') (as_seq h0 plain''));
  Seq.lemma_eq_intro (reveal_sbytes (as_seq h output)) (Spec.CTR.counter_mode chacha20_ctx chacha20_cipher (Ghost.reveal log).k (Ghost.reveal log).n (UInt32.v ctr) (reveal_sbytes (as_seq h0 plain)));
  ()


#reset-options "--max_fuel 0 --z3rlimit 20"

val chacha20:
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length plain} ->
  key:uint8_p{length key = 32} ->
  nonce:uint8_p{length nonce = 12} ->
  ctr:U32.t{U32.v ctr + (length plain / 64) < pow2 32} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain /\ live h key /\ live h nonce))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h0 plain /\ live h0 key /\ live h0 nonce
      /\ modifies_1 output h0 h1
      /\ (let o = reveal_sbytes (as_seq h1 output) in
         let plain = reveal_sbytes (as_seq h0 plain) in
         let k = reveal_sbytes (as_seq h0 key) in
         let n = reveal_sbytes (as_seq h0 nonce) in
         let ctr = U32.v ctr in
         o == Spec.CTR.counter_mode chacha20_ctx chacha20_cipher k n ctr plain)))
let chacha20 output plain len k n ctr =
  (**) let hinit = ST.get() in
  push_frame();
  (**) let h0 = ST.get() in
  let st = alloc () in
  (**) let h1 = ST.get() in
  let l  = init st k n in
  (**) let h2 = ST.get() in
  (**) lemma_modifies_0_1' st h0 h1 h2;
  let l' = chacha20_counter_mode output plain len l st ctr in
  (**) let h3 = ST.get() in
  (**) lemma_modifies_0_2 output st h0 h2 h3;
  pop_frame();
  (**) let hfin = ST.get() in
  (**) modifies_popped_1 output hinit h0 h3 hfin
*)
