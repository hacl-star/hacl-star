module Hacl.Impl.Chacha20

open FStar.HyperStack
open FStar.HyperStack.ST
open Lib.IntTypes

open Lib.Buffer
open Lib.ByteBuffer
open Lib.Buffer.Lemmas
open Spec.Chacha20

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module Spec = Spec.Chacha20

(* Definition of the state *)
type state = lbuffer uint32 16
type idx = n:size_t{v n < 16}
unfold let blocksize:size_t = size 64

noextract unfold let v = size_v

noextract unfold let index (x:size_nat) = size x

noextract unfold 
let as_state (st:state) (h:mem) : GTot Spec.state =
  LSeq.to_lseq #uint32 (as_seq st h)
  
[@ "substitute"]
private
val line: st:state -> a:idx -> b:idx -> d:idx -> s:rotval U32 ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st h0 h1 /\
			   as_state st h1 == Spec.line (v a) (v b) (v d) s (as_state st h0)))
[@ "substitute"]
let line st a b d s =
  let sa = st.(a) in let sb = st.(b) in
  st.(a) <- add_mod #U32 sa sb;
  let sd = st.(d) in let sa = st.(a) in
  let sda = sd ^. sa in
  st.(d) <- sda <<<. s


[@ "c_inline"]
private
val quarter_round: st:state -> a:idx -> b:idx -> c:idx -> d:idx ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st h0 h1 /\
			  as_state st h1 == Spec.quarter_round (v a) (v b) (v c) (v d) (as_state  st h0 )))

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
	     as_state st h1 == Spec.column_round (as_state st h0)))
[@ "substitute"]
let column_round st =
  quarter_round st (index 0) (index 4) (index 8)  (index 12);
  quarter_round st (index 1) (index 5) (index 9)  (index 13);
  quarter_round st (index 2) (index 6) (index 10) (index 14);
  quarter_round st (index 3) (index 7) (index 11) (index 15)

[@ "substitute"]
private
val diagonal_round: st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st h0 h1 /\
       as_state st h1 == Spec.diagonal_round (as_state st h0)))
[@ "substitute"]
let diagonal_round st =
  quarter_round st (index 0) (index 5) (index 10) (index 15);
  quarter_round st (index 1) (index 6) (index 11) (index 12);
  quarter_round st (index 2) (index 7) (index 8)  (index 13);
  quarter_round st (index 3) (index 4) (index 9)  (index 14)


[@ "c_inline"]
private
val double_round: st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st h0 h1 /\
		 as_state st h1 == Spec.double_round (as_state st h0)))
[@ "c_inline"]
let double_round st =
  column_round st;
  diagonal_round st


[@ "c_inline"]
private
val rounds: st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st h0 h1 /\
		 as_state st h1 == Spec.rounds (as_state st h0)))
[@ "c_inline"]
let rounds st =
  iter #uint32 #16 #(size 16) (size 10) Spec.double_round double_round st

[@ "c_inline"]
private
val chacha20_core:
  k:state ->
  st:state ->
  Stack unit
    (requires (fun h -> live h k /\ live h st /\ disjoint st k))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 k h0 h1 /\
		as_state k h1 == Spec.chacha20_core (as_state st h0)))
#reset-options "--z3rlimit 50"
[@ "c_inline"]
let chacha20_core k st =
  copy #_ k (size 16) st;
  rounds k;
  map2 (size 16) (add_mod #U32) k st;
  ()

[@ "c_inline"]
private
val setup:
  st:state ->
  k:lbuffer uint8 32 ->
  n:lbuffer uint8 12 ->
  Stack unit
    (requires (fun h -> live h st /\ live h k /\ live h n
                    /\ disjoint k st /\ disjoint n st))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st h0 h1
                       /\ as_state st h1 ==
			 Spec.setup (as_lseq k h0) (as_lseq n h0) (as_lseq st h0)))

#reset-options "--z3rlimit 50 --max_fuel 0"
[@ "c_inline"]
let setup st k n =
  st.(index 0) <- u32 Spec.c0;
  st.(index 1) <- u32 Spec.c1;
  st.(index 2) <- u32 Spec.c2;
  st.(index 3) <- u32 Spec.c3;
  let st_k = sub st (index 4) (index 8) in
  uints_from_bytes_le #U32 #8 st_k (size 8) k;
  let st_n = sub st (index 13) (index 3) in
  uints_from_bytes_le #U32 #3 st_n (size 3) n

[@ "c_inline"]
val chacha20_init:
  k:lbuffer uint8 32 ->
  n:lbuffer uint8 12 ->
  StackInline state
    (requires (fun h -> live h k /\ live h n))
    (ensures (fun h0 st h1 -> preserves_live h0 h1 /\ creates1 st h0 h1
                       /\ as_lseq st h1 ==
			 Spec.chacha20_init (as_lseq k h0) (as_lseq n h0)))

[@ "c_inline"]
let chacha20_init k n =
  let st : state = create #uint32 #16 (size 16) (u32 0) in
  setup st k n;
  st


[@ "c_inline"]
val chacha20_set_counter: st:state -> c:size_t -> Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st h0 h1
                       /\ as_lseq st h1 ==
			 Spec.chacha20_set_counter (as_lseq st h0) (size_v c)))

[@ "c_inline"]
let chacha20_set_counter st c =
  st.(size 12) <- size_to_uint32 c

[@ "c_inline"]
val chacha20_key_block: b:lbuffer uint8 64 -> st:state -> Stack unit
    (requires (fun h -> live h st /\ live h b /\ disjoint st b))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 b h0 h1
                       /\ as_lseq b h1 ==
			 Spec.chacha20_key_block (as_lseq st h0)))
[@ "c_inline"]
let chacha20_key_block b st =
  let h0 = ST.get() in
  alloc #h0 (size 16) (u32 0) b
  (fun h ->
     let st0 = as_lseq st h in
     (fun _ bseq -> bseq == Spec.chacha20_key_block st0))
  (fun st' -> chacha20_core st' st;
	   uints_to_bytes_le #U32 b (size 16) st')

[@ "c_inline"]
val chacha20_key_block0: b:lbuffer uint8 64 ->
  k:lbuffer uint8 32 ->
  n:lbuffer uint8 12 -> Stack unit
    (requires (fun h -> live h k /\ live h n /\ live h b /\ disjoint b k /\ disjoint b n))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 b h0 h1
                       /\ as_lseq b h1 ==
			 Spec.chacha20_key_block0 (as_lseq k h0) (as_lseq n h0)))
[@ "c_inline"]
let chacha20_key_block0 b k n =
  let h0 = ST.get() in
  alloc #h0 (size 16) (u32 0) b
  (fun h ->
    let key = as_lseq k h in
    let nonce = as_lseq n h in
    (fun _ bfin -> bfin == Spec.chacha20_key_block0 key nonce))
  (fun st -> setup st k n;
	  chacha20_key_block b st)


[@ "c_inline"]
val chacha20_encrypt_block:
  st0:state ->
  ctr0:size_t ->
  incr:size_t{size_v ctr0 + size_v incr <= max_size_t} ->
  block: lbuffer uint8 64 ->
  Stack unit
    (requires (fun h -> live h block /\
		     live h st0 /\
		     disjoint block st0 /\
		     disjoint st0 block ))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\
		           modifies1 block h0 h1 /\
			   as_lseq block h1 ==
			   Spec.chacha20_encrypt_block
			   (as_lseq st0 h0)
			   (size_v ctr0)
			   (size_v incr)
			   (as_lseq block h0)))

let chacha20_encrypt_block st0 ctr0 incr block =
  let h0 = ST.get () in
  alloc #h0 (size 16) (u32 0) block
  (fun h ->
    let st_init = as_lseq st0 h in
    let block_init = as_lseq block h in
    (fun _ block_fin ->
      block_fin ==
      Spec.chacha20_encrypt_block st_init (size_v ctr0) (size_v incr) block_init))
  (fun st -> copy st (size 16) st0;
	  chacha20_set_counter st (ctr0 +. incr);
	  let h1 = ST.get() in
	  alloc #h1 (size 64) (u8 0) block
	    (fun h ->
	       let st_init = as_lseq st h in
	       let block_init = as_lseq block h in
	       (fun _ block_fin ->
		 let kb_v = Spec.chacha20_key_block st_init in
		 block_fin == LSeq.map2 (^.) block_init kb_v))
	    (fun kb -> chacha20_key_block kb st;
		    map2 (size 64) (^.) block kb))

[@ "c_inline"]
val chacha20_encrypt_last:
  st0:state ->
  ctr0:size_t ->
  incr:size_t{size_v ctr0 + size_v incr <= max_size_t} ->
  len:size_t{size_v len < blocklen} ->
  block: lbuffer uint8 (size_v len) ->
  Stack unit
    (requires (fun h -> live h block /\
		     live h st0 /\
		     disjoint block st0 /\
		     disjoint st0 block ))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\
		           modifies1 block h0 h1 /\
			   as_lseq block h1 ==
			   Spec.chacha20_encrypt_last
			   (as_lseq st0 h0)
			   (size_v ctr0)
			   (size_v incr)
			   (size_v len)
			   (as_lseq block h0)))

let chacha20_encrypt_last st0 ctr0 incr len block =
  let h0 = ST.get () in
  alloc #h0 (size 64) (u8 0) block
  (fun h ->
    let st_init = as_lseq st0 h in
    let block_init = as_lseq block h in
    (fun _ block_fin ->
      block_fin ==
      Spec.chacha20_encrypt_last st_init (size_v ctr0) (size_v incr) (size_v len) block_init))
    (fun bl -> copy (sub bl (size 0) len) len block;
	    chacha20_encrypt_block st0 ctr0 incr bl;
	    copy block len (sub bl (size 0) len))


[@ "c_inline"]
val chacha20_encrypt_bytes:
  clen:size_t ->
  cipher:lbuffer uint8 (size_v clen) ->
  plain:lbuffer uint8 (size_v clen) ->
  key:lbuffer uint8 32 ->
  nonce:lbuffer uint8 12 ->
  ctr:size_t{size_v ctr + size_v clen <= max_size_t} ->
  Stack unit
    (requires (fun h -> live h cipher /\
		     live h plain /\
		     live h key /\
		     live h nonce /\
		     disjoint cipher plain /\ disjoint plain cipher /\
		     disjoint cipher key /\ disjoint key cipher /\
		     disjoint cipher nonce /\ disjoint nonce cipher /\
		     size_v ctr + (size_v clen / blocklen) <= max_size_t))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\
		           modifies1 cipher h0 h1))

let chacha20_encrypt_bytes clen cipher plain key nonce ctr =
  let h0 = ST.get() in
  alloc #h0 (size 16) (u32 0) cipher
  (fun h ->
     let key0 = as_lseq key h in
     let nonce0 = as_lseq nonce h in
     let plain0 = as_lseq plain h in
     (fun _ cipher_final ->
       cipher_final ==
       Spec.chacha20_encrypt_bytes key0 nonce0 (size_v ctr) (size_v clen) plain0))
  (fun st -> copy cipher clen plain;
          setup st key nonce;
	  let nblocks = clen /. blocksize in
	  let rem = clen %. blocksize in
	  let cipher0 = sub cipher (size 0) (nblocks *. blocksize) in
	  let cipher1 = sub cipher (nblocks *. blocksize) rem in
	  let h0 = ST.get() in
	  map_blocks #h0 #_ #blocklen #(size_v clen / blocklen) blocksize nblocks cipher0
	    (fun h ->
    	       let st0 = as_lseq st h in
	       Spec.chacha20_encrypt_block st0 (size_v ctr))
	    (fun i ->
	       let bufi = sub cipher0 (i *. blocksize) blocksize in
	       chacha20_encrypt_block st ctr i bufi);
	  chacha20_encrypt_last st ctr nblocks rem cipher1
	  )



(*

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


[@ "c_inline"]
val init:
  st:state ->
  k:lbuffer uint8 32 ->
  n:lbuffer uint8 12 ->
  Stack unit
    (requires (fun h -> live h k /\ live h n /\ live h st /\ disjoint k st /\ disjoint n st))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st h0 h1))
[@ "c_inline"]
let init st k n =
  setup st k n 0

#reset-options " --max_fuel 0 --z3rlimit 400"

val update_last:
  len:size_t{0 < len /\ len < 64} ->
  output:lbuffer uint8 len ->
  plain:lbuffer uint8 len ->
  st:state ->
  ctr:size_t{ctr + (len / 64) <= max_size_t} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain /\ disjoint output plain /\ disjoint st output /\ disjoint st plain)) //invariant log h st))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies2 output st h0 h1))
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

(*
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
  len:size_t ->
  output:lbuffer uint8 len ->
  plain:lbuffer uint8 len ->
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
let chacha20_counter_mode_blocks output plain len log st ctr =
  let h0 = ST.get() in
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
  
  



