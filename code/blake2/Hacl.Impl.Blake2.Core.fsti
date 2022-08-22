module Hacl.Impl.Blake2.Core
module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.IntVector

module Spec = Spec.Blake2

#set-options "--max_fuel 0 --max_ifuel 1"

type m_spec =
  | M32
  | M128
  | M256

noextract inline_for_extraction
type word_t (a:Spec.alg) = Spec.word_t a

noextract inline_for_extraction
let element_t (a:Spec.alg) (m:m_spec) =
  match a,m with
  | Spec.Blake2S,M128 -> (vec_t U32 4)
  | Spec.Blake2S,M256 -> (vec_t U32 4)
  | Spec.Blake2B,M256 -> (vec_t U64 4)
  | _ -> (word_t a)

noextract inline_for_extraction
val zero_element: a:Spec.alg -> m:m_spec -> element_t a m

noextract inline_for_extraction
let row_len (a:Spec.alg) (m:m_spec) : size_t =
  match a,m with
  | Spec.Blake2S,M128 -> 1ul
  | Spec.Blake2S,M256 -> 1ul
  | Spec.Blake2B,M256 -> 1ul
  | _ -> 4ul

noextract inline_for_extraction
unfold let row_p (a:Spec.alg) (m:m_spec) =
  lbuffer (element_t a m) (row_len a m)

noextract inline_for_extraction
val row_v: #a:Spec.alg -> #m:m_spec -> h:mem -> row_p a m -> GTot (Spec.row a)

noextract
val row_v_lemma: #a:Spec.alg -> #m:m_spec -> h0:mem -> h1:mem -> r1:row_p a m -> r2:row_p a m ->
  Lemma (ensures (as_seq h0 r1 == as_seq h1 r2 ==>
		  row_v h0 r1 == row_v h1 r2))
	[SMTPat (row_v h0 r1); SMTPat (row_v h1 r2)]

noextract inline_for_extraction
unfold let state_p (a:Spec.alg) (m:m_spec) =
  lbuffer (element_t a m) (4ul *. row_len a m)

noextract inline_for_extraction
unfold let index_t = n:size_t{v n < 4}

noextract inline_for_extraction
let g_rowi (#a:Spec.alg) (#m:m_spec) (st:state_p a m)  (idx:index_t) : GTot (row_p a m) =
  gsub st (idx *. row_len a m) (row_len a m)

val g_rowi_disjoint: #a:Spec.alg -> #m:m_spec -> st:state_p a m -> idx1:index_t -> idx2:index_t ->
  Lemma (ensures (v idx1 <> v idx2 ==> disjoint (g_rowi st idx1) (g_rowi st idx2)))
	[SMTPat (disjoint (g_rowi st idx1) (g_rowi st idx2))]

val g_rowi_unchanged: #a:Spec.alg -> #m:m_spec -> h0:mem -> h1:mem -> st:state_p a m -> i:index_t ->
  Lemma (requires (as_seq h0 st == as_seq h1 st))
	(ensures (as_seq h0 (g_rowi st i) == as_seq h1 (g_rowi st i)))
	[SMTPat (as_seq h0 (g_rowi st i)); SMTPat (as_seq h1 (g_rowi st i))]

val g_rowi_disjoint_other:  #a:Spec.alg -> #m:m_spec -> #b:Type -> st:state_p a m -> i:index_t -> x:buffer b ->
  Lemma(requires (disjoint st x))
       (ensures (disjoint (g_rowi st i) x))
       [SMTPat (disjoint (g_rowi st i) x)]

inline_for_extraction noextract
val state_v: #a:Spec.alg -> #m:m_spec -> mem -> state_p a m -> GTot (Spec.state a)

noextract
val state_v_eq_lemma: #a:Spec.alg -> #m:m_spec -> h0:mem -> h1:mem -> st1:state_p a m -> st2:state_p a m ->
  Lemma (requires (as_seq h0 st1 == as_seq h1 st2))
	(ensures (state_v h0 st1 == state_v h1 st2))
	[SMTPat (state_v #a #m h0 st1); SMTPat (state_v #a #m h1 st2)]

noextract
val state_v_rowi_lemma: #a:Spec.alg -> #m:m_spec -> h:mem -> st:state_p a m -> i:index_t ->
  Lemma (requires (live h st))
	(ensures (Lib.Sequence.((state_v h st).[v i] == row_v h (g_rowi st i))))
	[SMTPat (row_v h (g_rowi st i))]

noextract
val state_v_live_rowi_lemma: #a:Spec.alg -> #m:m_spec -> h:mem -> st:state_p a m -> i:index_t ->
  Lemma (requires (live h st))
	(ensures (live h (g_rowi st i)))
	[SMTPat (live h (g_rowi st i))]

noextract
val modifies_one_row: a:Spec.alg -> m:m_spec -> h0:mem -> h1:mem -> st:state_p a m -> i:index_t -> j:index_t ->
  Lemma (requires (live h0 st /\ modifies (loc (g_rowi st i)) h0 h1 /\ v i <> v j))
	(ensures (row_v h1 (g_rowi st j) == row_v h0 (g_rowi st j)))
	[SMTPat (modifies (loc (g_rowi st i)) h0 h1); SMTPat (row_v h1 (g_rowi st j))]

noextract
val modifies_row_state: a:Spec.alg -> m:m_spec -> h0:mem -> h1:mem -> st:state_p a m -> i:index_t ->
  Lemma (requires (live h0 st /\ modifies (loc (g_rowi st i)) h0 h1))
	(ensures (modifies (loc st) h0 h1 /\
		  state_v h1 st == Lib.Sequence.((state_v h0 st).[v i] <- row_v h1 (g_rowi st i))))
	[SMTPat (modifies (loc (g_rowi #a #m st i)) h0 h1)]


noextract inline_for_extraction
val rowi: #a:Spec.alg -> #m:m_spec -> st:state_p a m -> idx:index_t ->
	  Stack (row_p a m)
	  (requires (fun h -> live h st))
	  (ensures (fun h0 r h1 -> h0 == h1 /\ live h1 r /\ r == g_rowi st idx))

noextract inline_for_extraction
val xor_row: #a:Spec.alg -> #m:m_spec -> r1:row_p a m -> r2:row_p a m ->
	  Stack unit
	  (requires (fun h -> live h r1 /\ live h r2 /\ disjoint r1 r2))
	  (ensures (fun h0 _ h1 -> modifies (loc r1) h0 h1 /\
				row_v h1 r1 == Spec.( row_v h0 r1 ^| row_v h0 r2 )))
noextract inline_for_extraction
val add_row: #a:Spec.alg -> #m:m_spec -> r1:row_p a m -> r2:row_p a m ->
	  Stack unit
	  (requires (fun h -> live h r1 /\ live h r2 /\ disjoint r1 r2))
	  (ensures (fun h0 _ h1 -> modifies (loc r1) h0 h1 /\
				row_v h1 r1 == Spec.( row_v h0 r1 +| row_v h0 r2 )))
noextract inline_for_extraction
val ror_row: #a:Spec.alg -> #m:m_spec -> r1:row_p a m -> r2:rotval (Spec.wt a) ->
	  Stack unit
	  (requires (fun h -> live h r1))
	  (ensures (fun h0 _ h1 -> modifies (loc r1) h0 h1 /\
				row_v h1 r1 == Spec.( row_v h0 r1 >>>| r2 )))
noextract inline_for_extraction
val permr_row: #a:Spec.alg -> #m:m_spec -> r1:row_p a m -> n:index_t ->
	  Stack unit
	  (requires (fun h -> live h r1))
	  (ensures (fun h0 _ h1 -> modifies (loc r1) h0 h1 /\
				row_v h1 r1 == Spec.( rotr (row_v h0 r1) (v n) )))

val create4_lemma: #a:Type -> x0:a -> x1:a -> x2:a -> x3:a ->
  Lemma (ensures (
    let l = [ x0; x1; x2; x3 ] in
    assert_norm (List.Tot.length l = 4);
    Lib.Sequence.createL l == Lib.Sequence.create4 x0 x1 x2 x3))
	[SMTPat (Lib.Sequence.createL [x0;x1;x2;x3])]

noextract inline_for_extraction
val alloc_row: a:Spec.alg -> m:m_spec ->
	  StackInline (row_p a m)
	  (requires (fun h -> True))
	  (ensures (fun h0 r h1 -> stack_allocated r h0 h1 (Lib.Sequence.create (v (row_len a m)) (zero_element a m)) /\
				live h1 r /\
				row_v h1 r == Spec.zero_row a))

noextract inline_for_extraction
val create_row: #a:Spec.alg -> #m:m_spec -> r1:row_p a m -> w0:word_t a -> w1:word_t a -> w2:word_t a -> w3:word_t a ->
	  Stack unit
	  (requires (fun h -> live h r1))
	  (ensures (fun h0 _ h1 -> modifies (loc r1) h0 h1 /\
				row_v h1 r1 == Spec.( create_row w0 w1 w2 w3 )))
noextract inline_for_extraction
val load_row: #a:Spec.alg -> #m:m_spec -> r1:row_p a m -> ws:lbuffer (word_t a) 4ul ->
	  Stack unit
	  (requires (fun h -> live h r1 /\ live h ws /\ disjoint r1 ws))
	  (ensures (fun h0 _ h1 -> modifies (loc r1) h0 h1 /\
				row_v h1 r1 == Spec.( load_row (as_seq h0 ws))))


noextract inline_for_extraction
let size_row al = 4ul *. size (Spec.size_word al)

noextract inline_for_extraction
val store_row: #a:Spec.alg -> #m:m_spec -> b:lbuffer uint8 (size_row a) -> r:row_p a m ->
	  Stack unit
	  (requires (fun h -> live h r /\ live h b /\ disjoint r b))
	  (ensures (fun h0 _ h1 -> modifies (loc b) h0 h1 /\
			        as_seq h1 b == Lib.ByteSequence.uints_to_bytes_le (row_v h0 r)))

noextract inline_for_extraction
val store_row32: #a:Spec.alg -> #m:m_spec -> b:lbuffer (word_t a) 4ul -> r:row_p a m ->
	  Stack unit
	  (requires (fun h -> live h r /\ live h b /\ disjoint r b))
	  (ensures (fun h0 _ h1 -> modifies (loc b) h0 h1 /\
			        Spec.( load_row (as_seq h1 b)) == row_v h0 r))

noextract inline_for_extraction
let size_block (a:Spec.alg) : x:size_t{v x = 16 * Spec.size_word a} =
  Spec.alg_inversion_lemma a;
  match a with
  | Spec.Blake2.Blake2S -> 64ul
  | Spec.Blake2.Blake2B -> 128ul

noextract inline_for_extraction
type block_p (a:Spec.alg) = lbuffer uint8 (size_block a)

noextract inline_for_extraction
type block_w (a:Spec.alg) = lbuffer (word_t a) 16ul

noextract inline_for_extraction
val gather_row: #a:Spec.alg -> #ms:m_spec -> r:row_p a ms -> m:block_w a ->
          i0: Spec.sigma_elt_t -> i1:Spec.sigma_elt_t -> i2:Spec.sigma_elt_t -> i3:Spec.sigma_elt_t
	  -> Stack unit
	  (requires (fun h -> live h r /\ live h m /\ disjoint r m))
	  (ensures (fun h0 _ h1 -> modifies (loc r) h0 h1 /\
				row_v h1 r == Spec.(gather_row (as_seq h0 m) i0 i1 i2 i3)))

noextract inline_for_extraction
val alloc_state: a:Spec.alg -> m:m_spec ->
	  StackInline (state_p a m)
	  (requires (fun h -> True))
	  (ensures (fun h0 r h1 -> stack_allocated r h0 h1 (Lib.Sequence.create (4 * v (row_len a m)) (zero_element a m)) /\
				live h1 r))



noextract inline_for_extraction
val copy_state: #a:Spec.alg -> #m:m_spec -> st2:state_p a m -> st1:state_p a m ->
	  Stack unit
	  (requires (fun h0 -> live h0 st1 /\ live h0 st2 /\ disjoint st1 st2))
	  (ensures (fun h0 r h1 -> modifies (loc st2) h0 h1 /\
			        state_v h1 st2 == state_v h0 st1))

noextract inline_for_extraction
let load_state_st (a: Spec.alg) (m: m_spec) =
  st:state_p a m -> st32:state_p a M32 ->
	  Stack unit
	  (requires (fun h -> live h st /\ live h st32 /\ disjoint st st32))
	  (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1 /\
				state_v h1 st == state_v h0 st32))

noextract inline_for_extraction
val load_state_from_state32: #a:Spec.alg -> #m:m_spec -> load_state_st a m

noextract inline_for_extraction
let store_state_st (a: Spec.alg) (m: m_spec) =
  st32:state_p a M32 -> st:state_p a m ->
	  Stack unit
	  (requires (fun h -> live h st /\ live h st32 /\ disjoint st st32))
	  (ensures (fun h0 _ h1 -> modifies (loc st32) h0 h1 /\
				state_v h1 st32 == state_v h0 st))

noextract inline_for_extraction
val store_state_to_state32: #a:Spec.alg -> #m:m_spec -> store_state_st a m
