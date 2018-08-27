module Lib.Buffer.Lemmas

open FStar.HyperStack
open FStar.HyperStack.ST
open Lib.IntTypes

module Seq = Lib.Sequence
open Lib.Buffer

val live_sub_lemma: #a:Type0 -> #len:size_nat -> h:mem -> b:lbuffer a len -> start:size_t -> n:size_t{v start + v n <= len} -> Lemma
			 (requires (live h b))
			 (ensures (live h (gsub #a #len #(v n) b start n)))
			 [SMTPat (live h (gsub #a #len #(v n) b start n))]

val live_super_lemma: #a:Type0 -> #len:size_nat -> h:mem -> b:lbuffer a len -> start:size_t -> n:size_t{v start + v n <= len} -> Lemma
			 (requires (live h (gsub #a #len #(v n) b start n)))
			 (ensures (live h b))
			 [SMTPat (live h (gsub #a #len #(v n) b start n))]

val disjoint_self_lemma: #a:Type0 -> #len:size_nat -> b:lbuffer a len -> Lemma
			 (requires (True))
			 (ensures (~ (disjoint b b)))
			 [SMTPat (disjoint b b)]

val disjoint_sub_lemma1: #a1:Type0 -> #a2:Type0 -> #len1:size_nat -> #len2:size_nat -> b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> start1:size_t -> n1:size_t{v start1 + v n1 <= len1} -> Lemma
			 (requires (disjoint b1 b2))
			 (ensures (disjoint (gsub #a1 #len1 #(v n1) b1 start1 n1) b2 /\ disjoint b2 (gsub #a1 #len1 #(v n1) b1 start1 n1)))
			 [SMTPatOr[[SMTPat (disjoint (gsub #a1 #len1 #(v n1) b1 start1 n1) b2)];
				   [SMTPat (disjoint b2 (gsub #a1 #len1 #(v n1) b1 start1 n1))]]]

val disjoint_sub_lemma2: #a:Type0 -> #len:size_nat -> b:lbuffer a len -> start1:size_t -> n1:size_t{v start1 + v n1 <= len} -> start2:size_t -> n2:size_t{v start2 + v n2 <= len} -> Lemma
			 (requires (v start1 + v n1 <= v start2 \/ v start2 + v n2 <= v start1))
			 (ensures (disjoint (gsub #a #len #(v n1) b start1 n1) (gsub #a #len #(v n2) b start2 n2)))
			 [SMTPat (disjoint (gsub #a #len #(v n1) b start1 n1) (gsub #a #len #(v n2) b  start2 n2))]

val as_seq_sub_lemma: #a:Type0 -> #len:size_nat -> h:mem -> b:lbuffer a len -> start:size_t -> n:size_t{v start + v n <= len} -> Lemma
			 (requires (live h b))
			 (ensures (as_seq (gsub #a #len #(v n) b start n) h == Seq.sub #a #(len) (as_seq b h) (v start) (v n)))
			 [SMTPat (as_seq (gsub #a #len #(v n) b start n) h)]


val preserves_live_lemma: #a:Type0 -> #len:size_nat -> b:lbuffer a len -> h0:mem -> h1:mem -> Lemma
			 (requires (preserves_live h0 h1 /\ live h0 b))
			 (ensures  (live h1 b))
			 [SMTPat (preserves_live h0 h1);
			  SMTPat (live h0 b)]


val creates1_lemma:  #a1:Type0 -> #a2:Type0 -> #len1:size_nat -> #len2:size_nat -> b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> h0:mem -> h1:mem -> Lemma
			 (requires (live h0 b1 /\ creates1 b2 h0 h1))
			 (ensures  (live h1 b1 /\ disjoint b1 b2 /\ disjoint b2 b1))
			 [SMTPat (creates1 b2 h0 h1);
			  SMTPat (live h0 b1)]

(*
val creates1_preserves:  #a1:Type0 -> #len1:size_nat -> b:lbuffer a1 len1 -> h0:mem -> h1:mem -> h2:mem -> Lemma
			 (requires (preserves_live h0 h1 /\ creates1 b h1 h2))
			 (ensures  (creates1 b h0 h2))
			 [SMTPat (creates1 b h1 h2);
			  SMTPat (preserves_live h0 h1)]
val creates1_preserves':  #a1:Type0 -> #len1:size_nat -> b:lbuffer a1 len1 -> h0:mem -> h1:mem -> h2:mem -> Lemma
			 (requires (creates1 b h0 h1 /\ preserves_live h1 h2))
			 (ensures  (creates1 b h0 h2))
			 [SMTPat (creates1 b h0 h1);
			  SMTPat (preserves_live h1 h2)]
*)

let creates2 #a1 #a2 #len1 #len2 (b1:lbuffer a1 len1) (b2:lbuffer a2 len2) h0 h1 =
  creates1 #a1 #len1 b1 h0 h1 /\
  creates1 #a2 #len2 b2 h0 h1

let creates3 #a1 #a2 #a3  #len1 #len2  #len3 (b1:lbuffer a1 len1) (b2:lbuffer a2 len2) (b3:lbuffer a3 len3) h0 h1 =
  creates1 #a1 #len1 b1 h0 h1 /\
  creates1 #a2 #len2 b2 h0 h1 /\
  creates1 #a3 #len3 b3 h0 h1

val live_list_lemma1: #a:Type0 -> #len:size_nat -> b:lbuffer a len -> h:mem -> Lemma
			(requires (True))
			(ensures (live_list h [BufItem b] == live h b))
			[SMTPat (live_list h [BufItem b])]

val live_list_lemma2: #a1:Type0 -> #a2:Type0 -> #len1:size_nat -> #len2:size_nat -> b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> h:mem -> Lemma
			(requires (True))
			(ensures (live_list h [BufItem b1; BufItem b2] == (live h b1 /\ live h b2)))
			[SMTPat (live_list h [BufItem b1; BufItem b2])]

val live_list_lemma3: #a1:Type0 -> #a2:Type0 -> #a3:Type0 -> #len1:size_nat -> #len2:size_nat -> #len3:size_nat ->
			b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> b3:lbuffer a3 len3 -> h:mem -> Lemma
			(requires (True))
			(ensures (live_list h [BufItem b1; BufItem b2; BufItem b3] == (live h b1 /\ live h b2 /\ live h b3)))
			[SMTPat (live_list h [BufItem b1; BufItem b2; BufItem b3])]


val disjoint_list_lemma1: #a:Type0 -> #a1:Type0 -> #len:size_nat -> #len1:size_nat -> b0:lbuffer a len -> b:lbuffer a1 len1 -> Lemma
			(requires (True))
			(ensures (disjoint_list b0 [BufItem b] == (disjoint b0 b /\ disjoint b b0) ))
			[SMTPat (disjoint_list #a b0 [BufItem #a1 #len1 b])]

val disjoint_list_lemma2: #a0:Type0 -> #a1:Type0 -> #a2:Type0 -> #len0:size_nat -> #len1:size_nat -> #len2:size_nat -> b0:lbuffer a0 len0 -> b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 ->  Lemma
			(requires (True))
			(ensures (disjoint_list b0 [BufItem b1; BufItem b2] == (disjoint b0 b1 /\ disjoint b0 b2 /\ disjoint b1 b0 /\ disjoint b2 b0)))
			[SMTPat (disjoint_list b0 [BufItem b1; BufItem b2])]

val disjoint_list_lemma3: #a0:Type0 -> #a1:Type0 -> #a2:Type0 -> #a3:Type0 -> #len0:size_nat -> #len1:size_nat -> #len2:size_nat -> #len3:size_nat ->
			b0:lbuffer a0 len0 -> b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> b3:lbuffer a3 len3 -> Lemma
			(requires (True))
			(ensures (disjoint_list b0 [BufItem b1; BufItem b2; BufItem b3] == (disjoint b0 b1 /\ disjoint b0 b2 /\ disjoint b0 b3 /\ disjoint b1 b0 /\ disjoint b2 b0 /\ disjoint b3 b0)))
			[SMTPat (disjoint_list b0 [BufItem b1; BufItem b2; BufItem b3])]


val disjoint_lists_lemma_1_1: #a0:Type0 -> #a1:Type0 -> #len0:size_nat -> #len1:size_nat -> b0:lbuffer a0 len0 -> b1:lbuffer a1 len1 -> Lemma
			(requires (True))
			(ensures (disjoint_lists [BufItem b0] [BufItem b1] == (disjoint b0 b1 /\ disjoint b1 b0) ))
			[SMTPat (disjoint_lists [BufItem b0] [BufItem b1])]

val disjoint_lists_lemma_2_1: #a0:Type0 -> #a1:Type0 -> #a2:Type0 -> #len0:size_nat -> #len1:size_nat -> #len2:size_nat -> b0:lbuffer a0 len0 -> b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> Lemma
			(requires (True))
			(ensures (disjoint_lists [BufItem b0; BufItem b1] [BufItem b2] == (disjoint b0 b2 /\ disjoint b2 b0 /\ disjoint b1 b2 /\ disjoint b2 b1)))
			[SMTPat (disjoint_lists [BufItem b0; BufItem b1] [BufItem b2])]

val disjoint_lists_lemma_1_2: #a0:Type0 -> #a1:Type0 -> #a2:Type0 -> #len0:size_nat -> #len1:size_nat -> #len2:size_nat -> b0:lbuffer a0 len0 -> b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> Lemma
			(requires (True))
			(ensures (disjoint_lists [BufItem b0] [BufItem b1; BufItem b2] == (disjoint b0 b1 /\ disjoint b1 b0 /\ disjoint b0 b2 /\ disjoint b2 b0)))
			[SMTPat (disjoint_lists [BufItem b0] [BufItem b1; BufItem b2])]

val disjoint_lists_lemma_2_2: #a0:Type0 -> #a1:Type0 -> #a2:Type0 -> #a3:Type0 -> #len0:size_nat -> #len1:size_nat -> #len2:size_nat -> #len3:size_nat -> b0:lbuffer a0 len0 -> b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> b3:lbuffer a3 len3 -> Lemma
			(requires (True))
			(ensures (disjoint_lists [BufItem b0; BufItem b1] [BufItem b2; BufItem b3] == (disjoint b0 b2 /\ disjoint b2 b0 /\ disjoint b0 b3 /\ disjoint b3 b0 /\ disjoint b1 b2 /\ disjoint b2 b1 /\ disjoint b1 b3 /\ disjoint b3 b1)))
			[SMTPat (disjoint_lists [BufItem b0; BufItem b1] [BufItem b2; BufItem b3])]

val disjoint_lists_lemma_3_1: #a0:Type0 -> #a1:Type0 -> #a2:Type0 -> #a3:Type0 -> #len0:size_nat -> #len1:size_nat -> #len2:size_nat -> #len3:size_nat -> b0:lbuffer a0 len0 -> b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> b3:lbuffer a3 len3 -> Lemma
			(requires (True))
			(ensures (disjoint_lists [BufItem b0; BufItem b1; BufItem b2] [BufItem b3] == (disjoint b0 b3 /\ disjoint b3 b0 /\ disjoint b1 b3 /\ disjoint b3 b1 /\ disjoint b2 b3 /\ disjoint b3 b2) ))
			[SMTPat (disjoint_lists [BufItem b0; BufItem b1; BufItem b2] [BufItem b3])]

val disjoint_lists_lemma_1_3: #a0:Type0 -> #a1:Type0 -> #a2:Type0 -> #a3:Type0 -> #len0:size_nat -> #len1:size_nat -> #len2:size_nat -> #len3:size_nat -> b0:lbuffer a0 len0 -> b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> b3:lbuffer a3 len3 -> Lemma
			(requires (True))
			(ensures (disjoint_lists [BufItem b0] [BufItem b1; BufItem b2; BufItem b3] == (disjoint b0 b1 /\ disjoint b1 b0 /\ disjoint b0 b2 /\ disjoint b2 b0 /\ disjoint b0 b3 /\ disjoint b3 b0) ))
			[SMTPat (disjoint_lists [BufItem b0] [BufItem b1; BufItem b2; BufItem b3])]

val disjoint_lists_lemma_1_4: #a0:Type0 -> #a1:Type0 -> #a2:Type0 -> #a3:Type0 -> #a4:Type0 -> #len0:size_nat -> #len1:size_nat -> #len2:size_nat -> #len3:size_nat -> #len4:size_nat -> b0:lbuffer a0 len0 -> b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> b3:lbuffer a3 len3 -> b4:lbuffer a4 len4 -> Lemma
			(requires (True))
			(ensures (disjoint_lists [BufItem b0] [BufItem b1; BufItem b2; BufItem b3; BufItem b4] == (disjoint b0 b1 /\ disjoint b1 b0 /\ disjoint b0 b2 /\ disjoint b2 b0 /\ disjoint b0 b3 /\ disjoint b3 b0 /\ disjoint b0 b4 /\ disjoint b4 b0) ))
			[SMTPat (disjoint_lists [BufItem b0] [BufItem b1; BufItem b2; BufItem b3; BufItem b4])]

val disjoint_lists_lemma_4_1: #a0:Type0 -> #a1:Type0 -> #a2:Type0 -> #a3:Type0 -> #a4:Type0 -> #len0:size_nat -> #len1:size_nat -> #len2:size_nat -> #len3:size_nat -> #len4:size_nat -> b0:lbuffer a0 len0 -> b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> b3:lbuffer a3 len3 -> b4:lbuffer a4 len4 -> Lemma
			(requires (True))
			(ensures (disjoint_lists [BufItem b0; BufItem b1; BufItem b2; BufItem b3] [BufItem b4] == (disjoint b0 b4 /\ disjoint b4 b0 /\ disjoint b1 b4 /\ disjoint b4 b1 /\ disjoint b2 b4 /\ disjoint b4 b2 /\ disjoint b3 b4 /\ disjoint b4 b3) ))
			[SMTPat (disjoint_lists [BufItem b0; BufItem b1; BufItem b2; BufItem b3] [BufItem b4])]

val disjoint_lists_lemma_2_4: #a0:Type0 -> #a1:Type0 -> #a2:Type0 -> #a3:Type0 -> #a4:Type0 -> #a5:Type0 -> #len0:size_nat -> #len1:size_nat -> #len2:size_nat -> #len3:size_nat -> #len4:size_nat -> #len5:size_nat -> b0:lbuffer a0 len0 -> b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> b3:lbuffer a3 len3 -> b4:lbuffer a4 len4 -> b5:lbuffer a5 len5 -> Lemma
			(requires (True))
			(ensures (disjoint_lists [BufItem b0; BufItem b1] [BufItem b2; BufItem b3; BufItem b4; BufItem b5] == (disjoint b0 b2 /\ disjoint b2 b0 /\ disjoint b0 b3 /\ disjoint b3 b0 /\ disjoint b0 b4 /\ disjoint b4 b0 /\ disjoint b1 b2 /\ disjoint b2 b1 /\ disjoint b1 b3 /\ disjoint b3 b1 /\ disjoint b1 b4 /\ disjoint b4 b1) ))
			[SMTPat (disjoint_lists [BufItem b0; BufItem b1] [BufItem b2; BufItem b3; BufItem b4; BufItem b5])]


val disjoint_lists_lemma_4_2: #a0:Type0 -> #a1:Type0 -> #a2:Type0 -> #a3:Type0 -> #a4:Type0 -> #a5:Type0 -> #len0:size_nat -> #len1:size_nat -> #len2:size_nat -> #len3:size_nat -> #len4:size_nat -> #len5:size_nat -> b0:lbuffer a0 len0 -> b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> b3:lbuffer a3 len3 -> b4:lbuffer a4 len4 -> b5:lbuffer a5 len5 -> Lemma
			(requires (True))
			(ensures (disjoint_lists [BufItem b0; BufItem b1; BufItem b2; BufItem b3] [BufItem b4; BufItem b5] == (disjoint b0 b4 /\ disjoint b4 b0 /\ disjoint b1 b4 /\ disjoint b4 b1 /\ disjoint b2 b4 /\ disjoint b4 b2 /\ disjoint b3 b4 /\ disjoint b4 b3 /\ disjoint b0 b5 /\ disjoint b5 b0 /\ disjoint b1 b5 /\ disjoint b5 b1 /\ disjoint b2 b5 /\ disjoint b5 b2 /\ disjoint b3 b5 /\ disjoint b5 b3) ))
			[SMTPat (disjoint_lists [BufItem b0; BufItem b1; BufItem b2; BufItem b3] [BufItem b4; BufItem b5])]


val disjoints_lemma1: #a:Type0 -> #len:size_nat -> b:lbuffer a len -> Lemma
			(requires (True))
			(ensures (disjoints [BufItem b] == (disjoint b b)))
//			[SMTPat (disjoints [BufItem #a #len b])]

val disjoints_lemma2: #a0:Type0 -> #a1:Type0 -> #len0:size_nat -> #len1:size_nat -> b0:lbuffer a0 len0 -> b1:lbuffer a1 len1 -> Lemma
			(requires (True))
			(ensures (disjoints [BufItem b0; BufItem b1] == (disjoint b0 b1 /\ disjoint b1 b0) ))
//			[SMTPat (disjoints [BufItem b0; BufItem b1])]

val disjoints_lemma3: #a0:Type0 -> #a1:Type0 -> #a2:Type0 -> #len0:size_nat -> #len1:size_nat -> #len2:size_nat -> b0:lbuffer a0 len0 -> b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 ->  Lemma
			(requires (True))
			(ensures (disjoints [BufItem b0; BufItem b1; BufItem b2] == (disjoint b0 b1 /\ disjoint b1 b0 /\ disjoint b0 b2 /\ disjoint b2 b0 /\ disjoint b1 b2 /\ disjoint b2 b1)))
//			[SMTPat (disjoints [BufItem b0; BufItem b1; BufItem b2])]

val disjoints_lemma4: #a0:Type0 -> #a1:Type0 -> #a2:Type0 -> #a3:Type0 -> #len0:size_nat -> #len1:size_nat -> #len2:size_nat -> #len3:size_nat ->
			b0:lbuffer a0 len0 -> b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> b3:lbuffer a3 len3 -> Lemma
			(requires (True))
			(ensures (disjoints [BufItem b0; BufItem b1; BufItem b2; BufItem b3] == (
           disjoint b0 b1 /\ disjoint b1 b0 /\ disjoint b0 b2 /\ disjoint b2 b0 /\ disjoint b0 b3 /\ disjoint b3 b0 /\
           disjoint b1 b2 /\ disjoint b2 b1 /\ disjoint b1 b3 /\ disjoint b3 b1 /\
           disjoint b2 b3 /\ disjoint b3 b2)))
//			[SMTPat (disjoints [BufItem b0; BufItem b1; BufItem b2; BufItem b3])]

val modifies_modifies_1: #a:Type0 -> #len:size_nat -> b:lbuffer a len -> h0:mem -> h1:mem -> Lemma
			(requires (True))
			(ensures (modifies [BufItem b] h0 h1 == modifies1 b h0 h1))
			[SMTPat (modifies [BufItem b] h0 h1)]

val list_cons1_lemma: #a:Type0 -> x:a -> y:a -> Lemma
			 (requires True)
			 (ensures ([x;y] == x::[y]))
			 [SMTPat (x::[y])]
val list_cons2_lemma: #a:Type0 -> x:a -> y:a -> z:a -> Lemma
			 (requires True)
			 (ensures ([x;y;z] == x::[y;z]))
			 [SMTPat (x::[y;z])]

val modifies_modifies_2: #a1:Type0 -> #a2:Type0 -> #len1:size_nat -> #len2:size_nat ->
			b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> h0:mem -> h1:mem -> Lemma
			(requires (True))
			(ensures (modifies [BufItem b1; BufItem b2] h0 h1 == modifies2 b1 b2 h0 h1))
			[SMTPat (modifies [BufItem b1; BufItem b2] h0 h1)]

val modifies_modifies_3: #a1:Type0 -> #a2:Type0 -> #a3:Type0 -> #len1:size_nat -> #len2:size_nat -> #len3:size_nat ->
			b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> b3:lbuffer a3 len3 ->
			h0:mem -> h1:mem -> Lemma
			(requires True)
			(ensures (modifies [BufItem b1; BufItem b2; BufItem b3] h0 h1 == modifies3 b1 b2 b3 h0 h1))
			[SMTPat (modifies [BufItem b1; BufItem b2; BufItem b3] h0 h1)]

val preserves_live_refl: h0:mem -> Lemma
		         (requires (True))
			 (ensures (preserves_live h0 h0))
			 [SMTPat (preserves_live h0 h0)]

val preserves_live_trans: h0:mem -> h1:mem -> h2:mem -> Lemma
		         (requires (preserves_live h0 h1 /\ preserves_live h1 h2))
			 (ensures (preserves_live h0 h2))
			 [SMTPat (preserves_live h0 h1);
			  SMTPat (preserves_live h1 h2)]

val modifies_1_refl: #a:Type0 -> #len:size_nat -> b:lbuffer a len -> h0:mem -> Lemma
			 (requires (live h0 b))
			 (ensures (modifies1 b h0 h0))
			 [SMTPat (modifies1 b h0 h0)]

val modifies_1_modifies_2: #a1:Type0 -> #a2:Type0 -> #len1:size_nat -> #len2:size_nat -> b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> h0:mem -> h1:mem -> Lemma
			 (requires (live h0 b1 /\ live h0 b2 /\ modifies1 b1 h0 h1))
			 (ensures (modifies2 b1 b2 h0 h1 /\ modifies2 b2 b1 h0 h1))
			 [SMTPat (modifies1 b1 h0 h1);
			  SMTPat (live h0 b1);
			  SMTPat (live h0 b2)]


val modifies_2_modifies_3: #a1:Type0 -> #a2:Type0 -> #a3:Type0 -> #len1:size_nat -> #len2:size_nat -> #len3:size_nat ->
		           b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> b3:lbuffer a3 len3 -> h0:mem -> h1:mem -> Lemma
			 (requires (live h0 b1 /\ live h0 b2 /\ live h0 b3 /\ modifies2 b1 b2 h0 h1))
			 (ensures (modifies3 b1 b2 b3 h0 h1 /\ modifies3 b1 b3 b2 h0 h1 /\ modifies3 b2 b1 b3 h0 h1 /\
				   modifies3 b2 b3 b1 h0 h1 /\ modifies3 b3 b1 b2 h0 h1 /\ modifies3 b3 b2 b1 h0 h1))
			 [SMTPat (modifies2 b1 b2 h0 h1);
			  SMTPat (live h0 b1);
			  SMTPat (live h0 b2);
			  SMTPat (live h0 b3)]


val modifies_1_trans: #a:Type0 -> #len:size_nat -> b:lbuffer a len -> h0:mem -> h1:mem -> h2:mem -> Lemma
			 (requires (live h0 b /\ modifies1 b h0 h1 /\ modifies1 b h1 h2))
			 (ensures (modifies1 b h0 h2))
			 [SMTPat (modifies1 b h0 h1);
			  SMTPat (modifies1 b h1 h2);
			  SMTPat (live h0 b)]


val modifies_2_trans: #a1:Type0 -> #a2:Type0 -> #len1:size_nat -> #len2:size_nat -> b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> h0:mem -> h1:mem -> h2:mem -> Lemma
			 (requires (live h0 b1 /\ live h0 b2 /\ modifies2 b1 b2 h0 h1 /\ modifies2 b1 b2 h1 h2))
			 (ensures (modifies2 b1 b2 h0 h2))
			 [SMTPat (modifies2 b1 b2 h0 h1);
			  SMTPat (modifies2 b1 b2 h1 h2);
			  SMTPat (live h0 b1);
			  SMTPat (live h0 b2)]

val modifies_3_trans: #a1:Type0 -> #a2:Type0 -> #a3:Type0 -> #len1:size_nat -> #len2:size_nat -> #len3:size_nat ->
		           b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> b3:lbuffer a3 len3 -> h0:mem -> h1:mem -> h2:mem -> Lemma
			 (requires (live h0 b1 /\ live h0 b2 /\ live h0 b3 /\ modifies3 b1 b2 b3 h0 h1 /\ modifies3 b1 b2 b3 h1 h2))
			 (ensures (modifies3 b1 b2 b3 h0 h2))
			 [SMTPat (modifies3 b1 b2 b3 h0 h1);
			  SMTPat (modifies3 b1 b2 b3 h1 h2);
			  SMTPat (live h0 b1);
			  SMTPat (live h0 b2);
			  SMTPat (live h0 b3)]


val modifies1_lemma:  #a1:Type0 -> #a2:Type0 -> #len1:size_nat -> #len2:size_nat -> b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> h0:mem -> h1:mem -> Lemma
			 (requires (disjoint b1 b2 /\ live h0 b1 /\ modifies1 b2 h0 h1))
			 (ensures  (live h1 b1 /\ as_seq b1 h1 == as_seq b1 h0))
			 [SMTPat (disjoint b1 b2);
			  SMTPat (live h0 b1);
			  SMTPat (modifies1 b2 h0 h1)]


val modifies2_lemma:  #a1:Type0 -> #a2:Type0 -> #a3:Type0 -> #len1:size_nat -> #len2:size_nat -> #len3:size_nat -> b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> b3:lbuffer a3 len3 -> h0:mem -> h1:mem -> Lemma
			 (requires (disjoint b1 b2 /\ disjoint b1 b3 /\ live h0 b1 /\ modifies2 b2 b3 h0 h1))
			 (ensures  (live h1 b1 /\ as_seq b1 h1 == as_seq b1 h0))
			 [SMTPat (disjoint b1 b2);
			  SMTPat (disjoint b1 b3);
			  SMTPat (live h0 b1);
			  SMTPat (modifies2 b2 b3 h0 h1)]


val modifies3_lemma:  #a1:Type0 -> #a2:Type0 -> #a3:Type0 -> #a4:Type0-> #len1:size_nat -> #len2:size_nat -> #len3:size_nat -> #len4:size_nat ->
		      b1:lbuffer a1 len1 -> b2:lbuffer a2 len2 -> b3:lbuffer a3 len3 -> b4:lbuffer a4 len4 -> h0:mem -> h1:mem -> Lemma
			 (requires (disjoint b1 b2 /\ disjoint b1 b3 /\ disjoint b1 b4 /\ live h0 b1 /\ modifies3 b2 b3 b4 h0 h1))
			 (ensures  (live h1 b1 /\ as_seq b1 h1 == as_seq b1 h0))
			 [SMTPat (disjoint b1 b2);
			  SMTPat (disjoint b1 b3);
			  SMTPat (disjoint b1 b4);
			  SMTPat (live h0 b1);
			  SMTPat (modifies3 b2 b3 b4 h0 h1)]


val modifies_sub_lemma: #a:Type0 -> #len:size_nat -> b:lbuffer a len -> start:size_t -> n:size_t{v start+v n <= len} -> h0:mem -> h1:mem -> Lemma
			 (requires (live h0 b /\ modifies1 (gsub #a #len #(v n) b start n) h0 h1))
			 (ensures  (modifies1 b h0 h1 /\ as_seq b h1 == Seq.update_sub #a #(len) (as_seq b h0) (v start) (v n) (Seq.sub #a  #(len) (as_seq b h1) (v start) (v n))))
			 [SMTPat (live h0 b);
			  SMTPat (modifies1 (gsub #a #len #(v n) b start n) h0 h1)]
