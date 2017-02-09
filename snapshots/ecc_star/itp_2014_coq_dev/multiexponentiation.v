(* -------------------------------------------------------------------- *)
Require Import ssreflect ssrnat ssrbool eqtype div ssrint ssrnum.
Require Import fintype ssralg ssrfun choice seq bigop matrix ec intdiv.

Import GRing.Theory.

Open Local Scope ring_scope.

Section Multiexponentiation.

Fixpoint nat_to_bin_aux (n a : nat) : seq bool :=
  match a with
    |0 => [::]
    |a.+1 => 
      match n with 
        |0 => [::]
        |_.+1 => (odd n) :: (nat_to_bin_aux n./2 a)
      end   
  end.

Definition nat_to_bin (n : nat) := nat_to_bin_aux n n.

(*lsb ... msb*)

Lemma nat_to_bin0 : nat_to_bin 0 = [::].
Proof. by []. Qed.

Lemma nat_to_bin1 : nat_to_bin 1 = [:: true].
Proof. by []. Qed.

Lemma nat_to_bin_eq_nil n : (nat_to_bin n == [::]) = (n == 0%N).
Proof.
apply/eqP/eqP => h.
+ by case: n h.
+ by rewrite h.
Qed.

Lemma nat_to_bin_simpl n a :
nat_to_bin_aux n.+1 a.+1 = (odd n.+1) :: (nat_to_bin_aux (n.+1)./2 a).
Proof. by []. Qed.

Lemma general_ind :
forall (P : nat -> Prop),
(forall n, (forall p : nat , (p < n)%N -> P p) -> P n) ->
forall n, P n.
Proof.
    move=> P ind n; move: {-2}n (leqnn n); elim: n => [|n IHn] p.
      by rewrite leqn0=> /eqP->; apply: ind.
    move=> lt_p_Sn; apply: ind=> k lt_k_p; apply: IHn.
    by rewrite -ltnS; rewrite (leq_trans lt_k_p).
  Qed.

Lemma nat_to_bin_aux_G (n m : nat) :
(n <= m)%N -> nat_to_bin_aux n m = nat_to_bin_aux n n. 
Proof.
elim/general_ind : n m.
case.
* by move=> IH m nGETm /= ;  case : m nGETm.
* move => n IH m nLTm ; case : m nLTm IH.
 + by rewrite ltn0.
 + move=> m nLTm IH; rewrite !nat_to_bin_simpl.
* have h1 : nat_to_bin_aux (n.+1)./2 m = nat_to_bin_aux (n.+1)./2 (n.+1)./2.
  apply: IH.
+ rewrite -divn2 ; apply: ltn_Pdiv => //.
+ case : m nLTm.
  * rewrite ltnS leqn0; move/eqP => nEQ0; by rewrite nEQ0 /=.
  * move=> m; rewrite ltnS; move=> nLTm; rewrite -divn2.
    have hn : (n.+1 %/ 2 <= n)%N.
    rewrite -ltnS;  by apply: ltn_Pdiv.
    apply: (leq_trans hn nLTm).
* have h2 : nat_to_bin_aux (n.+1)./2 n = nat_to_bin_aux (n.+1)./2 (n.+1)./2.
  apply: IH.
+ rewrite -divn2; apply: ltn_Pdiv => //.
+ rewrite -ltnS -divn2; apply: ltn_Pdiv => //.
by rewrite h1 h2.
Qed.

Lemma nat_to_bin_S :
forall (x : bool) (m : nat), m != 0%N ->
nat_to_bin (x + 2 * m)%N = x :: (nat_to_bin m).
Proof.
move=> x m mN0.
case : x.
* rewrite addnC addn1 /nat_to_bin /=.
  rewrite {2}mul2n uphalf_double -dvdn2 dvdn_mulr; last by rewrite dvdnn.
  have h : nat_to_bin_aux m (2 * m) = nat_to_bin_aux m m. 
  + apply: nat_to_bin_aux_G; by apply: leq_pmull.
  by rewrite h.
* rewrite add0n /nat_to_bin /=.
  have h : exists n, m = n.+1.
  + move: mN0; case:m => // x hx; exists x => //.
  move:h => [x mSx]; rewrite mSx.
  have h : (2 * x.+1)%N = ((2 * x).+1).+1.
  + by rewrite -[x.+1]addn1 mulnDr muln1 mul2n addn2.
  rewrite h nat_to_bin_simpl.
  have hodd : (odd (2 * x).+2) = false.
  + apply: negbTE; rewrite -h -dvdn2 dvdn_mulr // dvdnn.
  rewrite hodd -h -divn2 mulKn //.
  have H : nat_to_bin_aux x.+1 (2 * x).+1 = nat_to_bin_aux x.+1 x.+1. 
  + apply: nat_to_bin_aux_G; rewrite ltnS; by apply: leq_pmull.
  by rewrite H.
Qed.

Fixpoint bin_to_nat (l : seq bool) : nat :=
  match l with 
    |[::] => 0%N
    |x :: xs => (x + 2 * (bin_to_nat xs))%N 
  end.

Definition epurate (b : bool):=
  match b with
    |true => [:: true]
    |false => [::]
  end.

Fixpoint norm_bin1 (u : seq bool) :=
  match u with
    |[::] => [::]
    |x :: xs =>
      let v := norm_bin1 xs in 
        match v with 
          |[::] => epurate x
          |y :: ys => x :: v
        end
  end.

Fixpoint norm_bin_rev (v : seq bool) : seq bool :=
  match v with 
    |[::] => [::]
    |x :: xs => 
      if (x == true) then v
        else norm_bin_rev xs
  end.

(* norm_bin2 was an alternative but not used *)
Definition norm_bin2 (u : seq bool) :=
  rev (norm_bin_rev (rev u)).

Lemma norm_bin2_true : norm_bin2 [:: true] = [:: true].
Proof. by []. Qed.

Lemma norm_bin2_false : norm_bin2 [:: false] = [::].
Proof. by []. Qed.

Lemma norm_bin2_nil : norm_bin2 [::] = [::].
Proof. by []. Qed.

Lemma norm_bin1_true : norm_bin1 [:: true] = [:: true].
Proof. by []. Qed.

Lemma norm_bin1_false : norm_bin1 [:: false] = [::].
Proof. by []. Qed.


Lemma norm_bin1_nil : norm_bin1 [::] = [::].
Proof. by []. Qed.


Lemma rev_last :
forall (x b : bool) (xs : seq bool), last b (rev (x::xs)) = x.
Proof.
move=> x b xs.
by rewrite rev_cons last_rcons.
Qed.

Lemma correct_norm_bin (u : seq bool) :
bin_to_nat u == bin_to_nat (norm_bin1 u).
Proof.
elim: u => //=.
move=> x xs.
case h : (norm_bin1 xs)=> [//= | y ys].
* move/eqP => h0.
rewrite h0 muln0 addn0.
rewrite /epurate.
case: x => //=.
* move/eqP=> IH.
by rewrite IH.
Qed.

Lemma cancelB u : 
nat_to_bin (bin_to_nat u) = norm_bin1 u.
Proof.
elim: u.
* by rewrite /=.
* move=> x xs IH; rewrite /=.
case Hbtn: (bin_to_nat xs).
+ rewrite muln0 addn0; move: IH.
rewrite Hbtn nat_to_bin0 => <-.
by case: x.
+ rewrite nat_to_bin_S // -Hbtn IH.
case thenilcase : (norm_bin1 xs) => [|y ys //].
have absurd : bin_to_nat xs = 0%N.
* move: (correct_norm_bin xs).
  rewrite thenilcase //=.
  move/eqP => -> //.
move: Hbtn. 
by rewrite absurd.
Qed.

Lemma bin_to_nat_nil : bin_to_nat [::] = 0%N.
Proof. by []. Qed.

Lemma bin_to_nat_true : bin_to_nat [:: true] = 1%N.
Proof. by []. Qed.

Lemma bin_to_nat_false u : norm_bin1 u = [::] -> bin_to_nat u = 0%N.
Proof. 
move/eqP: (correct_norm_bin u)=> -> -> //. Qed.

Lemma bin_to_nat_cons x xs : bin_to_nat (x :: xs) = (x + 2 * bin_to_nat xs)%N.
Proof. by []. Qed.

Lemma uphalf_len m : (uphalf m <= m)%N.
Proof.
elim:m => //.
move=> n IH.
have uphalfS : (uphalf (n.+1) <= (uphalf n) + 1)%N.
* by rewrite /= uphalf_half -addnA addn1 ltn_addl.
rewrite -(leq_add2r 1 (uphalf n) n) in IH. 
rewrite -{2}[n.+1]addn1.
apply: (leq_trans uphalfS IH).
Qed.

Lemma uphalf_S m : (~~ odd m + 2 * (odd m + m./2))%N = m.+1.
Proof.
move: (odd_double_half m)=> Hm.
rewrite -[m.+1]addn1 -{4}Hm.
case HHm : (odd m) => /=; rewrite !add0n.
by rewrite mulnDr muln1 [(1 + (m./2).*2)%N]addnC -[((m./2).*2 + 1 + 1)%N]addnA addn1 addnC mul2n.
by rewrite mul2n addnC.
Qed.

Lemma cancelN n : 
bin_to_nat (nat_to_bin n) = n.
Proof. 
elim/general_ind : n => n IH.
case Hn : n => [// | m].
have h : nat_to_bin (uphalf m) = nat_to_bin_aux (uphalf m) m. 
* rewrite /nat_to_bin; symmetry.
  apply : nat_to_bin_aux_G.
  by rewrite uphalf_len.
* rewrite /= -h IH.
+ by rewrite uphalf_half uphalf_S.
+ have mltn : (m < n)%N. by rewrite Hn ltnSn.
  by apply: (leq_ltn_trans (uphalf_len m) mltn).
Qed.
 
Definition block (u : seq bool) (w i : nat) :=
 mkseq (fun k => nth false u (w*i + k)) w.

(*first block is the zero-block*)
(* when i > (size u)%/w then block = [::false; .. ; false] *)
(* block [::] w i = [::false; .. ;false] *)

Definition n_blocks (u : seq bool) (w : nat) :=
if size u is 0%N then 0%N
else (((size u).-1) %/ w).+1.

Lemma size_block u w i: 
size (block u w i) = w.
Proof.
by rewrite size_mkseq.
Qed.

Lemma block_size0 u i w: w = 0%N -> block u w i = [::]. 
Proof. by move => ->. Qed.

Lemma n_blocks_nil w : n_blocks [::] w = 0%N.
Proof. by []. Qed.

Lemma n_blocks_size0 u : u != [::] -> n_blocks u 0%N = 1%N.
Proof. by case : u. Qed.

Lemma n_blocks_cons x xs w : n_blocks (x :: xs) w != 0%N.
Proof. by []. Qed.

Lemma n_blocks0_eq_nil u w : (n_blocks u w == 0%N) = (u == [::]).   
Proof.
apply/eqP/eqP => h.
+ by case : u h.
+ by rewrite h n_blocks_nil.
Qed.

Variable G : zmodType.

Definition expG w (u : seq bool) (P : G) :=
    let d := (n_blocks u w) in
    foldl
      (fun R i =>
        let R := R *+ (2^w) in
          R + (P *+ (bin_to_nat (block u w i))))
      0 (rev (iota 0 d)).

Lemma expG_nil w P : expG w [::] P = 0.
Proof. by []. Qed.

(* true but not useful finaly *)
(*
Lemma n_blocks_decr b w1 w2 :
(w1 < w2)%N -> (n_blocks b w1 >= n_blocks b w2)%N.
move=> ineq.
case: b=> [//=|x xs].
rewrite /n_blocks /=.
set s:= size _.
case H : (s %/ w1 == s %/ w2).
by rewrite (eqP H) ltnSn.
rewrite ltnS; move/negbT: H => ineqdiv.
admit.
Qed.
*)

Lemma size_normalized_lt_seq b:
(size (norm_bin1 b) <= size b)%N.
Proof.
elim:b => [//= | x xs IH].
rewrite /=; case H : (norm_bin1 xs) => [|y ys].
+ by case: x => /=.
+ rewrite {1}/size // -/size.
have hsize : size (norm_bin1 xs) = (size ys).+1.
* by rewrite H.
by rewrite -hsize ltnS.
Qed.

Lemma size_seq_lt_block b (w : nat):
  w != 0%N -> ((size b) <= w * (n_blocks b w))%N.
Proof.
move=> wNz.
elim:b => [//| x xs IH].
rewrite /n_blocks //=  mulnC; apply: ltn_ceil.
by rewrite lt0n.
Qed.

Lemma nat2bin_size_block b (w : nat):
  w != 0%N -> (size (norm_bin1 b) <= w * (n_blocks b w))%N.
Proof. 
move=> wNz.
move: (size_seq_lt_block b w wNz) => ineq.
apply: (leq_trans (size_normalized_lt_seq b) ineq).
Qed.

Lemma norm_bin1_cons_true xs : 
 norm_bin1 (true :: xs) = true :: (norm_bin1 xs).
Proof.
case H : (norm_bin1 xs) => [|y ys] ; by rewrite /= H.
Qed.

Lemma norm_bin1_cons_false1 xs : 
norm_bin1 xs != nil -> norm_bin1 (false :: xs) = false :: (norm_bin1 xs).
Proof.
case H : (norm_bin1 xs) => [|y ys] ; by rewrite /= H.
Qed.

Lemma norm_bin1_cons_false2 xs : 
norm_bin1 xs = nil -> norm_bin1 (false :: xs) = (norm_bin1 xs).
Proof.
move=> Hnil.
by rewrite /= Hnil.
Qed.

Lemma half_leqn n : ((n./2) <= n)%N.
Proof. by rewrite -divn2 leq_div. Qed.

Lemma halfS_ltSn n : (((n.+1)./2) < n.+1)%N.
Proof. 
rewrite -divn2.
by apply: ltn_Pdiv.
Qed.

Lemma nat2bin_normalized n:
  norm_bin1 (nat_to_bin n) = nat_to_bin n.
Proof. 
elim/general_ind : n => n IH.
rewrite /nat_to_bin; case Hn : n => [//|m].
rewrite nat_to_bin_simpl; case H : (odd m.+1).
+ rewrite norm_bin1_cons_true !nat_to_bin_aux_G; last by rewrite -ltnS halfS_ltSn.
  rewrite !IH //; by rewrite Hn halfS_ltSn. 
+ rewrite !nat_to_bin_aux_G; last by rewrite -ltnS halfS_ltSn.
  have h : nat_to_bin (m.+1)./2 = nat_to_bin_aux (m.+1)./2 (m.+1)./2. by [].
  rewrite -h; set s := nat_to_bin _ ; rewrite /=.
  have notodd : ((m.+1)./2 > 0)%N.
  * move/negbT : H; rewrite -dvdn2 -divn2; move=> H; by rewrite ltn_divRL.
  case H1 : (norm_bin1 s)=> [|x xs //].
  * move: H1; rewrite /s; move/bin_to_nat_false; rewrite cancelN.
    move: notodd; rewrite lt0n; move=> h1 h2. 
    move: h1; by rewrite h2.
  * by rewrite -H1 /s IH ; last by rewrite Hn halfS_ltSn.
Qed.

Lemma bin_to_nat_MSB0:
  forall b n, bin_to_nat (b ++ nseq n false) = bin_to_nat b. 
Proof. 
move=> b n.
elim: b=> //=.
+ elim: n => //=.
  move=> n IH; by rewrite IH.
+ move=> x xs IH; by rewrite IH.
Qed.

Lemma bin_to_nat_singl b : bin_to_nat [:: b] = b%N.
Proof.
case : b.
by rewrite bin_to_nat_true.
by apply: bin_to_nat_false.
Qed.

Lemma bin_to_nat_last x xs : 
bin_to_nat (rcons xs x) = 
((bin_to_nat xs) + bin_to_nat [:: x] * 2 ^ (size xs))%N.
Proof.
elim: xs=> [ /= |y ys IH].
+ by rewrite !muln0 !addn0 add0n expn0 muln1.
+ rewrite /= muln0 addn0 IH bin_to_nat_singl.
  rewrite expnS mulnA [(x * 2)%N]mulnC mulnDr.
  by rewrite addnA mulnA.
Qed.

Lemma take_drop_lemma l k : 
bin_to_nat l = (bin_to_nat (take k l) + bin_to_nat (drop k l) * 2 ^ k)%N.
Proof.
case H : (l == [::]).
* rewrite (eqP H) //=.
* elim : k => [| n IH].
  + by rewrite take0 drop0 expn0 muln1.
  + move/negbT :H.
    rewrite -[l!= [::]]Bool.andb_true_r.
    move/predD1P; case => lNnil _.
    case Hsize: (size l < n.+1)%N; last first.
    * have Hn: (n < size l)%N. 
    by rewrite ltnNge (negbT Hsize).
    rewrite (@take_nth _ false _ _) // bin_to_nat_last size_takel; last first.
    + by rewrite leq_eqVlt Hn orbT.
    + rewrite expnS mulnA -addnA -mulnDl [(_ * 2)%N]mulnC.
    rewrite bin_to_nat_singl -bin_to_nat_cons -drop_nth //.
    * rewrite take_oversize.
    rewrite drop_oversize.
    rewrite bin_to_nat_nil mul0n addn0 //.
    by apply: ltnW.
    by apply: ltnW.
Qed.

Lemma block_false bs w i k:
block (bs ++ nseq k false) w i = block bs w i. 
Proof.
rewrite /block /=.
have funeq : (fun k0 : nat => nth false (bs ++ nseq k false) (w * i + k0)) =1
(fun k0 : nat => nth false bs (w * i + k0)).
+ move=> n /=.
  rewrite nth_cat.
  case H : (w * i + n < size bs)%N => //.
  rewrite nth_nseq //=.
  case: (w * i + n - size bs < k)%N ; symmetry; apply: nth_default; by rewrite leqNgt H.
move: (eq_mkseq funeq)=> H.
by rewrite (H w).
Qed.

Lemma take_block us w i : 
w != 0%N -> 
(w * i.+1 <= size us)%N ->
(block us w i) = take w (drop (w * i) us).
Proof.
move=> wNz ineq.
apply: (@eq_from_nth _ false _ _).
rewrite size_block size_take size_drop.
+ have H : (w <= size us  - w * i)%N.
    rewrite -(leq_add2r (w * i) _ _) subnK.
    by rewrite addnC -{2}[w]muln1 -mulnDr addn1.
    have h : (w * i <= w * i.+1)%N.
    by rewrite leq_pmul2l ?leqnSn // ?lt0n.
    by apply: leq_trans h ineq.
  move: H; rewrite leq_eqVlt.
  move/orP; case=> H.
  by rewrite -(eqP H) //= ltnn.
  by rewrite H.
+ rewrite size_block; move=> k Hsize.
  by rewrite nth_take // nth_drop /block nth_mkseq.
Qed.

(* missing property for drop *)
Lemma drop_add k m (us: seq bool) : drop (k + m) us = drop k (drop m us). 
Admitted.

Lemma lemma us w i : 
  w != 0%N -> 
  (w * i.+1 <= size us)%N ->
  (bin_to_nat (drop (w * i.+1) us) * 2 ^ w  +  bin_to_nat (block us w i))%N  =  
  bin_to_nat (drop (w * i) us).
Proof.
move=> wNz ineq.
rewrite take_block //.
have dropw : drop (w * i.+1) us = drop w (drop (w * i) us). 
by rewrite -addn1 mulnDr muln1 addnC drop_add.
rewrite dropw.
rewrite addnC.
by rewrite -take_drop_lemma.
Qed.


(* Fancy proof :) *)
Lemma expG_correct : forall (P : G) (n w : nat),
  w != 0%N -> expG w (nat_to_bin n) P = P *+ n.
Proof.
  move=> x n w nz_w; rewrite /expG foldl_rev.
  set d := (n_blocks _ _).
  set f := (fun _ _ => _).
  rewrite -[n]cancelN -(bin_to_nat_MSB0 _ (w * d - size (nat_to_bin n))).
  set u := (nseq _ _).
  have ->: nat_to_bin n ++ u = drop (w * (d - d)) (nat_to_bin n ++ u).
    by rewrite subnn muln0 drop0.
  move: (erefl (0 + d)%N).
  rewrite {1}add0n => /esym.
  move: 0%N => i; move: {1 3 5}d => j.
  elim : j i => [|j IH] i //=.  
   move=> _;  rewrite subn0 drop_oversize //.
   rewrite -nat2bin_normalized.
   rewrite size_cat size_nseq.
   rewrite nat2bin_normalized addnC subnK ?leqnn //.
   + rewrite /d -{1}nat2bin_normalized; by apply: nat2bin_size_block.
  move=> H; rewrite IH /f; last by rewrite addSnnS.
  rewrite -mulrnA -mulrnDr; congr (_ *+ _).
  rewrite -H -{1}addSnnS -!addnBA // !subnn !addn0.
  set us := nat_to_bin n ++ u.
  have Hblock : block (nat_to_bin n) w i = block us w i.
  by rewrite /us /u block_false.
  rewrite Hblock.
  apply: lemma => //.
  have size_us : size us = (w * d)%N.
  rewrite /us size_cat /u size_nseq subnKC //.
  by rewrite /d -{1}nat2bin_normalized nat2bin_size_block.
  rewrite size_us leq_pmul2l ?lt0n.
  by rewrite -H -{1}[i]addn0 ltn_add2l.
  done.
Qed.


(******************************************)
(*          MULTIEXPONENTIATION !!!       *)
(******************************************)

Definition algoG (w : nat) (u v : seq bool) (P Q : G) :=
let d := maxn (n_blocks u w) (n_blocks v w) in 
foldl 
( fun (R : G) (i : nat) => 
 let R0 := R *+ 2 ^ w in 
   R0 + (P *+ bin_to_nat (block u w i)) + (Q *+ bin_to_nat (block v w i)))  0
(rev (iota 0 d)).

Lemma algo_nil2 w P Q : algoG w [::] [::] P Q = 0.
Proof. by []. Qed.

Lemma algo_correct :
  forall (P Q : G) (n m w : nat), 
    w != 0%N -> 
    algoG w (nat_to_bin n) (nat_to_bin m) P Q = P *+ n + Q *+ m.
Proof.
  move=> P Q n m w nz_w; rewrite /algoG foldl_rev.
  set d := maxn  _ _.
  set f := (fun _ _ => _).
  rewrite -[n]cancelN -(bin_to_nat_MSB0 _ (w * d - size (nat_to_bin n))).
  set u := (nseq _ _).
  rewrite -[m]cancelN -(bin_to_nat_MSB0 (nat_to_bin m) (w * d - size (nat_to_bin m))).
  set v := (nseq _ _).
  have Hn: nat_to_bin n ++ u = drop (w * (d - d)) (nat_to_bin n ++ u).
    by rewrite subnn muln0 drop0.
  have Hm: nat_to_bin m ++ v = drop (w * (d - d)) (nat_to_bin m ++ v).
    by rewrite subnn muln0 drop0.
  rewrite Hn Hm; clear Hn Hm.
  move: (erefl (0 + d)%N).
  rewrite {1}add0n => /esym.
  move: 0%N => i; move: {1 3 5 7}d => j.
  elim : j i => [|j IH] i //=.  
   move=> _;  rewrite subn0 !drop_oversize //.
   by rewrite bin_to_nat_nil !mulr0n addr0.
   + rewrite size_cat size_nseq subnKC.
   by rewrite leqnn.
   move: (size_seq_lt_block (nat_to_bin m) w nz_w)=> H1.
   move: (leq_maxr (n_blocks (nat_to_bin n) w) (n_blocks (nat_to_bin m) w)).
   rewrite -/d -(@leq_pmul2l w (n_blocks (nat_to_bin m) w) d) ?lt0n //.
   move=> H2; by rewrite (leq_trans H1 H2).
   + rewrite size_cat size_nseq subnKC.
   by rewrite leqnn.
   move: (size_seq_lt_block (nat_to_bin n) w nz_w)=> H1.
   move: (leq_maxl (n_blocks (nat_to_bin n) w) (n_blocks (nat_to_bin m) w)).
   rewrite -/d -(@leq_pmul2l w (n_blocks (nat_to_bin n) w) d) ?lt0n //.
   move=> H2; by rewrite (leq_trans H1 H2).
 move=> H; rewrite IH /f; last by rewrite addSnnS.
 set us := nat_to_bin n ++ u.
 set vs := nat_to_bin m ++ v.
 rewrite mulrnDl -!mulrnA [(P *+ _) + _]addrC.
 set q1 := (bin_to_nat (drop (w * (d - j)) vs) * 2 ^ w)%N.
 set q2 := bin_to_nat (block (nat_to_bin m) w i)%N.
 set p1 := (bin_to_nat (drop (w * (d - j)) us) * 2 ^ w)%N.
 set p2 :=  bin_to_nat (block (nat_to_bin n) w i)%N.
 rewrite -[Q *+ q1 + P *+ p1 + P *+ p2]addrA.
 rewrite -mulrnDr addrC addrA -mulrnDr addrC.
 have Hp : (p1 + p2 = bin_to_nat (drop (w * (d - j.+1)) us))%N.
 * rewrite /p1 /p2.
 have Hblock : block (nat_to_bin n) w i = block us w i.
 by rewrite /us /u block_false.
 rewrite Hblock.
 rewrite -H -{1}addSnnS -!addnBA // !subnn !addn0.
 apply: lemma=> //.
 + rewrite /us size_cat /u size_nseq subnKC -H.
  rewrite leq_pmul2l ?lt0n //.
  move: (ltn_add2l i 0 j.+1);  by rewrite addn0.
 + rewrite H.
  move: (size_seq_lt_block (nat_to_bin n) w nz_w)=> H1.
  move: (leq_maxl (n_blocks (nat_to_bin n) w) (n_blocks (nat_to_bin m) w)).
  rewrite -/d -(@leq_pmul2l w (n_blocks (nat_to_bin n) w) d) ?lt0n //.
  move=> H2; by rewrite (leq_trans H1 H2).
 have Hq : (q1 + q2 = bin_to_nat (drop (w * (d - j.+1)) vs))%N.
 * rewrite /q1 /q2.
 have Hblock : block (nat_to_bin m) w i = block vs w i.
 by rewrite /us /u block_false.
 rewrite Hblock.
 rewrite -H -{1}addSnnS -!addnBA // !subnn !addn0.
 apply: lemma=> //.
 + rewrite /us size_cat /u size_nseq subnKC -H.
  rewrite leq_pmul2l ?lt0n //.
  move: (ltn_add2l i 0 j.+1);  by rewrite addn0.
 + rewrite H.
  move: (size_seq_lt_block (nat_to_bin m) w nz_w)=> H1.
  move: (leq_maxr (n_blocks (nat_to_bin n) w) (n_blocks (nat_to_bin m) w)).
  rewrite -/d -(@leq_pmul2l w (n_blocks (nat_to_bin m) w) d) ?lt0n //.
  move=> H2.
  by rewrite (leq_trans H1 H2).
rewrite [(q2 + q1)%N]addnC.
by rewrite Hp Hq.
Qed.

Lemma algo_nilf w m P Q : w != 0%N -> algoG w [::] (nat_to_bin m) P Q = Q *+ m.
Proof. 
  move=> wNz.
  rewrite -nat_to_bin0 algo_correct //.
  by rewrite mulr0n add0r.
Qed.

Lemma algo_nils w n P Q : w != 0%N -> algoG w (nat_to_bin n) [::] P Q = P *+ n.
Proof. 
  move=> wNz.
  rewrite -nat_to_bin0 algo_correct //.
  by rewrite mulr0n addr0.
Qed.

End Multiexponentiation.


Section Decomposition.

(****************************************)
(*        short vectors                 *)
(****************************************)
(*  The Algorithm :                     *)          
(*                                      *)                   
(* Let E ec over Fq                     *) 
(* Let P <- E(Fq) of prime order n      *) 
(* Let h endomorphism over Fq and       *)
(* Let l : nat, st h(P) = [l]*P         *)
(*                                      *)
(* Input : n, l, k                      *)
(* Output k1 and k2 st k = k1 + k2 * l [mod n]       *)
(*                                                   *)
(*   Methodology                                     *)
(* Following the GLV-paper we can divide the problem *)
(*   into the two following subproblems:             *)
(* (1) finding two short linearly ind vectors v1 = (x1, y1), v2 = (x2, y2) st  *)
(* f (v1) = f (v2) = 0 i.e.                                                    *) 
(* (x1 + lamda * y1) mod n = (x2 + lamda * y2) mod n  = 0                      *)
(* (2) find vector v in the lattice L(v1, v2) close to (k, 0)                  *)
(* Then we take (k1 , k2) = (k, 0) - v                                         *)
(*******************************************************************************)

Definition P (a b : nat) (r : nat) (x y : int) :=
  r%:Z = x * a%:Z + y * b%:Z.

 Fixpoint eea_rec (r' : nat) (u' v' : int) (acc : seq (nat * int * int)) n :=
  match n with
  | 0    => None
  | n.+1 =>
    if   r' == 0%N
    then Some acc
    else
      let: (r, u, v) := head (0%N, 0, 0) acc in
        let (q, m) := (r %/ r', r %% r') in
          eea_rec m (u - q%:Z * u') (v - q%:Z * v') ((r', u', v') :: acc) n
  end.

Definition eea (a b : nat) : seq (nat * int * int) :=
  if   a == 0%N
  then [:: (b, 0, 1)]
  else odflt [::] (eea_rec b 0 1 [:: (a, 1, 0)] (maxn a b).+1).

(***************************)

Lemma relation_eea_rec a b: 
  forall r' u' v' (acc : (seq (nat * int * int))) n,
    (P a b) r' u' v' ->
    (forall r x y, (r, x, y) \in acc -> (P a b) r x y )-> 
    acc != [::] -> 
    (forall r u v, (r, u, v) \in odflt [::] (eea_rec r' u' v' acc n) -> 
      (P a b) r u v).
Proof.
  move=> r' u' v' acc n.
  elim : n acc r' u' v' => [//|n IH acc r' u' v']. 
  case Hr' : r' IH => [//=|m]  IH P1 inacc acc_Nnil r u v /=.
  set R := head _ _ .
  have : R = head (0%N, 0, 0) acc. done. 
  move: R => [[r1 u1] v1] HR H.
  apply : (IH  ((m.+1, u', v') :: acc) (r1 %% m.+1) (u1 - (r1 %/ m.+1)%:Z * u') (v1 - (r1 %/ m.+1)%:Z * v')); 
    rewrite //=; last first.
  + move => r0 x y; rewrite in_cons; case/orP.
  by move/eqP=>  [-> -> ->].
  by apply: inacc.
  + have HP : P a b r1 u1 v1.
  apply: inacc; by rewrite HR -nth0 mem_nth // lt0n size_eq0.
  move: HP; rewrite /P => HP; rewrite -Hr'.
  set k := _ %% _; set q := _ %/ _.
  rewrite !mulrBl addrAC addrA -HP -!mulrA -addrA -!mulNr -(mulrDr (- q%:Z) (v' * b) (u' * a)).
  rewrite -Hr' /P in P1. 
  rewrite [_ * _ + _ * _]addrC -P1 /k /q {2}(divn_eq r1 r') mulNr.
  symmetry; apply/eqP; by rewrite subr_eq addrC.
Qed.


Lemma relation_eea a b :
  forall v,  
    let: (r, x, y) := v in
      (r, x, y) \in (eea a b) -> (P a b) r x y.
Proof.
  move=> [[r x] y]; rewrite /eea /P.
  case Ha : (a == 0%N).
  + by rewrite mem_seq1 => /eqP [-> -> ->]; rewrite mul0r mul1r add0r.
  + set d := (maxn _ _).+1 ; set acc := [:: _]; move=> H.
  apply: (relation_eea_rec a b b 0 1 acc d).
  * by rewrite /P mul0r add0r mul1r.
  * move=> r1 x1 y1; rewrite /acc /P.  
  by rewrite mem_seq1 => /eqP [-> -> ->]; rewrite mul0r mul1r addr0.
  * by rewrite /acc.
  done.
Qed.


Lemma eea_mod a b :
  forall v,  
    let: (r, x, y) := v in
      (r, x, y) \in (eea a b) -> r%:Z - y * b%:Z = x * a%:Z.  
Proof.
  move=> [[r x] y] H.
  move: (relation_eea a b (r, x, y) H).
  rewrite /P; move/eqP; rewrite -subr_eq; move/eqP => //.
Qed.


Lemma in_acc_in_eea r u v (acc : seq ( nat * int * int)) 
n (x : nat * int * int) :
(r <= n)%N -> 
x \in acc -> x \in odflt [::] (eea_rec r u v acc n.+1). 
Proof.
elim : n acc r u v x.
+ move=> acc r u v x; rewrite leqn0.
move/eqP => -> //.
+ move=> n IH acc r u v x rleqSn xin.
case Head : (head (0%N, 0%:Z, 0%:Z) acc) => [[r1 u1] v1]. 
set q := r1 %/ r; set m := r1 %% r.
have H1 : r == 0%N -> odflt [::] (eea_rec r u v acc n.+2) = acc.
* move/eqP => -> //.
have H2 : r != 0%N -> eea_rec r u v acc n.+2 = 
eea_rec m (u1 - q%:Z * u) (v1 - q%:Z * v) ((r, u, v) :: acc) n.+1.
* move=> rnz; by rewrite //= Head (negbTE rnz) /m.
case Hr : (r == 0%N); first by rewrite (H1 Hr).
rewrite (H2 (negbT Hr)); apply: IH.
rewrite /m; move: rleqSn.
rewrite leq_eqVlt; move/orP; case => H.
* by rewrite (eqP H) -ltnS ltn_mod.
* have : (r1 %% r < r)%N. 
by rewrite ltn_mod lt0n (negbT Hr).
move=> lt2; rewrite -ltnS.
by rewrite (ltn_trans lt2 H).
* rewrite in_cons; apply/orP; by right.
Qed.

Lemma size_cons : forall (T : Type) (x : T) (xs : seq T), 
size (x :: xs) = (size xs).+1.  
Proof. by rewrite {1}/size. Qed.

Lemma eea_size_nz a b :
a != 0%N -> b != 0%N -> (size (eea a b) > 1)%N.
Proof.
move=> a_nz b_nz.
have a_in : (a, 1, 0) \in (eea a b).
+ rewrite /eea (negbTE a_nz). 
  apply: in_acc_in_eea; by rewrite ?inE ?eqxx ?leq_maxr.
have b_in : (b, 0, 1) \in (eea a b).
  rewrite /eea (negbTE a_nz) /= (negbTE b_nz).
  case Hmaxn : (maxn _ _)=> [|n].  
+ move: Hmaxn; rewrite /maxn; case ineq : (a < b)%N => H.
  by move: b_nz; rewrite H.
  by move: a_nz; rewrite H.
+ apply: in_acc_in_eea.
* rewrite -ltnS -Hmaxn; move: (leq_maxr a b)=> H2.
  have H1: (a %% b < b)%N by rewrite ltn_mod lt0n.
  move: H2; rewrite leq_eqVlt; move/orP; case.
  + move/eqP=> H2; rewrite -H2 ltn_mod lt0n //.
  + by apply: ltn_trans.
* rewrite inE; apply/orP; left; done.
case: (eea a b) a_in b_in => [//|x xs].
rewrite in_cons; move/orP; case=> A.
+ rewrite in_cons; move/orP; case=> B.
  move/eqP:A => A; move:B; rewrite -A. 
  by rewrite !xpair_eqE //= oner_eq0 Bool.andb_false_r. 
  rewrite size_cons; case: xs B => [//| y ys B].
  by rewrite size_cons.
+ rewrite in_cons; move/orP; case=> B.
  move/eqP:B => B; rewrite size_cons.
  case: xs A => [//| y ys A]; by rewrite size_cons.
  rewrite size_cons; case: xs A B => [//| y ys A].
  by rewrite size_cons.
Qed.


Definition filter_sqrr (n : nat) (rs : seq (nat * int * int)) :=
[seq t <- rs | let: (r, x, y) := t in (n <= r ^2)%N].


Definition eea_sqrr (n l : nat) :=
filter_sqrr n (eea n l).


Lemma head_in n l :  head (0%N, 0%:Z, 0%:Z) (eea_sqrr n l) \in eea n l. 
Proof.
rewrite /eea_sqrr; set s := eea _ _.
have Hs : forall x, x \in (filter_sqrr n s) -> x \in s.
+ move=> x; rewrite /filter_sqrr mem_filter.
move/andP; case=> _ -> //.
+ apply: Hs; rewrite -nth0; apply: mem_nth.
rewrite lt0n size_eq0 /filter_sqrr /s -has_filter //=.
apply/hasP => //=; case Hn : n => [|k].
+ rewrite /eea //=; exists (l, 0, 1); rewrite ?inE ?eqxx ?leq0n //.
+ rewrite /eea.
have Hk : (k.+1 == 0%N) = false by [].
rewrite Hk; clear Hk; exists (k.+1, 1, 0).
apply: in_acc_in_eea; rewrite ?leq_maxr ?inE //.
clear Hn; case:k => [//|k].
rewrite -mulnn -{1}[k.+1]mul1n.
by apply: ltn_mul.
Qed.



Lemma eea_size_gt0 a b :
(size (eea a b) > 0)%N.
Proof.
rewrite lt0n size_eq0.
case H: (eea a b)=> [|//].
move: (head_in a b); by rewrite H.
Qed.


(* as it is in the math proof but for our case is just the index of the head *)
(* not used in the proof *)
Definition maxrseq (n l : nat) :=
\max_(i <- (eea_sqrr n l)) (index i (eea n l)). 

Definition index_hd (n l : nat) :=
index (head (0%N, 0, 0) (eea_sqrr n l)) (eea n l).

(* before
Definition base (n l : nat) :=
if (l %| n) then ((l, -1),(n, 0)) else
let m := index_hd n l in 
let: (r1, x1, y1) := nth (0%N, 0, 0) (eea n l) m.-1 in 
let: (r0, x0, y0) := nth (0%N, 0, 0) (eea n l) m in 
let: (r2, x2, y2) := nth (0%N, 0, 0) (eea n l) m.-2 in 
if (r0%:Z ^+ 2 + y0 ^+ 2 <= r2%:Z ^+ 2 + y2 ^+ 2) then ((r1, -y1),(r0, -y0))
else ((r1, -y1),(r2, -y2)).
(*  what is going on with the first if branch :                    *)
(*  if l %| n then size (eea n l) == 2                             *)
(*  in that case we have m = index_hd n l = 0 or 1                 *)
(*  and then m-1 or m-2 = -1 in theory                             *)
(*  but by definition in nat, 0.-1 = 0                             *)
(*  i.e. if m == 0 => m.-1 == 0 => m.-2 == 0  case 5 5             *)
(*  in practice we never enter the if branch because n is prime    *)
(*  (page 4 of the GLV article :) Let E be an ec defined over Fq   *)
(*   and P <- E(Fq) be a point of prime order n                    *)

(*  in the case that l %| n we definitely have a problem but it will never happen  *)
(*  if l does not divide n then size (eea n l) >= 3                                *)
(*  but in that case we may have problems too                                      *)
(*  because nothing stops m from being 1 or 0 ,                                    *) 
(*  (case 9 8,  m = 1) (case 9 87, m = 0)                                          *)
(*  m == 0 -> take (triplet_0, triplet_1) what else can I do ?                     *)
(*  m == 1 -> take (triplet_0, triplet_1) this is normal enough                    *)
*)

Definition base (n l : nat) :=
let m := index_hd n l in 
if (m <= 1)%N then 
let: (r0, x0, y0) := nth (0%N, 0, 0) (eea n l) 0%N in 
let: (r1, x1, y1) := nth (0%N, 0, 0) (eea n l) 1%N in 
((r0, -y0),(r1, -y1))
else 
let: (r1, x1, y1) := nth (0%N, 0, 0) (eea n l) m.-1 in 
let: (r0, x0, y0) := nth (0%N, 0, 0) (eea n l) m in 
let: (r2, x2, y2) := nth (0%N, 0, 0) (eea n l) m.-2 in 
if (r0%:Z ^+ 2 + y0 ^+ 2 <= r2%:Z ^+ 2 + y2 ^+ 2) then ((r1, -y1),(r0, -y0))
else ((r1, -y1),(r2, -y2)).


(****************************************************)
(* n != 0 ok because n = order of the point & n prime *)
(* l != 0 ok because l from the endomorphism of the curve *)
(* to clean *)
Lemma base_modn_snd n l :
n != 0%N -> l != 0%N ->
let (u,v) := base n l in 
((v.1)%:Z + v.2 * l = 0 %[mod n])%Z.
Proof.
move=> n_nz l_nz.
case Hbase : (base n l)=> [u v]. 
apply /eqP.
rewrite eqz_mod_dvd subr0.
set m := index_hd n l. 
case Hm : (m <= 1)%N.
+ move : (Hbase); rewrite /base Hm.
case Hnth0 : (nth (0%N, 0, 0) (eea n l) 0) => [[r0 x0] y0]. 
case Hnth1 : (nth (0%N, 0, 0) (eea n l) 1) => [[r1 x1] y1]. 
move/eqP; rewrite xpair_eqE; move/andP; case => Hu Hv.
rewrite (surjective_pairing u) in Hu; rewrite (surjective_pairing v) in Hv.
move : Hv; rewrite xpair_eqE; case/andP; rewrite eq_sym; move/eqP=> -> //.
rewrite eq_sym; move/eqP=> -> //.
apply/dvdzP.
exists x1.
rewrite mulNr.
apply: (eea_mod n l (r1, x1, y1)).
rewrite -Hnth1; apply: mem_nth.
apply: eea_size_nz => //.

(* seconde case *)
move : (Hbase); rewrite /base Hm.
case Hnth : (nth (0%N, 0, 0) (eea n l) m.-1) => [[rm xm] ym].
case Hnth0 : (nth (0%N, 0, 0) (eea n l) m) => [[rm0 xm0] ym0]. 
case Hnth2 : (nth (0%N, 0, 0) (eea n l) m.-2) => [[rm2 xm2] ym2]. 
case H : (rm0%:Z ^+ 2 + ym0 ^+ 2 <= rm2%:Z ^+ 2 + ym2 ^+ 2).

(*one*)
move/eqP; rewrite xpair_eqE; move/andP; case.
move=> _; rewrite eq_sym; move/eqP=> //.
rewrite (surjective_pairing v).
move/eqP; rewrite xpair_eqE; move/andP; case => H1 H2.
rewrite (eqP H1) (eqP H2) //=.
apply/dvdzP.
exists xm0.
rewrite mulNr.
apply : (eea_mod n l (rm0, xm0, ym0)).
rewrite -Hnth0.
apply: mem_nth.
rewrite /m /index_hd.
by rewrite index_mem head_in.

(* two *)
move/eqP; rewrite xpair_eqE; move/andP; case.
move=> _; rewrite eq_sym; move/eqP=> //.
rewrite (surjective_pairing v).
move/eqP; rewrite xpair_eqE; move/andP; case => H1 H2.
rewrite (eqP H1) (eqP H2) //=.
apply/dvdzP.
exists xm2.
rewrite mulNr.
apply : (eea_mod n l (rm2, xm2, ym2)).
rewrite -Hnth2.
apply: mem_nth.

have Hinter: (m < size (eea n l))%N.
by rewrite /m /index_hd index_mem head_in.

have Hfst : (m.-2 < m)%N.
move: (leq_trans (leq_pred m.-1) (leq_pred m)).
rewrite leq_eqVlt.
move/orP; case=> //.
move/eqP => H0.

case h : m=> [|x].
by move: Hm; rewrite h.
rewrite //=.
case X : x=> [//|y //].
apply: (ltn_trans Hfst Hinter).
Qed.

Lemma base_modn_fst n l :
let (u,v) := base n l in 
((u.1)%:Z + u.2 * l = 0 %[mod n])%Z.
Proof.
case Hbase : (base n l)=> [u v]. 
apply /eqP.
rewrite eqz_mod_dvd subr0.
set m := index_hd n l. 
case Hm : (m <= 1)%N. 
+ move : (Hbase); rewrite /base Hm.
case Hnth0 : (nth (0%N, 0, 0) (eea n l) 0) => [[r0 x0] y0]. 
case Hnth1 : (nth (0%N, 0, 0) (eea n l) 1) => [[r1 x1] y1]. 
move/eqP; rewrite xpair_eqE; move/andP; case => Hu Hv.
rewrite (surjective_pairing u) in Hu; rewrite (surjective_pairing v) in Hv.
move : Hu; rewrite xpair_eqE; case/andP; rewrite eq_sym; move/eqP=> -> //.
rewrite eq_sym; move/eqP=> -> //.
apply/dvdzP.
exists x0.
rewrite mulNr.
apply: (eea_mod n l (r0, x0, y0)).
rewrite -Hnth0; apply: mem_nth.
by rewrite eea_size_gt0.

move : (Hbase); rewrite /base Hm.
case Hnth : (nth (0%N, 0, 0) (eea n l) m.-1) => [[rm xm] ym].
case Hnth0 : (nth (0%N, 0, 0) (eea n l) m) => [[rm0 xm0] ym0]. 
case Hnth2 : (nth (0%N, 0, 0) (eea n l) m.-2) => [[rm2 xm2] ym2]. 

move=> Hu.

have U : u = (rm, -ym).
case H : (rm0%:Z ^+ 2 + ym0 ^+ 2 <= rm2%:Z ^+ 2 + ym2 ^+ 2).
+ move/eqP: Hu; rewrite H //.
rewrite xpair_eqE; move/andP; case.
rewrite eq_sym. move/eqP=> U _; by rewrite U.
+ move/eqP: Hu; rewrite H //.
rewrite xpair_eqE; move/andP; case.
rewrite eq_sym. move/eqP=> U _; by rewrite U.
move:U; rewrite (surjective_pairing u).
move/eqP; rewrite xpair_eqE; move/andP; case => H1 H2.
rewrite (eqP H1) (eqP H2) //=.
apply/dvdzP.
exists xm.
rewrite mulNr.
apply: (eea_mod n l (rm, xm, ym)).
rewrite -Hnth; apply: mem_nth.

have ineq : (m < size (eea n l))%N.
by rewrite /m /index_hd index_mem head_in. 
apply: leq_ltn_trans (leq_pred m) ineq.
Qed.


(*approximation of n/m (in Q) by an integer*)
Definition approx (n m : nat) := 
let r := n %% m in 
let q := n %/ m in
if (2*r <= m)%N then q else q.+1. 

Definition approxZ (n m : int) :=
((sgz n) * (sgz m)) * (approx (absz n) (absz m))%:Z.


(*using base*) 
Definition cramer_coefs n l k :=
let (u, v) := base n l in 
let D := u.1%:Z * v.2 - u.2 * v.1%:Z in
(approxZ (k * v.2) D, approxZ (- k * u.2) D).


Definition decomp (n l k : nat) :=
let (a, b) := cramer_coefs n l k in 
let (u, v) := base n l in 
let k1 := k%:Z - (a * u.1%:Z + b * v.1%:Z) in 
let k2 := - (a * u.2 + b * v.2) in 
(k1, k2).


Lemma correct_decomp n l k :
let (k1, k2) := decomp n l k in
n != 0%N -> l != 0%N -> 
(k = (k1 + k2 * l) %[mod n])%Z.
Proof.
case Hdecomp : (decomp n l k)=> [k1 k2]. 
move=> nNz lNz.
move: Hdecomp; rewrite /decomp.
case Hcramer : (cramer_coefs n l k)=> [a b]. 
case Hbase : (base n l)=> [u v]. 
move/eqP; rewrite xpair_eqE; move/andP; case => H1 H2.
move: H1; rewrite eq_sym; move/eqP => -> //.
move: H2; rewrite eq_sym; move/eqP => -> //.
rewrite mulNr mulrDl; apply/eqP.
rewrite eqz_mod_dvd.
rewrite opprB addrA opprB addrA addrC. 
rewrite addrA addrA [_ + k%:Z]addrC.
have Hk : k%:Z - k%:Z = 0.
by apply/eqP; rewrite subr_eq0.
rewrite Hk; clear Hk.
rewrite add0r -addrA [b * v.2 * l + _]addrC.
rewrite -addrA -[b * v.2 * l]mulrA -mulrDr.
rewrite addrA  -[a * u.2 * l]mulrA  -mulrDr.
rewrite [_ + u.1%:Z]addrC. 
move : (base_modn_fst n l); rewrite Hbase. 
move/eqP; rewrite eqz_mod_dvd subr0; move=> Hu.
move : (base_modn_snd n l nNz lNz); rewrite Hbase.
move/eqP; rewrite eqz_mod_dvd subr0; move=> Hv.
apply/ dvdzP.
move/dvdzP :Hu=> [x Hu].
move/dvdzP :Hv=> [y Hv].
rewrite Hu Hv.
exists (a * x + b * y).
by rewrite mulrDl !mulrA.
Qed.

End Decomposition.

Section Endomorphisms.

(*****************************************************************************)
(*                        EC ENDOMORPHISMS                                   *)
(*****************************************************************************)

Require Import prime.

  Variable K : ecuDecFieldType.
  Variable E : ecuType K.

Local Notation "\- x" := (@ECGroup.neg K E x).
Local Notation "a \+ b" := (@ECGroup.add _ E a b).

(*
Definition natmul (n : nat) (P : point K) : point K :=
  nosimpl iterop _ n (ECGroup.add E) P ∞.

Local Notation "x \*+ n" := (natmul n x) (at level 40, left associativity).
*)

Definition C (P Q : ec E) w :=
  \matrix_(i < 2 ^ w, j < 2 ^ w)
    (P *+ i + Q *+ j).

(* 
P point of E with prime order n => 
everything in the scalar mul to be done mod n
because we will be performing scalar multiplication in the < P > subgroup of E
phi Q = [l]*Q forall Q <- <P> 
*)


Variable P : ec E.
Variable n : nat.
Axiom prime_n : prime n.
Axiom order_P_is_n : (forall m : nat, (m.+1 < n)%N -> P *+ m.+1 != 0). 
Axiom order_P_is_n_2 : P *+ n = 0.
Variable phi : (ec E) -> (ec E).
Variable l : nat.


Lemma all_for_phi : forall a,
(* Q in <P> *)  phi (P *+ a) = (P *+ a) *+ l.
Admitted.


End Endomorphisms.



(*****************************************************************************)
(*                              DRAFT                                        *)
(*****************************************************************************)

Lemma base_modn_snd n l :
let (u,v) := base n l in 
exists k, 
(v.1)%:Z + v.2 * l%:Z = k * n%:Z.
Proof.
case Hbase : (base2 n l)=> [u v]; set m := index_hd n l. 
case Hm : (m <= 1)%N.

move : (Hbase); rewrite /base2 Hm.
case Hnth0 : (nth (0%N, 0, 0) (eea n l) 0) => [[r0 x0] y0]. 
case Hnth1 : (nth (0%N, 0, 0) (eea n l) 1) => [[r1 x1] y1]. 

move/eqP; rewrite xpair_eqE; move/andP; case => Hu Hv.


rewrite (surjective_pairing u) in Hu; rewrite (surjective_pairing v) in Hv.
move : Hv; rewrite xpair_eqE; case/andP; rewrite eq_sym; move/eqP=> -> //.
rewrite eq_sym; move/eqP=> -> //.
exists x1.
admit.

move : (Hbase); rewrite /base2 Hm.

case Hnth : (nth (0%N, 0, 0) (eea n l) m.-1) => [[rm xm] ym].
case Hnth0 : (nth (0%N, 0, 0) (eea n l) m) => [[rm0 xm0] ym0]. 
case Hnth2 : (nth (0%N, 0, 0) (eea n l) m.-2) => [[rm2 xm2] ym2]. 
case H : (rm0%:Z ^+ 2 + ym0 ^+ 2 <= rm2%:Z ^+ 2 + ym2 ^+ 2).

move/eqP; rewrite xpair_eqE; move/andP; case.
move=> _; rewrite eq_sym; move/eqP=> //.
rewrite (surjective_pairing v).
move/eqP; rewrite xpair_eqE; move/andP; case => H1 H2.
rewrite (eqP H1) (eqP H2) //=.
exists xm0.
move : (eea_mod n l (rm0, xm0, ym0))=> Heea.

have Hin : (rm0, xm0, ym0) \in (eea n l).
rewrite -Hnth0.

(* m > 2 *)
rewrite /m /index_hd.
rewrite nth_index //. (**)


have Hhead : (head (0%N, 0%:Z, 0%:Z) (eea_sqrr n l)) \in (eea n l).
admit.


Search _ index.


(* very big mess *)
Admitted.



(*******************)


Lemma base_modn_fst n l :
let (u,v) := base n l in 
exists k, 
(u.1)%:Z + u.2 * l%:Z = k * n%:Z.
Proof.
case Hbase : (base n l)=> [u v]; set m := index_hd n l. 
case Hdiv : (l %| n).
+ move: Hbase; rewrite /base Hdiv.
move/eqP; rewrite xpair_eqE; move/andP; case => Hu Hv.
rewrite (surjective_pairing u) in Hu; rewrite (surjective_pairing v) in Hv.
move : Hu; rewrite xpair_eqE; case/andP; rewrite eq_sym; move/eqP=> -> //.
rewrite eq_sym; move/eqP=> -> //.
exists 0.
rewrite mul0r mulN1r; apply/eqP; by rewrite (subr_eq0 l%:Z l%:Z).
+ case Hnth : (nth (0%N, 0, 0) (eea n l) m.-1) => [[rm xm] ym].
have Hu1 : u = (rm, -ym).
* move : Hbase; rewrite /base Hdiv -/m !Hnth.
case Hnth0 : (nth (0%N, 0, 0) (eea n l) m) => [[rm0 xm0] ym0]. 
case Hnth2 : (nth (0%N, 0, 0) (eea n l) m.-2) => [[rm2 xm2] ym2]. 
case H : (rm0%:Z ^+ 2 + ym0 ^+ 2 <= rm2%:Z ^+ 2 + ym2 ^+ 2).
move/eqP; rewrite xpair_eqE; move/andP; case; move/eqP=> -> //.
move/eqP; rewrite xpair_eqE; move/andP; case; move/eqP=> -> //.
* exists xm.
rewrite (surjective_pairing u) in Hu1.
move/eqP : Hu1; rewrite xpair_eqE; move/andP; case => H1 H2.
rewrite (eqP H1) (eqP H2).
have Hin : (rm, xm, ym) \in (eea n l).
* rewrite -Hnth; apply: mem_nth; rewrite /m /index_hd.
set k := head _ _; move : (index_size k (eea n l)).
set a := index _ _; set b := size (eea _ _).
rewrite leq_eqVlt; move/orP; case => H.
rewrite -(eqP H) -{2}(@prednK a) ?(ltnSn a.-1) //.
by rewrite (eqP H) /b eea_size.
move: (leq_pred a)=> Ha; apply : (leq_ltn_trans Ha H).
* move: (eea_mod n l (rm, xm, ym) Hin).
move=> H; rewrite -H; congr (_ + _); by rewrite mulNr.
Qed.

Lemma base_modn_snd n l :
let (u,v) := base n l in 
exists k, 
(v.1)%:Z + v.2 * l%:Z = k * n%:Z.
Proof.
case Hbase : (base n l)=> [u v]; set m := index_hd n l. 
case Hdiv : (l %| n).
+ move: Hbase; rewrite /base Hdiv.
move/eqP; rewrite xpair_eqE; move/andP; case => Hu Hv.
rewrite (surjective_pairing u) in Hu; rewrite (surjective_pairing v) in Hv.
move : Hv; rewrite xpair_eqE; case/andP; rewrite eq_sym; move/eqP=> -> //.
rewrite eq_sym; move/eqP=> -> //.
exists 1.
by rewrite mul0r addr0 mul1r. 

+ case Hnth : (nth (0%N, 0, 0) (eea n l) m.-1) => [[rm xm] ym].
case Hnth0 : (nth (0%N, 0, 0) (eea n l) m) => [[rm0 xm0] ym0]. 
case Hnth2 : (nth (0%N, 0, 0) (eea n l) m.-2) => [[rm2 xm2] ym2]. 
case H : (rm0%:Z ^+ 2 + ym0 ^+ 2 <= rm2%:Z ^+ 2 + ym2 ^+ 2).
* move : Hbase; rewrite /base Hdiv -/m Hnth Hnth0 Hnth2 H. 
move=> Huv.
have Hv0 : v = (rm0, -ym0).
* move: Huv.
move/eqP; rewrite xpair_eqE; move/andP; case.
move=> _; rewrite eq_sym; move/eqP=> //.
* exists xm0.
rewrite (surjective_pairing v) in Hv0.
move/eqP : Hv0; rewrite xpair_eqE; move/andP; case => H1 H2.
rewrite (eqP H1) (eqP H2).

have Hin : (rm0, xm0, ym0) \in (eea n l).
(*FALSE*)
admit.

* move: (eea_mod n l (rm0, xm0, ym0) Hin).
move=> HH; rewrite -HH; congr (_ + _); by rewrite mulNr.

admit.

Qed.
(*
rewrite -Hnth0; apply: mem_nth; rewrite /m /index_hd.
set k := head _ _; move : (index_size k (eea n l)).
set a := index _ _; set b := size (eea _ _).
rewrite leq_eqVlt; move/orP; case => H.
rewrite -(eqP H) -{2}(@prednK a) ?(ltnSn a.-1) //.
by rewrite (eqP H) /b eea_size.
move: (leq_pred a)=> Ha; apply : (leq_ltn_trans Ha H).
*)



(* tests for base  *)

Eval compute in (eea 9 8).
(* [:: (1, 1, Negz 0); (8, 0, 1); (9, 1, 0)]*)
Eval compute in (eea_sqrr 9 8).
(* [:: (8, 0, 1); (9, 1, 0)] *)
Eval compute in (index_hd 9 8).
(* 1*)
Eval compute in (base 9 8).
(*(1, 1, (1, 1))*)




Eval compute in (eea 101 5).
(*[:: (1, 1, Negz 19); (5, 0, 1); (101, 1, 0)]*)
Eval compute in (eea_sqrr 101 5).
(* [:: (101, 1, 0)]*)
Eval compute in (index_hd 101 5).
(*2*)
Eval compute in (base 101 5).
(*(5, Negz 0, (1, 20))*)



Eval compute in (eea 200 101).
(*[:: (1, 50, Negz 98); (2, Negz 0, 2); (99, 1, Negz 0); 
          (101, 0, 1); (200, 1, 0)]*)
Eval compute in (eea_sqrr 200 101).
(*[:: (99, 1, Negz 0); (101, 0, 1); (200, 1, 0)]*)
Eval compute in (index_hd 200 101).
(*2*)
Eval compute in (base 200 101).
(*(2, Negz 1, (99, 1))*)



Eval compute in (eea 5 5).
(*[::  (5, 0, 1); (5, 1, 0)]*)
Eval compute in (eea_sqrr 5 5).
(*[::  (5, 0, 1); (5, 1, 0)]*)
Eval compute in (index_hd 5 5).
(*0*)
Eval compute in (base 5 5).
(*(5, Negz 0, (5, Negz 0))*)
(*  edo m == 0 k pairnei gia m-2 == 0 k m-1 == 0 *)



Eval compute in (eea 54 6).
(*[:: (6, 0, 1); (54, 1, 0)]*)
Eval compute in (index_hd 54 6).
(*1*)
Eval compute in (base 54 6).
(*(6, Negz 0, (6, Negz 0))*)
(*  edo m == 1 k pairnei gia m-2 == 0 
opote r1, x1, y1 einai to proto stoixeio me index m-1 == index 0
k r0, x0, x0 einai pali to proto me index m-1 == index 0  *)


(************************)


(*using vector_base separately *)
Definition vector_base1 (n l : nat) :=
let m := index_hd n l in 
let R := nth (0%N, 0, 0) (eea n l) m.+1 in 
((R.1).1 , - R.2).


Definition vector21 (n l : nat) := 
let m := index_hd n l in 
let R := nth (0%N, 0, 0) (eea n l) m in 
((R.1).1 , - R.2).


Definition vector22 (n l : nat) :=  
let m := index_hd n l in 
let R := nth (0%N, 0, 0) (eea n l) m.+2 in 
((R.1).1 , - R.2).

(*euclidean norm*)
Definition vector_base2 (n l : nat) :=
let a := vector21 n l in 
let b := vector22 n l in
if (a.1%:Z ^+ 2 + a.2 ^+ 2 <= b.1%:Z ^+ 2 + b.2 ^+ 2) then a 
else b.

Definition cramer1 n l k :=
let u := (vector_base1 n l) in 
let v := (vector_base2 n l) in 
let D := u.1%:Z * v.2 - u.2 * v.1%:Z in
approxZ (k * v.2) D.


Definition cramer2 n l k :=
let u := (vector_base1 n l) in 
let v := (vector_base2 n l) in 
let D := u.1%:Z * v.2 - u.2 * v.1%:Z in
approxZ (- k * u.2) D.


Definition decomposition (n l k : nat) :=
let a := cramer1 n l k in 
let b := cramer2 n l k in
let (u1, u2) := vector_base1 n l in
let (v1, v2) := vector_base2 n l in
let x := k%:Z - (a * u1%:Z + b * v1%:Z) in 
let y := - (a * u2 + b * v2) in 
(x, y).
(**********************************************************)


(* Definition f (n l : nat) (v : nat * int) :=  *)
(* (v.1 + l * v.2) %% n. *)
(*to prove that f v1 = f v2 = 0 *)
(*are the types ok ? and is the lemma in this form ok ?*)
Lemma v1_modn n l : 
let u := vector_base1 n l in 
exists m : int, (u.1)%:Z + l%:Z * u.2 == m * n%:Z.
Admitted.


Lemma linear_ind_vectors n l :
let u := vector_base1 n l in 
let v := vector_base2 n l in 
u.1%:Z * v.2 - u.2 * v.1%:Z != 0%:Z. 
Admitted.


Lemma correct_decomposition n l k :
let (x, y) := decomposition n l k in
k%:Z = x + y * l%:Z.
Admitted.

(*********************************************************)
(*********************************************************)


(*the operation in the seq of coefs*)
Definition Xk (a b : int) (q : nat) : int :=
(a - q%:Z * b).

Fixpoint seq_aux (a b : int) (qs : seq nat) :=
match qs with
|[::] => [::]
|q :: qs' => (Xk a b q) :: (seq_aux b (Xk a b q) qs')
end.

(* the seq of quotients from the EEA almost as in div *)
Fixpoint egcdn_qseq m n s qs :=
match s with
|0 => [::0%N]
|s'.+1 =>
    let: (q, r) := edivn m n in
    if r > 0 then egcdn_qseq n r s' (q :: qs) else qs
end.


Definition seqX m n :=
seq_aux 0 1 (rev (egcdn_qseq m n n [::])).

Definition seqY m n :=
seq_aux 1 0 (rev (egcdn_qseq m n n [::])).


Fixpoint egcdn_rseq m n s rs :=
match s with
|0%N => [::0%N] 
|S s' => 
  let r := m %% n in
    if r > 0 then egcdn_rseq n r s' (r :: rs) else rs
end.


Definition rseq m n := rev (egcdn_rseq m n n [::]).

(* maybe better to avoid the rev *)
Fixpoint egcdn_qseq2 m n s qs :=
match s with
|0 => [::0%N]
|s'.+1 =>
    let: (q, r) := edivn m n in
    if r > 0 then egcdn_qseq2 n r s' (qs ++ [::q]) else qs
end.


Eval compute in (seqX 120 23).
(* [:: Negz 4; 21; Negz 25; 47] *)
Eval compute in (seqY 120 23).
(* [:: 1; Negz 3; 5; Negz 8] *)
Eval compute in (egcdn_qseq 120 23 23 [::]).
(*[:: 1; 1; 4; 5]*)
Eval compute in (egcdn_qseq2 120 23 23 [::]).
(*[:: 5; 4; 1; 1]*)
Eval compute in (rseq 120 23).
(*[:: 5; 3; 2; 1]*)


(******************************)

Fixpoint invariant_N (w n k : nat) := 
let u := nat_to_bin n in 
match k with 
|0%N => 0%N
|i.+1 => (2^w * (invariant_N w n i) + (bin_to_nat (block u w i.+1)))%N 
end.



Lemma cut_block :
forall (bs : seq bool) (w : nat),
let b1 := (get_window bs w 1) in
let b2 := drop w bs in
let n := bin_to_nat bs in
((bin_to_nat b2) + 2^w * (bin_to_nat b1))%N = n.
Admitted.





Lemma decomposition n w :
let d := size (complete_zeros (nat_to_bin n) w) %/ w in 
invariant_N w n d = n. 
Admitted.


(**************** before block functions ***************)


Definition winget (u : seq bool) (w : nat) (i : nat) :=
  let s := take w (drop (w * i) u) in
    s ++ (nseq (w - size s) false).


Lemma other u w i : 
forall k : nat, nth false (winget u w i) k == nth false u (i * w + k)%N .


Definition complete_zeros (u : seq bool) (w : nat) :=
  let r := (size u)%%w in
    if (r == 0%N) then u
      else u ++ (nseq (w - r) false).

(* complete_zeros [::] w = [::] *)

Definition get_window (u : seq bool) (w : nat) (i : nat) :=
let v := complete_zeros u w in
let sz := size v in
if (sz < w * (i + 1)) then nseq w false
else
take w (drop (w * i)%N v).  

Eval compute in (get_window [:: true ; true; false; true] 3 0).
Eval compute in (get_window  [:: true ; true; false; true] 2 2).

(* get_window [::] w i = [::] *)
(* get_window starts from 1 i.e. (get_window seq 1) is the first*)


Lemma size_complete_zeros :
forall (w : nat) (u : seq bool), 
w != 0%N -> w %| size ((complete_zeros u) w).  
Proof.
move=> w u wNz.
rewrite /complete_zeros.
case szdiv : (size u %% w == 0)%N.
apply/dvdnP.
set a := size _.
set q := a %/ w.
exists q. 
move: (divn_eq a w) => lemma_useful.
have h0 : a%%w == 0%N.
rewrite /a szdiv //.
rewrite /q.
by rewrite {1}lemma_useful (eqP h0) addn0.

rewrite size_cat size_nseq.

set v := size u.
apply/dvdnP.

rewrite {1}(divn_eq v w).
exists ((v%/w) + 1)%N.
set q := v%/w.
set r := v%%w.

rewrite -addnA subnKC.
by rewrite mulnDl mul1n.

rewrite /r.
rewrite leq_eqVlt.
apply/orP; right.
by rewrite ltn_mod lt0n.

Qed.

Lemma size_window :
forall (w k : nat) (u: seq bool),
u != [::] -> k != 0%N -> size (get_window u w k) = w.
Proof.
move=> w k u uNnil kNz.
case Hw: (w == 0)%N.

rewrite (eqP Hw) /get_window take0.
apply/eqP.
rewrite size_eq0 //.

move/negbT: Hw => Hw.
rewrite /get_window size_take.
case:ltP => //.
set t := complete_zeros _ _.
rewrite size_drop.

move/ltP.
rewrite -leqNgt.
case h : (size t < w*k).

 
have Hzero : (size t - w*k = 0)%N.
apply/eqP; rewrite subn_eq0 leq_eqVlt.
apply/orP; right; by rewrite h.

rewrite Hzero subn0.

have lemma : forall a b : nat, 0 < b -> a %| b -> b <= a -> a = b.
move=> a b bNz adivb blta.
apply/eqP; rewrite eqn_leq.
apply/andP; split.
apply: dvdn_leq => //.
by rewrite blta.

have sztNz : 0 < size t.
rewrite lt0n size_eq0 /t /complete_zeros.

case szuw : (size u %% w == 0)%N => //=.
rewrite -size_eq0 size_cat addn_eq0.
apply/nandP; left; by rewrite size_eq0.

move : (size_complete_zeros w u Hw).
rewrite -/t.
move => h1 h2.
apply/eqP.
rewrite eq_sym.
apply/eqP.
apply: (lemma w (size t) sztNz) => //. 

(* (size t < w*k) = false*)
move/negbT : h.
rewrite -leqNgt.
move=> h.
rewrite subKn //.
move=> H.

have hk : k = 1%N.
move: H.
rewrite -{2}(muln1 w).
rewrite leq_pmul2l.
rewrite leq_eqVlt.
move/orP.
case.
* move/eqP => //.
* rewrite ltnS leqn0 (negbTE kNz) //.
by rewrite lt0n.

by rewrite hk muln1.
Qed.



Eval compute in (complete_zeros [::] 2).


Lemma exact_size_complete_zeros : 
forall (w : nat) (u : seq bool), 
w != 0%N -> u != [::] -> (size (complete_zeros u w) = ((size u).-1 %/ w + 1) * w)%N.
Proof.
move=> w u wNz uNnil.
rewrite /complete_zeros.
case :eqP=> Hsz.

case h_size : (size u) => [ //= | s].
* move/eqP : h_size; by rewrite size_eq0 (negbTE uNnil).

Admitted.


Lemma start_from_one : 
forall (w : nat) (u : seq bool), 
w != 0%N -> u != [::] -> 
0%N < size (complete_zeros u w) %/ w . 
Proof.
move=> w u wNz uNnil.
move : (exact_size_complete_zeros w u wNz uNnil)=> sz.

case h: (size u) => [| s].

move/eqP : h.
rewrite size_eq0 (negbTE uNnil) //.

move: sz.
rewrite h /=.

Check @ltP.

case : s h.

rewrite div0n add0n mul1n.
move=> sz_u sz_cz.
rewrite sz_cz divnn.
rewrite -lt0n in wNz.
rewrite wNz //.





Goal forall u w i, size (winget u w i) = w.
Proof.Admitted. 
(*
  move=> u w i; rewrite /winget size_cat size_take; case: ltP.
  + by rewrite size_nseq subnn addn0.
  + move=> ltw; rewrite size_drop size_nseq.
*)


Definition algo w (u v : seq bool) (P Q : point K) :=
  let C := fun i j => (P \*+ i \+ Q \*+ j) in
  let t := maxn (size u) (size v) in
  let d := ((t %/ w) + (t %% w != 0))%N in

    foldl
      (fun R i =>
        let ui := bin_to_nat (get_window u w i) in
        let vi := bin_to_nat (get_window u w i) in
        let R := R \*+ (2^w) in
          R \+ C ui vi)
      ∞ (iota 0 d).




Definition algo_before w (u v : seq bool) (P Q : point K) :=
  let C := fun i j => (P \*+ i \+ Q \*+ j) in
  let t := maxn (size u) (size v) in
  let d := ((t %/ w) + (t %% w != 0))%N in

    foldl
      (fun R i =>
        let ui := bin_to_nat (winget u w i) in
        let vi := bin_to_nat (winget u w i) in
        let R := R \*+ (2^w) in
          R \+ C ui vi)
      ∞ (iota 0 d).


Definition exp1 w (u : seq bool) (P : point K) :=
  let t := (size (complete_zeros u w)) in
  let d := (t %/ w) in
    foldl
      (fun R i =>
        let ui := bin_to_nat (get_window u w i) in
        let R := R \*+ (2^w) in
          R \+ (P \*+ i))
      ∞ (iota 0 d).

Parameter G : zmodType.


Fixpoint invariant_N (w n k : nat) := 
let u := nat_to_bin n in 
match k with 
|0%N => 0%N
|i.+1 => (2^w * (invariant_N w n i) + (bin_to_nat (get_window u w i.+1)))%N 
end.



Fixpoint R (w n k : nat) (P : G) :=
let u := nat_to_bin n in
match k with 
|0%N => 0
|i.+1 => ((R w n i P) *+ 2^w) + (P *+ (bin_to_nat (get_window u w i.+1)))
end.

(*
Lemma correct_N w n k P : 
R w n k P = P *+ (N w n k).
Proof.
elim: k => [//=|k IH].
rewrite /= IH.
set s := (bin_to_nat _).
by rewrite mulrnDr mulnC mulrnA.
Qed.
*)


Definition expG w (u : seq bool) (P : G) :=
  let t := (size (complete_zeros u w)) in
  let d := (t %/ w) in
    foldl
      (fun R i =>
        let R := R *+ (2^w) in
          R + (P *+ i))
      0 (iota 0 d).


Eval compute in (nat_to_bin 14).
(*[:: false; true; true; true]*)

Eval compute in (get_window [:: false; true; true; true] 3 1).
(*[:: true; false; false]*)

Eval compute in (get_window [:: false; true; true; true] 3 2).
(*[:: false; true; true]*)

Eval compute in (bin_to_nat [:: true; false; false]).
(*1*)

Eval compute in (bin_to_nat [:: false; true; true]).
(*6*)

Eval compute in (N 3 14 1).
Eval compute in (N 3 14 2).

(* N1 == first_block = 1
   N2 == N 3 14 2 = 2 ^3 * (N 1) + second_block = 8 + 6 = 14 *)

(* first_block from the end = get_window 1 *)
(* nat_to_bin gives the binary form starting from the LSB *)
(* N1 = first_block from the end *)
(* Nk = nat that represents k_blocks starting from the end *)





Lemma cut_block :
forall (bs : seq bool) (w : nat),
let b1 := (get_window bs w 1) in
let b2 := drop w bs in
let n := bin_to_nat bs in
((bin_to_nat b2) + 2^w * (bin_to_nat b1))%N = n.
Admitted.





Lemma decomposition n w :
let d := size (complete_zeros (nat_to_bin n) w) %/ w in 
invariant_N w n d = n. 
Admitted.




Lemma correct_exp1 u w P: 
expG w u P = P *+ (bin_to_nat u).
Proof.
  move=> /=; rewrite /expG; set d := (size _ %/ _).
  set n := (bin_to_nat _).
  have: n = N w n d. admit.
  move=> ->; rewrite {}/n.
  elim: d => [//|d IH].


Print bin_to_nat.


Print N.


Search _ foldl.
  

Lemma invariant w u P: 





Lemma decomposition_N :
forall n w : nat, 
let u := 





Lemma correct : forall (n m w : nat) (P Q : point K),
let u := (nat_to_bin n) in
let v := (nat_to_bin m) in
P \*+ n \+ Q \*+ m = algo w u v P Q. 
Proof.


(* 
*** Local Variables: ***
*** coq-load-path: ("../ssreflect" "..") ***
*** End: ***
 *)
