From Stdlib Require Import Ascii.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div.
From mathcomp Require Import choice zify boolp classical_sets functions.
Require Export HOLLight.init.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

(****************************************************************************)
(* Alignment of natural numbers *)
(****************************************************************************)

Definition IND_SUC_pred := fun f : ind -> ind => exists z : ind, (forall x1 : ind, forall x2 : ind, ((f x1) = (f x2)) = (x1 = x2)) /\ (forall x : ind, ~ ((f x) = z)).

Definition IND_SUC := ε IND_SUC_pred.

Lemma IND_SUC_def : IND_SUC = (@ε (ind -> ind) (fun f : ind -> ind => exists z : ind, (forall x1 : ind, forall x2 : ind, ((f x1) = (f x2)) = (x1 = x2)) /\ (forall x : ind, ~ ((f x) = z)))).
Proof. exact erefl. Qed.

Lemma IND_SUC_prop : IND_SUC_pred IND_SUC.
Proof.
  unfold IND_SUC. apply ε_spec.
  destruct axiom_6 as [f [h1 h2]]. exists f.
  rewrite ONTO_def in h2. rewrite <- existsNE in h2. destruct h2 as [z h2]. exists z.
  split.
  move=> x y /`. exact: h1. by move=>->.
  rewrite <- forallNE in h2. intros x e. apply (h2 x). symmetry. exact e.
Qed.

Lemma IND_SUC_inj : ONE_ONE IND_SUC.
Proof.
  generalize IND_SUC_prop. intros [z [h1 h2]]. intros x y e. rewrite <- h1.
  exact e.
Qed.

Definition IND_0_pred := fun z : ind => (forall x1 : ind, forall x2 : ind, ((IND_SUC x1) = (IND_SUC x2)) = (x1 = x2)) /\ (forall x : ind, ~ ((IND_SUC x) = z)).

Definition IND_0 := ε IND_0_pred.

Lemma IND_0_def : IND_0 = (@ε ind (fun z : ind => (forall x1 : ind, forall x2 : ind, ((IND_SUC x1) = (IND_SUC x2)) = (x1 = x2)) /\ (forall x : ind, ~ ((IND_SUC x) = z)))).
Proof. exact erefl. Qed.

Lemma IND_0_prop : IND_0_pred IND_0.
Proof.
  unfold IND_0 ; apply ε_spec ; exact: IND_SUC_prop.
Qed.

Lemma IND_SUC_neq_0 i : IND_SUC i <> IND_0.
Proof. generalize IND_0_prop. intros [h1 h2]. apply h2. Qed.

Inductive NUM_REP : ind -> Prop :=
  | NUM_REP_0 : NUM_REP IND_0
  | NUM_REP_S i : NUM_REP i -> NUM_REP (IND_SUC i).

Lemma NUM_REP_def : NUM_REP = (fun a : ind => forall NUM_REP' : ind -> Prop, (forall a' : ind, ((a' = IND_0) \/ (exists i : ind, (a' = (IND_SUC i)) /\ (NUM_REP' i))) -> NUM_REP' a') -> NUM_REP' a).
Proof. by ind_align. Qed.

Fixpoint dest_num n := match n with
  | 0 => IND_0
  | n.+1 => IND_SUC (dest_num n) end.

Definition mk_num := finv dest_num.

Lemma axiom_7 : forall (a : nat), (mk_num (dest_num a)) = a.
Proof.
  finv_inv_l ; elim=> /= [|n IHn] ; elim=> /= [|m IHm] ; first by [].
  rewrite sym. 1,2 : by move/IND_SUC_neq_0. by move/IND_SUC_inj/IHn=>->.
Qed.

Lemma axiom_8 : forall (r : ind), (NUM_REP r) = ((dest_num (mk_num r)) = r).
Proof.
  move=>r ; apply finv_inv_r=> /=.
  - by elim => {r}[| r' /[swap] -[n {r'}<-] _] ; [exists 0 | exists n.+1].
  - case => + {r}<- ; elim => [|?] ; [exact: NUM_REP_0 | exact: NUM_REP_S].
Qed.

Lemma _0_def : 0 = (mk_num IND_0).
Proof. constr_align axiom_7. Qed.

Lemma SUC_def : S = (fun _2104 : nat => mk_num (IND_SUC (dest_num _2104))).
Proof. constr_align axiom_7. Qed.

(****************************************************************************)
(* Alignment of mathematical functions on natural numbers with N. *)
(****************************************************************************)

Definition NUMERAL : nat -> nat := id.

Lemma NUMERAL_def : NUMERAL = (fun _2128 : nat => _2128).
Proof. exact erefl. Qed.

Definition BIT0 := double.

Lemma BIT0_def : BIT0 = @ε (arr nat nat) (fun y0 : nat -> nat => ((y0 (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y1 : nat, (y0 (S y1)) = (S (S (y0 y1))))).
Proof. by total_align. Qed.

Definition BIT1 n := n.*2.+1.

(* /2= in a rewrite/intro pattern *)
Ltac ssrsimpl2 := rewrite/NUMERAL/BIT0/BIT1/double/=.

Lemma BIT1_def : BIT1 = (fun _2143 : nat => S (BIT0 _2143)).
Proof. exact erefl. Qed.

Lemma PRE_def : predn = (@ε (arr (prod nat (prod nat nat)) (arr nat nat)) (fun PRE' : (prod nat (prod nat nat)) -> nat -> nat => forall _2151 : prod nat (prod nat nat), ((PRE' _2151 (NUMERAL 0)) = (NUMERAL 0)) /\ (forall n : nat, (PRE' _2151 (S n)) = n)) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))))))).
Proof. by total_align. Qed.

Lemma add_def : addn = (@ε (arr nat (arr nat (arr nat nat))) (fun add' : nat -> nat -> nat -> nat => forall _2155 : nat, (forall n : nat, (add' _2155 (NUMERAL 0) n) = n) /\ (forall m : nat, forall n : nat, (add' _2155 (S m) n) = (S (add' _2155 m n)))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))).
Proof. by total_align. Qed.

Lemma mul_def : muln = (@ε (arr nat (arr nat (arr nat nat))) (fun mul' : nat -> nat -> nat -> nat => forall _2186 : nat, (forall n : nat, (mul' _2186 (NUMERAL 0) n) = (NUMERAL 0)) /\ (forall m : nat, forall n : nat, (mul' _2186 (S m) n) = (addn (mul' _2186 m n) n))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))).
Proof. by total_align => // * ; rewrite addnC. Qed.

Lemma EXP_def : expn = (@ε (arr (prod nat (prod nat nat)) (arr nat (arr nat nat))) (fun EXP' : (prod nat (prod nat nat)) -> nat -> nat -> nat => forall _2224 : prod nat (prod nat nat), (forall m : nat, EXP' _2224 m (NUMERAL 0) = NUMERAL (BIT1 0)) /\ (forall m : nat, forall n : nat, (EXP' _2224 m (S n)) = (muln m (EXP' _2224 m n)))) (@pair nat (prod nat nat) (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))) (@pair nat nat (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 0))))))) (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))).
Proof. total_align=> // ; exact: expnS. Qed.

Definition leqn : nat -> nat -> Prop := leq.
Definition geqn (n m : nat) : Prop := n >= m.
Definition ltn (n m : nat) : Prop := n < m.
Definition gtn (n m : nat) : Prop := n > m.

Lemma le_def : leqn = (@ε (arr (prod nat nat) (arr nat (arr nat Prop))) (fun le' : (prod nat nat) -> nat -> nat -> Prop => forall _2241 : prod nat nat, (forall m : nat, (le' _2241 m (NUMERAL 0)) = (m = (NUMERAL 0))) /\ (forall m : nat, forall n : nat, (le' _2241 m (S n)) = ((m = (S n)) \/ (le' _2241 m n)))) (@pair nat nat (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 0))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 0))))))))).
Proof.
  total_align => [m|n m] ; rewrite/leqn 2!eqP** ; first by case m.
  rewrite orP** ; move:m ; elim:n=>[|n IHn] m ; first by case m.
  by case:m=>* ; [case n | rewrite 2!ltnS].
Qed.

Lemma lt_def : ltn = (@ε (arr nat (arr nat (arr nat Prop))) (fun lt : nat -> nat -> nat -> Prop => forall _2248 : nat, (forall m : nat, (lt _2248 m (NUMERAL 0)) = False) /\ (forall m : nat, forall n : nat, (lt _2248 m (S n)) = ((m = n) \/ (lt _2248 m n)))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 0)))))))).
Proof.
  total_align => [? | n m] ; rewrite/ltn ?eqP** ; first by rewrite ltn0 falseE.
  rewrite orP** ; move:m ; elim:n=>[|n IHn] m ; first by case m.
  by case:m=>[|m] ; [case n | rewrite ltnS eqSS (@ltnS n.+1)].
Qed.

Lemma ge_def : geqn = (fun _2249 : nat => fun _2250 : nat => leqn _2250 _2249).
Proof. by []. Qed.

Lemma gt_def : gtn = (fun _2261 : nat => fun _2262 : nat => ltn _2262 _2261).
Proof. by []. Qed.

Lemma MAX_def : maxn = (fun _2273 : nat => fun _2274 : nat => @COND nat (leqn _2273 _2274) _2274 _2273).
Proof.
  by rewrite/leqn => /` n m ; case (ltngtP n m) => /1=.
Qed.

Lemma MIN_def : minn = (fun _2285 : nat => fun _2286 : nat => @COND nat (leqn _2285 _2286) _2285 _2286).
Proof.
  by rewrite/leqn => /` n m ; case (ltngtP n m) => /1=.
Qed.

Lemma minus_def : subn = (@ε (arr nat (arr nat (arr nat nat))) (fun pair' : nat -> nat -> nat -> nat => forall _2766 : nat, (forall m : nat, (pair' _2766 m (NUMERAL 0)) = m) /\ (forall m : nat, forall n : nat, (pair' _2766 m (S n)) = (predn (pair' _2766 m n)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))).
Proof.
  total_align =>* ; [exact: subn0 | exact: subnS].
Qed.

Lemma FACT_def : factorial = @ε ((prod nat (prod nat (prod nat nat))) -> nat -> nat) (fun FACT' : (prod nat (prod nat (prod nat nat))) -> nat -> nat => forall _2944 : prod nat (prod nat (prod nat nat)), ((FACT' _2944 (NUMERAL 0%num)) = (NUMERAL (BIT1 0%num))) /\ (forall n : nat, (FACT' _2944 (S n)) = (muln (S n) (FACT' _2944 n)))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0%num)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0%num)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0%num)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0%num))))))))))).
Proof. by total_align. Qed.

Lemma DIV_def : divn = (@ε (arr (prod nat (prod nat nat)) (arr nat (arr nat nat))) (fun q : (prod nat (prod nat nat)) -> nat -> nat -> nat => forall _3086 : prod nat (prod nat nat), exists r : nat -> nat -> nat, forall m : nat, forall n : nat, @COND Prop (n = (NUMERAL 0)) (((q _3086 m n) = (NUMERAL 0)) /\ ((r m n) = m)) ((m = (addn (muln (q _3086 m n) n) (r m n))) /\ (ltn (r m n) n))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))))))).
Proof.
  rewrite/ltn. align_ε.
  - exists modn=>n m /c` [->|]; first by split; [exact: divn0 | exact: modn0].
    rewrite eqP** negP** -lt0n ; split ; [exact:divn_eq | exact:ltn_pmod].
  - move=> div _ [rem div_def] ; ext=> m n ; specialize (div_def m n).
    eapply if_elim with (1 := div_def) ; first (move=>->[-> _] ; exact: divn0).
    move=> ? [{2}-> ?]; rewrite divnMDl ; last by rewrite lt0n -negP** -eqP**.
    by rewrite divn_small -?andP** ?addn0.
Qed. 

Lemma MOD_def : modn = (@ε (arr (prod nat (prod nat nat)) (arr nat (arr nat nat))) (fun r : (prod nat (prod nat nat)) -> nat -> nat -> nat => forall _3087 : prod nat (prod nat nat), forall m : nat, forall n : nat, @COND Prop (n = (NUMERAL 0)) (((divn m n) = (NUMERAL 0)) /\ ((r _3087 m n) = m)) ((m = (addn (muln (divn m n) n) (r _3087 m n))) /\ (ltn (r _3087 m n) n))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))))))).
Proof.
  rewrite/ltn. align_ε.
  - move=> n m /c` [->|]; first by split; [exact: divn0 | exact: modn0].
    rewrite eqP** negP** -lt0n ; split ; [exact:divn_eq | exact:ltn_pmod].
  - move=> rem _ rem_def ; ext => n m ; specialize (rem_def n m).
    eapply if_elim with (1 := rem_def) ; first(move=>->[_ ->]; exact:modn0).
    by move => ? [{2}-> ?] ; rewrite modnMDl modn_small.
Qed.

(****************************************************************************)
(* Alignment of the Even and Odd predicates. *)
(****************************************************************************)

Definition even n : Prop := ~~ odd n.
Definition oddn : nat -> Prop := odd.

Lemma EVEN_def : even = @ε ((prod nat (prod nat (prod nat nat))) -> nat -> Prop) (fun EVEN' : (prod nat (prod nat (prod nat nat))) -> nat -> Prop => forall _2603 : prod nat (prod nat (prod nat nat)), ((EVEN' _2603 (NUMERAL 0%num)) = True) /\ (forall n : nat, (EVEN' _2603 (S n)) = (~ (EVEN' _2603 n)))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0%num)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0%num)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0%num)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0%num))))))))))).
Proof.
  by total_align=> * ; [rewrite is_True | rewrite/even negP**].
Qed.

Lemma ODD_def: oddn = @ε ((prod nat (prod nat nat)) -> nat -> Prop) (fun ODD' : (prod nat (prod nat nat)) -> nat -> Prop => forall _2607 : prod nat (prod nat nat), ((ODD' _2607 (NUMERAL 0%num)) = False) /\ (forall n : nat, (ODD' _2607 (S n)) = (~ (ODD' _2607 n)))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0%num)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0%num)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0%num)))))))))).
Proof.
  by total_align=> * ; [rewrite is_False | rewrite/oddn negP**].
Qed.

(****************************************************************************)
(* NUMPAIR(x,y) = 2^x(2y+1): bijection between nat² and nat-{0}. *)
(****************************************************************************)

Definition NUMPAIR := fun x : nat => fun y : nat => muln (expn (NUMERAL (BIT0 (BIT1 0))) x) (addn (muln (NUMERAL (BIT0 (BIT1 0))) y) (NUMERAL (BIT1 0))).

Lemma NUMPAIR_def : NUMPAIR = (fun _17487 : nat => fun _17488 : nat => muln (expn (NUMERAL (BIT0 (BIT1 0))) _17487) (addn (muln (NUMERAL (BIT0 (BIT1 0))) _17488) (NUMERAL (BIT1 0)))).
Proof. exact erefl. Qed.

Lemma mulnI (n : nat) : n != 0 -> injective (muln n).
Proof.
  move=> /negbTE neqn0 ; elim => [|k IHk] m.
  - by rewrite muln0 sym eqP** muln_eq0 neqn0 /= -eqP** => ->.
  - case:m=>[|m] ; first by rewrite muln0 eqP** muln_eq0 neqn0 /= -eqP** => ->.
    rewrite 2!mulnS => /addnI eqkm ; f_equal ; exact:IHk.
Qed.

Lemma uniq_decomp_pow_ndvd (p : nat) : p != 0 -> forall n k n' k',
  ~~(p %| k) -> ~~(p %| k') -> p^n * k == p^n' * k' -> (n == n') && (k == k').
Proof.
  move=> neqp0 ; elim =>[|n IHn] k n' k' ndvdpk ndvdpk'.
  - case:n'=>[|n'] ; first by rewrite expn0 2!mul1n.
    rewrite expn0 expnS mul1n ; move:ndvdpk =>/[swap] /eqP -> contra.
    contradict contra=>/negP; apply; do 2 apply: dvdn_mulr; exact: dvdnn.
  - case:n'=>[|n'].
    + rewrite expn0 expnS mul1n eq_sym ; move:ndvdpk' =>/[swap] /eqP -> contra.
      contradict contra=>/negP; apply; do 2 apply: dvdn_mulr; exact: dvdnn.
    + rewrite 2!expnS -2!mulnA eqSS => /eqP/(mulnI neqp0)/eqP ?; exact:IHn.
Qed.

Lemma negnegbE b : ~~ ~~ b = b.
Proof. by case b. Qed.

Lemma odd_add2n1 (n : nat) : odd (2 * n + 1).
Proof.
  by elim:n=>[|n] ; last rewrite/odd mulnS ?addSn ?addnS addn0 negnegbE.
Qed.

Lemma NUMPAIR_INJ : forall x1 : nat, forall y1 : nat, forall x2 : nat, forall y2 : nat, ((NUMPAIR x1 y1) = (NUMPAIR x2 y2)) = ((x1 = x2) /\ (y1 = y2)).
Proof.
  move=> n m n' m' /` ; last by move=>-[-> ->].
  rewrite/NUMPAIR/2= => /eqP/uniq_decomp_pow_ndvd /[spec by []].
  rewrite 2!dvdn2 2!negnegbE => /[spec odd_add2n1 m | odd_add2n1 m'].
  by move/andP => -[/eqP ? /eqP/addIn/mulnI] /[spec by []].
Qed.

Lemma andb_sym : symmetric andb.
Proof. by do 2 case. Qed.

Lemma NUMPAIR_nonzero x y : NUMPAIR x y <> 0.
Proof.
  by rewrite/NUMPAIR/2= =>/eqP; rewrite muln_eq0 addn_eq0 expn_eq0 /= andb_sym.
Qed.

(****************************************************************************)
(* Inverse of NUMPAIR. *)
(****************************************************************************)

(* used for some embeddings in the definition of recspace *)

Lemma INJ_INVERSE2 {A B C : Type'} : forall P : A -> B -> C, (forall x1 : A, forall y1 : B, forall x2 : A, forall y2 : B, ((P x1 y1) = (P x2 y2)) = ((x1 = x2) /\ (y1 = y2))) -> exists X : C -> A, exists Y : C -> B, forall x : A, forall y : B, ((X (P x y)) = x) /\ ((Y (P x y)) = y).
Proof.
  intros f h.
  exists (fun c => ε (fun a => exists b, f a b = c)).
  exists (fun c => ε (fun b => exists a, f a b = c)).
  intros a b. split.
  match goal with [|- ε ?x = _] => set (Q := x); set (q := ε Q) end.
  assert (i : exists a, Q a). exists a. exists b. reflexivity.
  generalize (ε_spec i). fold q. unfold Q. intros [b' j]. rewrite h in j.
  destruct j as [j1 j2]. auto.
  match goal with [|- ε ?x = _] => set (Q := x); set (q := ε Q) end.
  assert (i : exists b, Q b). exists b. exists a. reflexivity.
  generalize (ε_spec i). fold q. unfold Q. intros [a' j]. rewrite h in j.
  destruct j as [j1 j2]. auto.
Qed.

Definition NUMFST0_pred :=  fun X : nat -> nat => exists Y : nat -> nat, forall x : nat, forall y : nat, ((X (NUMPAIR x y)) = x) /\ ((Y (NUMPAIR x y)) = y).

Definition NUMFST0 := ε NUMFST0_pred.

Lemma NUMFST0_NUMPAIR x y : NUMFST0 (NUMPAIR x y) = x.
Proof.
  destruct (INJ_INVERSE2 NUMPAIR_INJ) as [fst [snd h]].
  assert (i : exists q, NUMFST0_pred q). exists fst. exists snd. assumption.
  generalize (ε_spec i). fold NUMFST0. unfold NUMFST0_pred.
  intros [snd' h']. destruct (h' x y) as [j k]. assumption.
Qed.

Definition NUMSND0_pred :=  fun Y : nat -> nat => exists X : nat -> nat, forall x : nat, forall y : nat, ((X (NUMPAIR x y)) = x) /\ ((Y (NUMPAIR x y)) = y).

Definition NUMSND0 := ε NUMSND0_pred.

Lemma NUMSND0_NUMPAIR x y : NUMSND0 (NUMPAIR x y) = y.
Proof.
  destruct (INJ_INVERSE2 NUMPAIR_INJ) as [fst [snd h]].
  assert (i : exists x, NUMSND0_pred x). exists snd. exists fst. assumption.
  generalize (ε_spec i). fold NUMSND0. unfold NUMSND0_pred.
  intros [fst' h']. destruct (h' x y) as [j k]. assumption.
Qed.

Definition NUMFST := @ε ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> nat -> nat) (fun X : (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> nat -> nat => forall _17340 : prod nat (prod nat (prod nat (prod nat (prod nat nat)))), exists Y : nat -> nat, forall x : nat, forall y : nat, ((X _17340 (NUMPAIR x y)) = x) /\ ((Y (NUMPAIR x y)) = y)) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))))))))).

Lemma NUMFST_def : NUMFST = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> nat -> nat) (fun X : (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> nat -> nat => forall _17503 : prod nat (prod nat (prod nat (prod nat (prod nat nat)))), exists Y : nat -> nat, forall x : nat, forall y : nat, ((X _17503 (NUMPAIR x y)) = x) /\ ((Y (NUMPAIR x y)) = y)) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))))).
Proof. exact erefl. Qed.

Lemma NUMFST_NUMPAIR x y : NUMFST (NUMPAIR x y) = x.
Proof.
  rewrite/NUMFST/2= ; generalize (78, (85, (77, (70, (83, 84))))).
  generalize (nat * (nat * (nat * (nat * (nat * nat)))))%type => A a.
  match goal with |- ε ?x _ _ = _ => set (Q := x); set (fst := ε Q) end.
  assert (i: exists x, Q x). exists (fun _ => NUMFST0). unfold Q. intros _. exists NUMSND0.
  intros x' y'. rewrite NUMFST0_NUMPAIR NUMSND0_NUMPAIR. auto.
  generalize (ε_spec i). change (Q fst -> fst a (NUMPAIR x y) = x). intro h.
  destruct (h a) as [snd j]. destruct (j x y) as [j1 j2]. exact j1.
Qed.

Definition NUMSND1_pred :=  fun Y : nat -> nat => forall x : nat, forall y : nat, ((NUMFST (NUMPAIR x y)) = x) /\ ((Y (NUMPAIR x y)) = y).

Definition NUMSND1 := ε NUMSND1_pred.

Lemma NUMSND1_NUMPAIR x y : NUMSND1 (NUMPAIR x y) = y.
Proof.
  destruct (INJ_INVERSE2 NUMPAIR_INJ) as [fst [snd h]].
  assert (i : exists x, NUMSND1_pred x). exists snd. unfold NUMSND1_pred.
  intros x' y'. rewrite NUMFST_NUMPAIR. destruct (h x' y') as [h1 h2]. auto.
  generalize (ε_spec i). fold NUMSND1. unfold NUMSND1_pred. intro j.
  destruct (j x y) as [j1 j2]. exact j2.
Qed.

Definition NUMSND := @ε ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> nat -> nat) (fun Y : (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> nat -> nat => forall _17341 : prod nat (prod nat (prod nat (prod nat (prod nat nat)))), forall x : nat, forall y : nat, ((NUMFST (NUMPAIR x y)) = x) /\ ((Y _17341 (NUMPAIR x y)) = y)) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))))))))).

Lemma NUMSND_def : NUMSND = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> nat -> nat) (fun Y : (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> nat -> nat => forall _17504 : prod nat (prod nat (prod nat (prod nat (prod nat nat)))), forall x : nat, forall y : nat, ((NUMFST (NUMPAIR x y)) = x) /\ ((Y _17504 (NUMPAIR x y)) = y)) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))))))).
Proof. exact erefl. Qed.

Lemma NUMSND_NUMPAIR x y : NUMSND (NUMPAIR x y) = y.
Proof.
  rewrite/NUMSND/2= ; generalize (78, (85, (77, (83, (78, 68))))).
  generalize (prod nat (prod nat (prod nat (prod nat (prod nat nat))))); intros A a.
  match goal with |- ε ?x _ _ = _ => set (Q := x); set (snd := ε Q) end.
  assert (i: exists x, Q x). exists (fun _ => NUMSND1). unfold Q. intros _.
  intros x' y'. rewrite NUMFST_NUMPAIR NUMSND1_NUMPAIR. auto.
  generalize (ε_spec i). change (Q snd -> snd a (NUMPAIR x y) = y). intro h.
  destruct (h a x y) as [h1 h2]. exact h2.
Qed.

(****************************************************************************)
(* NUMSUM(b,n) = if b then 2n+1 else 2n : bijection between BxN and N. *)
(****************************************************************************)

(* used for some embeddings in the definition of recspace *)

Definition NUMSUM := fun b : Prop => fun n : nat => @COND nat b (S (muln (NUMERAL (BIT0 (BIT1 0))) n)) (muln (NUMERAL (BIT0 (BIT1 0))) n).

Lemma NUMSUM_def : NUMSUM = (fun _17505 : Prop => fun _17506 : nat => @COND nat _17505 (S (muln (NUMERAL (BIT0 (BIT1 0))) _17506)) (muln (NUMERAL (BIT0 (BIT1 0))) _17506)).
Proof. exact erefl. Qed.

Definition NUMLEFT n : Prop := odd n.

Definition NUMRIGHT n := (n - odd n) %/ 2.

Lemma NUMLEFT_NUMSUM b n : NUMLEFT (NUMSUM b n) = b.
Proof.
  rewrite/NUMLEFT/NUMSUM/2= => /c` H.
  - is_True H ; rewrite is_True -addn1 ; exact: odd_add2n1.
  - by is_False H ; rewrite is_False negP** mul2n odd_double.
Qed.

Lemma NUMRIGHT_NUMSUM b n : NUMRIGHT (NUMSUM b n) = n.
Proof.
  rewrite/NUMSUM/NUMRIGHT/2= => /c` H.
  - by rewrite -addn1 odd_add2n1 addnK mulKn.
  - by rewrite mul2n odd_double subn0 -mul2n mulKn.
Qed.

Lemma odd_predn (n : nat) : odd n -> odd n.-1 = false.
Proof.
  case:n=>[|n]; [by [] | rewrite succnK /= ; exact: negbTE].
Qed.

Lemma NUMSUM_surjective n : exists b x, n = NUMSUM b x.
Proof.
  exist (NUMLEFT n) (NUMRIGHT n) ; rewrite/NUMSUM/NUMLEFT/NUMRIGHT/2= => /c`.
  - move/[dup]=>oddn->;rewrite muln_divA;last by rewrite dvdn2 subn1 odd_predn.
    rewrite mulKn // subn1 prednK // ; exact: odd_gt0.
  - move/negP/negbTE/[dup]=> evenn -> ; rewrite subn0.
    by rewrite muln_divA ; [rewrite mulKn | rewrite dvdn2 evenn].
Qed.

Lemma NUMLEFT_def : NUMLEFT = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> nat -> Prop) (fun X : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> nat -> Prop => forall _17372 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))), exists Y : nat -> nat, forall x : Prop, forall y : nat, ((X _17372 (NUMSUM x y)) = x) /\ ((Y (NUMSUM x y)) = y)) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))))))))))).
Proof.
  cbn.
  align_ε.
  - exists NUMRIGHT.
    intros x y.
    split.
    + exact (NUMLEFT_NUMSUM x y).
    + exact (NUMRIGHT_NUMSUM x y).
  - intros NUMLEFT' _ h.
    destruct h as [NUMRIGHT' h].
    ext 1=>s.
    destruct (NUMSUM_surjective s) as [b [x k]].
    rewrite k (NUMLEFT_NUMSUM b x) (proj1 (h b x)).
    reflexivity.
Qed.

Lemma NUMRIGHT_def : NUMRIGHT = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> nat -> nat) (fun Y : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> nat -> nat => forall _17373 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))), forall x : Prop, forall y : nat, ((NUMLEFT (NUMSUM x y)) = x) /\ ((Y _17373 (NUMSUM x y)) = y)) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))))))).
Proof.
  cbn.
  align_ε.
  - split.
    + exact (NUMLEFT_NUMSUM x y).
    + exact (NUMRIGHT_NUMSUM x y).
  - intros NUMRIGHT' _ h.
    ext =>s.
    destruct (NUMSUM_surjective s) as [b [x k]].
    rewrite k (NUMRIGHT_NUMSUM b x) (proj2 (h b x)).
    reflexivity.
Qed.

(****************************************************************************)
(* Alignment of well-foundedness.
HOL Light: non-empty subsets has minimal, Rocq: has induction *)
(****************************************************************************)

Definition well_founded := Corelib.Init.Wf.well_founded.

Lemma WF_def {A : Type'} : (@well_founded A) = (fun _6923 : A -> A -> Prop => forall P : A -> Prop, (exists x : A, P x) -> exists x : A, (P x) /\ (forall y : A, (_6923 y x) -> ~ (P y))).
Proof.
  ext => R H.
  - intros X ne.
    destruct ne as [x Hx].
    rewrite <- (notE _); intro goal.
    case (prop_degen (forall y: A, ~ X y)); intro h.
    + rewrite is_True in h.
      assert (~ X x) by exact (h x).
      contradiction.
    + rewrite is_False in h.
      apply h.
      apply (well_founded_induction H).
      intros y g Xy.
      apply goal.
      exists y.
      split; assumption.
  - unfold well_founded.
    case (prop_degen (forall a : A, Acc R a)); intro h.
    + rewrite is_True in h.
      assumption.
    + rewrite -> is_False, <- existsNE in h.
      apply except.
      assert (G: exists x : A, ~ Acc R x /\ (forall y : A, R y x -> ~ ~ Acc R y))
        by apply (H _ h).
      destruct G as [x Gx].
      destruct Gx as [H0 H1].
      apply H0.
      apply Acc_intro.
      intros y Ryx.
      rewrite <- (notE _).
      apply H1.
      assumption.
Qed.

(****************************************************************************)
(* Alignment of  measures, that is functions A -> nat which creates a wf order by inverse image *)
(****************************************************************************)

(*Definition MEASURE {A : Type'} : (A -> nat) -> A -> A -> Prop := fun f : A -> nat => @Wf_nat.gtof A (fun x : A => N.to_nat (f x)).

Lemma MEASURE_def {A : Type'} : (fun f : A -> nat => @Wf_nat.gtof A (fun x : A => N.to_nat (f x))) = (fun _8094 : A -> nat => fun x : A => fun y : A => ltn (_8094 x) (_8094 y)).
Proof.
  apply fun_ext; intro f.
  unfold Wf_nat.gtof, MEASURE.
  ext x y.
  exact (inj_lt _ _).
Qed.*)

(****************************************************************************)
(* Alignment of recspace, the HOL-Light type used to encode inductive types. *)
(****************************************************************************)

(* recspace is basically an inductive type with one constant constructor BOTTOM
   and one recursive constructor CONSTR : nat -> A -> (nat -> recspace A) -> recspace A,
   defined through an embedding inside M := nat -> A -> Prop.
   INJN, INJA and INJF embed nat, A and nat -> M inside M,
   which, together with INJP embedding M*M inside M, allows to embed 
   nat * A * (nat -> M). *)

Definition INJN {A : Type'} := fun x : nat => fun n : nat => fun a : A => n = x.

Lemma INJN_def {A : Type'} : (@INJN A) = (fun _17537 : nat => fun n : nat => fun a : A => n = _17537).
Proof. exact erefl. Qed.

Definition INJA {A : Type'} := fun x : A => fun n : nat => fun b : A => b = x.

Lemma INJA_def {A : Type'} : (@INJA A) = (fun _17542 : A => fun n : nat => fun b : A => b = _17542).
Proof. exact erefl. Qed.

Definition INJF {A : Type'} := fun f : nat -> nat -> A -> Prop => fun n : nat => f (NUMFST n) (NUMSND n).

Lemma INJF_def {A : Type'} : (@INJF A) = (fun _17549 : nat -> nat -> A -> Prop => fun n : nat => _17549 (NUMFST n) (NUMSND n)).
Proof. exact erefl. Qed.

Definition INJP {A : Type'} := fun f : nat -> A -> Prop => fun g : nat -> A -> Prop => fun n : nat => fun a : A => @COND Prop (NUMLEFT n) (f (NUMRIGHT n) a) (g (NUMRIGHT n) a).

Lemma INJP_def {A : Type'} : (@INJP A) = (fun _17554 : nat -> A -> Prop => fun _17555 : nat -> A -> Prop => fun n : nat => fun a : A => @COND Prop (NUMLEFT n) (_17554 (NUMRIGHT n) a) (_17555 (NUMRIGHT n) a)).
Proof. exact erefl. Qed.

Definition ZCONSTR {A : Type'} := fun n : nat => fun a : A => fun f : nat -> nat -> A -> Prop => @INJP A (@INJN A (S n)) (@INJP A (@INJA A a) (@INJF A f)).

Lemma ZCONSTR_def {A : Type'} : (@ZCONSTR A) = (fun _17566 : nat => fun _17567 : A => fun _17568 : nat -> nat -> A -> Prop => @INJP A (@INJN A (S _17566)) (@INJP A (@INJA A _17567) (@INJF A _17568))).
Proof. exact erefl. Qed.

Definition ZBOT {A : Type'} := @INJP A (@INJN A (NUMERAL 0)) (@ε (nat -> A -> Prop) (fun z : nat -> A -> Prop => True)).

Lemma ZBOT_def {A : Type'} : (@ZBOT A) = (@INJP A (@INJN A (NUMERAL 0)) (@ε (nat -> A -> Prop) (fun z : nat -> A -> Prop => True))).
Proof. exact erefl. Qed.

Inductive ZRECSPACE {A : Type'} : (nat -> A -> Prop) -> Prop :=
| ZRECSPACE0 : ZRECSPACE ZBOT
| ZRECSPACE1 c i r : (forall n, ZRECSPACE (r n)) -> ZRECSPACE (ZCONSTR c i r).

Lemma ZRECSPACE_def {A : Type'} : (@ZRECSPACE A) = (fun a : nat -> A -> Prop => forall ZRECSPACE' : (nat -> A -> Prop) -> Prop, (forall a' : nat -> A -> Prop, ((a' = (@ZBOT A)) \/ (exists c : nat, exists i : A, exists r : nat -> nat -> A -> Prop, (a' = (@ZCONSTR A c i r)) /\ (forall n : nat, ZRECSPACE' (r n)))) -> ZRECSPACE' a') -> ZRECSPACE' a).
Proof. by ind_align. Qed.

Inductive recspace (A : Type) :=
| BOTTOM : recspace A
| CONSTR : nat -> A -> (nat -> recspace A) -> recspace A.

Arguments CONSTR [A] _ _ _.
Arguments BOTTOM {A}.

HB.instance Definition _ A := is_Type' (@BOTTOM A).

(* Explanations. *)

(* Suppose you wish to mutually define inductive types B1 ... Bn.

   - A is the product of the types of all external arguments in constructors of B1 ... Bn.
     ( Without waste, if two constructors use an argument of the same type, it won't appear twice in A. )
     ( Any argument not appearing in a constructor will be replaced by (ε (fun => True)). )
     ( If no constructor has external arguments then A is Prop by default, with only (ε (fun => True))
       appearing. )

   - nat -> recspace A will contain all recursive arguments by emulating lists.
     ( Fnil and FCONS defined below emulate [::] and cons. )
     ( Recursive arguments need to be either directly of type B_i for some i or of type T B_i where
       T is an already defined inductive type. In this case, HOL_Light adds another type
       to the mutual definition, TB_i (isomorphic to T B_i), maps T B_i to TB_i and then uses this mapping
       to define the actual constructors with arguments in T B_i. )

   - The first integer argument of CONSTR is used to index constructors.
     ( The first one defined will be assigned 0, the second 1, etc. )
 *)

(* Example of the definition of seq A :
  - Defined with recspace A (for the one external argument in cons).
  - [::] is the first constructor, so [::] = CONSTR 0 (ε (fun _ => True)) Fnil.
  - cons is the second one, so cons a l = CONSTR 1 a (FCONS l Fnil). *)

Definition Fnil {A : Type} : nat -> recspace A := fun _ => BOTTOM.

Notation "[ ]_rec" := Fnil (format "[ ]_rec").
Notation "[ x ]_rec" := (FCONS x Fnil).
Notation "[ x ; y ; .. ; z ]_rec" := (FCONS x (FCONS y .. (FCONS z Fnil) ..))
  (format "[ '[' x ; '/' y ; '/' .. ; '/' z ']' ]_rec").

Lemma FCONS_def {A : Type'} : @FCONS A = @ε ((prod nat (prod nat (prod nat (prod nat nat)))) -> A -> (nat -> A) -> nat -> A) (fun FCONS' : (prod nat (prod nat (prod nat (prod nat nat)))) -> A -> (nat -> A) -> nat -> A => forall _17460 : prod nat (prod nat (prod nat (prod nat nat))), (forall a : A, forall f : nat -> A, (FCONS' _17460 a f (NUMERAL 0)) = a) /\ (forall a : A, forall f : nat -> A, forall n : nat, (FCONS' _17460 a f (S n)) = (f n))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))).
Proof. by total_align. Qed.

Fixpoint _dest_rec {A : Type'} (r : recspace A) : nat -> A -> Prop :=
  match r with
  | BOTTOM => ZBOT
  | CONSTR n a f => ZCONSTR n a (fun m => _dest_rec (f m)) end.

Definition _mk_rec {A : Type'} : (nat -> A -> Prop) -> recspace A := finv _dest_rec.

Lemma axiom_10 : forall {A : Type'} (P : nat -> A -> Prop), (@ZRECSPACE A P) = ((@_dest_rec A (@_mk_rec A P)) = P).
Proof.
  intros A P. apply finv_inv_r.
  - induction 1.
    + now exists BOTTOM.
    + exists (CONSTR c i (fun n => _mk_rec (r n))). simpl. f_equal. 
      ext 1 =>n. exact (ε_spec (H0 n)).
  - intros (r , <-). induction r ; now constructor.
Qed.

(* For axiom_9 we need to prove injectivity of _dest_rec, which requires to prove 
   injectivity of every embedding involved  *)
Lemma NUMSUM_INJ : forall b1 : Prop, forall x1 : nat, forall b2 : Prop, forall x2 : nat, ((NUMSUM b1 x1) = (NUMSUM b2 x2)) = ((b1 = b2) /\ (x1 = x2)).
Proof.
  rewrite/NUMSUM/2= => P n Q m /c` /c`.
  1,3: rewrite -{1}(is_True Q)=> ->. 3,4: rewrite -{1}is_False=> ->.
  1,3: rewrite -{1}(is_True P)=> ->. 3,4: rewrite -{1}is_False=> ->.
  all: ext. 2,8: by case=>_ ->.
  - by move/succn_inj=> ? ; split ; last apply (@mulnI 2).
  - move=> contra; have: 2 %| (2 * n).+1 by rewrite contra dvdn_mulr.
    by rewrite dvdn2 /= -dvdn2 dvdn_mulr.
  - by case=>contra ; contradict contra=> <-.
  - move=> contra; have: 2 %| (2 * m).+1 by rewrite -contra dvdn_mulr.
    by rewrite dvdn2 /= -dvdn2 dvdn_mulr.
  - by case=>contra ; contradict contra=> ->.
  - by move=> ? ; split ; last apply (@mulnI 2).
Qed.

Lemma INJN_INJ {A : Type'} : forall n1 : nat, forall n2 : nat, ((@INJN A n1) = (@INJN A n2)) = (n1 = n2).
Proof.
  by rewrite/INJN=> * /1` [/[gen]equal_eq|->] // ; rewrite -(equal_eq _ point).
Qed.

Lemma INJA_INJ {A : Type'} : forall a1 : A, forall a2 : A, ((@INJA A a1) = (@INJA A a2)) = (a1 = a2).
Proof.
  by rewrite/INJA=> * /1` [/[gen]equal_eq|->] // ; rewrite -(equal_eq 0).
Qed.

Lemma INJF_INJ {A : Type'} : forall f1 : nat -> nat -> A -> Prop, forall f2 : nat -> nat -> A -> Prop, ((@INJF A f1) = (@INJF A f2)) = (f1 = f2).
Proof.
  rewrite/INJF => f g /1` [/[gen]? /f` n m ? |->] ; last by [].
  by rewrite -(NUMFST_NUMPAIR n m)-{2 4}(NUMSND_NUMPAIR n m).
Qed.

Lemma INJP_INJ {A : Type'} : forall f1 : nat -> A -> Prop, forall f1' : nat -> A -> Prop, forall f2 : nat -> A -> Prop, forall f2' : nat -> A -> Prop, ((@INJP A f1 f2) = (@INJP A f1' f2')) = ((f1 = f1') /\ (f2 = f2')).
Proof.
  rewrite/INJP => P P' Q Q' /1` ; last by case=>-> ->.
  move=>temp ; split => /f` n a ; move:temp=>/[gen].
  move/[spec NUMSUM True n | a]. 2: move/[spec NUMSUM False n | a].
  1,2: by rewrite NUMLEFT_NUMSUM NUMRIGHT_NUMSUM /1=.
Qed.

Lemma _dest_rec_inj {A : Type'} : 
  forall (r r' : recspace A), _dest_rec r = _dest_rec r' -> r = r'.
Proof.
  elim=>[|n r recs IHr]; elim=>[|n' r' recs' IHr'] ; rewrite/=/ZBOT/ZCONSTR.
  all: rewrite INJP_INJ INJN_INJ // =>-[].
  1,2: inversion 1.
  rewrite INJP_INJ INJF_INJ INJA_INJ=> [= ->] [->] /gen_fun1 rec_eq ; f_equal.
  move=> /1` ? ; exact: IHr.
Qed.

Lemma axiom_9 : forall {A : Type'} (a : recspace A), (@_mk_rec A (@_dest_rec A a)) = a.
Proof.
  intros A a. apply finv_inv_l. exact _dest_rec_inj.
Qed.

Lemma BOTTOM_def {A : Type'} : (@BOTTOM A) = (@_mk_rec A (@ZBOT A)).
Proof. constr_align (@axiom_9 A). Qed.

Lemma CONSTR_def {A : Type'} : (@CONSTR A) = (fun _17591 : nat => fun _17592 : A => fun _17593 : nat -> recspace A => @_mk_rec A (@ZCONSTR A _17591 _17592 (fun n : nat => @_dest_rec A (_17593 n)))).
Proof. constr_align (@axiom_9 A). Qed.

(****************************************************************************)
(* Alignment of the sum type constructor. *)
(****************************************************************************)

HB.instance Definition _ (A B : Type') := is_Type' (inl point : A+B).

Definition _dest_sum : forall {A B : Type'}, sum A B -> recspace (prod A B) :=
fun A B p => match p with
| inl a => CONSTR (NUMERAL 0) (a , ε (fun _ => True)) []_rec
| inr b => CONSTR (S (NUMERAL 0)) (ε (fun _ => True) , b) []_rec
end.

Definition _mk_sum {A B : Type'} := finv (@_dest_sum A B).

Lemma axiom_11 {A B : Type'} : forall (a : sum A B), (@_mk_sum A B (@_dest_sum A B a)) = a.
Proof. _mk_dest_inductive. Qed.

Lemma axiom_12 : forall {A B : Type'} (r : recspace (prod A B)), ((fun a : recspace (prod A B) => forall sum' : (recspace (prod A B)) -> Prop, (forall a' : recspace (prod A B), ((exists a'' : A, a' = ((fun a''' : A => @CONSTR (prod A B) (NUMERAL 0) (@pair A B a''' (@ε B (fun v : B => True))) (fun n : nat => @BOTTOM (prod A B))) a'')) \/ (exists a'' : B, a' = ((fun a''' : B => @CONSTR (prod A B) (S (NUMERAL 0)) (@pair A B (@ε A (fun v : A => True)) a''') (fun n : nat => @BOTTOM (prod A B))) a''))) -> sum' a') -> sum' a) r) = ((@_dest_sum A B (@_mk_sum A B r)) = r).
Proof. by _dest_mk_inductive. Qed.

Lemma INL_def {A B : Type'} : (@inl A B) = (fun a : A => @_mk_sum A B ((fun a' : A => @CONSTR (prod A B) (NUMERAL 0) (@pair A B a' (@ε B (fun v : B => True))) (fun n : nat => @BOTTOM (prod A B))) a)).
Proof. constr_align (@axiom_11 A B). Qed.

Lemma INR_def {A B : Type'} : (@inr A B) = (fun a : B => @_mk_sum A B ((fun a' : B => @CONSTR (prod A B) (S (NUMERAL 0)) (@pair A B (@ε A (fun v : A => True)) a') (fun n : nat => @BOTTOM (prod A B))) a)).
Proof. constr_align (@axiom_11 A B). Qed.

(****************************************************************************)
(* Alignment of the option type constructor. *)
(****************************************************************************)

Definition _dest_option : forall {A : Type'}, option A -> recspace A :=
  fun A o =>
    match o with
    | None => CONSTR (NUMERAL 0) (ε (fun _ => True)) []_rec
    | Some a => CONSTR (S (NUMERAL 0)) a []_rec
    end.

Definition _mk_option {A : Type'} := finv (@_dest_option A).

Lemma axiom_13 {A : Type'} : forall (a : option A), (@_mk_option A (@_dest_option A a)) = a.
Proof. _mk_dest_inductive. Qed.

Definition option_pred {A : Type'} (r : recspace A) :=
  forall option' : recspace A -> Prop,
      (forall a' : recspace A,
       a' = CONSTR (NUMERAL 0) (ε (fun _ : A => True)) (fun _ : nat => BOTTOM) \/
       (exists a'' : A, a' = CONSTR (S (NUMERAL 0)) a'' (fun _ : nat => BOTTOM)) ->
       option' a') -> option' r.

Lemma axiom_14' : forall {A : Type'} (r : recspace A), (option_pred r) = ((@_dest_option A (@_mk_option A r)) = r).
Proof. by _dest_mk_inductive. Qed.

Lemma axiom_14 : forall {A : Type'} (r : recspace A), ((fun a : recspace A => forall option' : (recspace A) -> Prop, (forall a' : recspace A, ((a' = (@CONSTR A (NUMERAL 0) (@ε A (fun v : A => True)) (fun n : nat => @BOTTOM A))) \/ (exists a'' : A, a' = ((fun a''' : A => @CONSTR A (S (NUMERAL 0)) a''' (fun n : nat => @BOTTOM A)) a''))) -> option' a') -> option' a) r) = ((@_dest_option A (@_mk_option A r)) = r).
Proof. exact @axiom_14'. Qed.

Lemma NONE_def {A : Type'} : (@None A) = (@_mk_option A (@CONSTR A (NUMERAL 0) (@ε A (fun v : A => True)) (fun n : nat => @BOTTOM A))).
Proof. constr_align (@axiom_13 A). Qed.

Lemma SOME_def {A : Type'} : (@Some A) = (fun a : A => @_mk_option A ((fun a' : A => @CONSTR A (S (NUMERAL 0)) a' (fun n : nat => @BOTTOM A)) a)).
Proof. constr_align (@axiom_13 A). Qed.

(****************************************************************************)
(* Alignment of the seq type constructor. *)
(****************************************************************************)

HB.instance Definition _ (A : Type') := isPointed.Build _ (Nil A).

Fixpoint _dest_seq {A : Type'} s : recspace A :=
  match s with
  | [::] => CONSTR 0 (ε (fun _ => True)) []_rec
  | a::s => CONSTR 1 a [_dest_seq s]_rec
  end.

Definition _mk_seq {A : Type'} := finv (@_dest_seq A).

Lemma axiom_15 {A : Type'} : forall (a : seq A), (@_mk_seq A (@_dest_seq A a)) = a.
Proof. _mk_dest_inductive. Qed.

Lemma axiom_16 : forall {A : Type'} (r : recspace A), ((fun a : recspace A => forall seq : (recspace A) -> Prop, (forall a' : recspace A, ((a' = (@CONSTR A (NUMERAL 0) (@ε A (fun v : A => True)) (fun n : nat => @BOTTOM A))) \/ (exists a0 : A, exists a1 : recspace A, (a' = ((fun a0' : A => fun a1' : recspace A => @CONSTR A (S (NUMERAL 0)) a0' (@FCONS (recspace A) a1' (fun n : nat => @BOTTOM A))) a0 a1)) /\ (seq a1))) -> seq a') -> seq a) r) = ((@_dest_seq A (@_mk_seq A r)) = r).
Proof. by _dest_mk_inductive. Qed.

Lemma NIL_def {A : Type'} : (Nil A) = (@_mk_seq A (@CONSTR A (NUMERAL 0) (@ε A (fun v : A => True)) (fun n : nat => @BOTTOM A))).
Proof. constr_align (@axiom_15 A). Qed.

Lemma CONS_def {A : Type'} : (@cons A) = (fun a0 : A => fun a1 : seq A => @_mk_seq A ((fun a0' : A => fun a1' : recspace A => @CONSTR A (S (NUMERAL 0)) a0' (@FCONS (recspace A) a1' (fun n : nat => @BOTTOM A))) a0 (@_dest_seq A a1))).
Proof. constr_align (@axiom_15 A). Qed.

(****************************************************************************)
(* Tools to align some seq functions *)
(****************************************************************************)

Inductive is_nil (A : Type) : seq A -> Prop := nil_is_nil : is_nil [::].
Arguments is_nil : clear implicits.

Lemma if_seq {A : Type} {B : Type'} {l : seq A} {x y : B} : 
  (if l = [::] then x else y) = if l is [::] then x else y.
Proof.
  by if_intro ; destruct l.
Qed.

Ltac if_seq := rewrite/COND if_seq.

(****************************************************************************)
(* Alignment of seq functions *)
(****************************************************************************)

Lemma APPEND_def {A : Type'} : (@cat A) = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (seq A) -> (seq A) -> seq A) (fun APPEND' : (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (seq A) -> (seq A) -> seq A => forall _17935 : prod nat (prod nat (prod nat (prod nat (prod nat nat)))), (forall l : seq A, (APPEND' _17935 (@nil A) l) = l) /\ (forall h : A, forall t : seq A, forall l : seq A, (APPEND' _17935 (@cons A h t) l) = (@cons A h (APPEND' _17935 t l)))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))))))).
Proof. by total_align. Qed.

Lemma REVERSE_def {A : Type'} : (@rev A) = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> (seq A) -> seq A) (fun REVERSE' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> (seq A) -> seq A => forall _17939 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))), ((REVERSE' _17939 (@nil A)) = (@nil A)) /\ (forall l : seq A, forall x : A, (REVERSE' _17939 (@cons A x l)) = (@cat A (REVERSE' _17939 l) (@cons A x (@nil A))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))))))))))).
Proof. by total_align=> // * ; rewrite rev_cons cats1. Qed.

Lemma LENGTH_def {A : Type'} : size = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (seq A) -> nat) (fun LENGTH' : (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (seq A) -> nat => forall _18106 : prod nat (prod nat (prod nat (prod nat (prod nat nat)))), ((LENGTH' _18106 (@nil A)) = 0) /\ (forall h : A, forall t : seq A, (LENGTH' _18106 (@cons A h t)) = (S (LENGTH' _18106 t)))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) ((BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) ((BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) ((BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) ((BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat ((BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) ((BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))))))))).
Proof. by total_align. Qed.

Lemma MAP_def {A B : Type'} : (@map A B) = (@ε ((prod nat (prod nat nat)) -> (A -> B) -> (seq A) -> seq B) (fun MAP' : (prod nat (prod nat nat)) -> (A -> B) -> (seq A) -> seq B => forall _17950 : prod nat (prod nat nat), (forall f : A -> B, (MAP' _17950 f (@nil A)) = (@nil B)) /\ (forall f : A -> B, forall h : A, forall t : seq A, (MAP' _17950 f (@cons A h t)) = (@cons B (f h) (MAP' _17950 f t)))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0))))))))))).
Proof. by total_align. Qed.

Definition BUTLAST (A : Type') (s : seq A) :=
  if s is x :: s' then belast x s' else [::].

Lemma BUTLAST_def {_25251 : Type'} : (@BUTLAST _25251) = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> (seq _25251) -> seq _25251) (fun BUTLAST' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> (seq _25251) -> seq _25251 => forall _17958 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))), ((BUTLAST' _17958 (@nil _25251)) = (@nil _25251)) /\ (forall h : _25251, forall t : seq _25251, (BUTLAST' _17958 (@cons _25251 h t)) = (@COND (seq _25251) (t = (@nil _25251)) (@nil _25251) (@cons _25251 h (BUTLAST' _17958 t))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))))))))))).
Proof.
  by total_align=> // a t ; if_seq ; elim:t. 
Qed.

Definition ALL {A : Type'} : (A -> Prop) -> seq A -> Prop := all.

Lemma ALL_def {_25307 : Type'} : (@ALL _25307) = (@ε ((prod nat (prod nat nat)) -> (_25307 -> Prop) -> (seq _25307) -> Prop) (fun ALL' : (prod nat (prod nat nat)) -> (_25307 -> Prop) -> (seq _25307) -> Prop => forall _17973 : prod nat (prod nat nat), (forall P : _25307 -> Prop, (ALL' _17973 P (@nil _25307)) = True) /\ (forall h : _25307, forall P : _25307 -> Prop, forall t : seq _25307, (ALL' _17973 P (@cons _25307 h t)) = ((P h) /\ (ALL' _17973 P t)))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))))))).
Proof.
  by total_align => * ; [rewrite is_True | rewrite/ALL -andP** asboolE].
Qed.

Fixpoint pairwise {A : Type'} (r : rel A) s := match s with
  | [::] => true
  | x::s => all (r x) s && pairwise r s end.

Definition PAIRWISE {A : Type'}: (A -> A -> Prop) -> seq A -> Prop := pairwise.

Lemma PAIRWISE_def {A : Type'} : (@PAIRWISE A) = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> (A -> A -> Prop) -> (seq A) -> Prop) (fun PAIRWISE' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> (A -> A -> Prop) -> (seq A) -> Prop => forall _18057 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))), (forall r : A -> A -> Prop, (PAIRWISE' _18057 r (@nil A)) = True) /\ (forall h : A, forall r : A -> A -> Prop, forall t : seq A, (PAIRWISE' _18057 r (@cons A h t)) = ((@ALL A (r h) t) /\ (PAIRWISE' _18057 r t)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))))))))))).
Proof.
  by total_align=> * ; [rewrite is_True | rewrite andP**].
Qed.

Definition FILTER {A : Type'} : (A -> Prop) -> seq A -> seq A := filter.

Lemma _FILTER_def {A : Type'} : (@FILTER A) = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (A -> Prop) -> (seq A) -> seq A) (fun FILTER' : (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (A -> Prop) -> (seq A) -> seq A => forall _18185 : prod nat (prod nat (prod nat (prod nat (prod nat nat)))), (forall P : A -> Prop, (FILTER' _18185 P (@nil A)) = (@nil A)) /\ (forall h : A, forall P : A -> Prop, forall t : seq A, (FILTER' _18185 P (@cons A h t)) = (@COND (seq A) (P h) (@cons A h (FILTER' _18185 P t)) (FILTER' _18185 P t)))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) ((BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) ((BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) ((BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) ((BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat nat ((BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) ((BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))))).
Proof. by total_align. Qed.

Definition MEM {A : Type'} a (s : seq A) : Prop := a \in s.

Lemma MEM_def {_25376 : Type'} : (@MEM _25376) = (@ε ((prod nat (prod nat nat)) -> _25376 -> (seq _25376) -> Prop) (fun MEM' : (prod nat (prod nat nat)) -> _25376 -> (seq _25376) -> Prop => forall _17995 : prod nat (prod nat nat), (forall x : _25376, (MEM' _17995 x (@nil _25376)) = False) /\ (forall h : _25376, forall x : _25376, forall t : seq _25376, (MEM' _17995 x (@cons _25376 h t)) = ((x = h) \/ (MEM' _17995 x t)))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))))))).
Proof.
  by total_align => * ; [ rewrite is_False | rewrite [in X in _=X]eqP** orP**].
Qed.

Lemma REPLICATE_def {A : Type'} : @nseq A = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) -> nat -> A -> seq A) (fun REPLICATE' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) -> nat -> A -> seq A => forall _18125 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))), (forall x : A, (REPLICATE' _18125 0 x) = (@nil A)) /\ (forall n : nat, forall x : A, (REPLICATE' _18125 (S n) x) = (@cons A x (REPLICATE' _18125 n x)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) ((BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) ((BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) ((BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) ((BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) ((BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) ((BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) ((BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat ((BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) ((BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))))))))))))).
Proof. by total_align. Qed.

Definition ITLIST {A B : Type'} 
(f: A -> B -> B) (l: seq A) (b: B) : B := @foldr A B f b l.

Lemma ITLIST_def {A B : Type'} : (@ITLIST A B) = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (A -> B -> B) -> (seq A) -> B -> B) (fun ITLIST' : (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (A -> B -> B) -> (seq A) -> B -> B => forall _18151 : prod nat (prod nat (prod nat (prod nat (prod nat nat)))), (forall f : A -> B -> B, forall b : B, (ITLIST' _18151 f (@nil A) b) = b) /\ (forall h : A, forall f : A -> B -> B, forall t : seq A, forall b : B, (ITLIST' _18151 f (@cons A h t) b) = (f h (ITLIST' _18151 f t b)))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))))).
Proof. by total_align. Qed.

Definition HD_HOL {A : Type'} := @ε ((prod nat nat) -> (seq A) -> A) (fun HD_HOL' : (prod nat nat) -> (seq A) -> A => forall _17927 : prod nat nat, forall t : seq A, forall h : A, (HD_HOL' _17927 (@cons A h t)) = h) (@pair nat nat (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))))).

Definition HD {A:Type'} := head (HD_HOL (Nil A)).

Lemma HD_def {A : Type'} : @HD A = @HD_HOL A.
Proof. by rewrite/HD_HOL ; partial_align (is_nil A). Qed.

Definition TL_HOL {A : Type'} := (@ε ((prod nat nat) -> (seq A) -> seq A) (fun TL_HOL' : (prod nat nat) -> (seq A) -> seq A => forall _17931 : prod nat nat, forall h : A, forall t : seq A, (TL_HOL' _17931 (@cons A h t)) = t) (@pair nat nat (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))))).

Definition TL {A : Type'} (s : seq A) := if s is [::] then TL_HOL [::]
  else behead s.

Lemma TL_def {A : Type'} : @TL A = @TL_HOL A.
Proof. by rewrite/TL_HOL ; partial_align (is_nil A). Qed.

Definition NULL : forall {A : Type'}, seq A -> Prop := nilp.

Lemma NULL_def {A : Type'} : @NULL A = (@ε ((prod nat (prod nat (prod nat nat))) -> (seq A) -> Prop) (fun NULL' : (prod nat (prod nat (prod nat nat))) -> (seq A) -> Prop => forall _18129 : prod nat (prod nat (prod nat nat)), ((NULL' _18129 (@nil A)) = True) /\ (forall h : A, forall t : seq A, (NULL' _18129 (@cons A h t)) = False)) (@pair nat (prod nat (prod nat nat)) ((BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) ((BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat nat ((BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) ((BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))))))).
Proof.
  total_align => * ; first by rewrite is_True.
  by rewrite/NULL is_False nilpE.
Qed.

Definition EX {A : Type'} : (A -> Prop) -> seq A -> Prop := has.

Lemma EX_def {A : Type'} : @EX A = (@ε ((prod nat nat) -> (A -> Prop) -> (seq A) -> Prop) (fun EX' : (prod nat nat) -> (A -> Prop) -> (seq A) -> Prop => forall _18143 : prod nat nat, (forall P : A -> Prop, (EX' _18143 P (@nil A)) = False) /\ (forall h : A, forall P : A -> Prop, forall t : seq A, (EX' _18143 P (@cons A h t)) = ((P h) \/ (EX' _18143 P t)))) (@pair nat nat ((BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) ((BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))))).
Proof.
  total_align => * ; first by rewrite is_False ; inversion 1.
  by rewrite/EX/= -orP** asboolE.
Qed.

Definition ALL2 {A B : Type'} : (A -> B -> Prop) -> seq A -> seq B -> Prop := all2.

Lemma ALL2_def {A B : Type'} : @ALL2 A B = (@ε ((prod nat (prod nat (prod nat nat))) -> (A -> B -> Prop) -> (seq A) -> (seq B) -> Prop) (fun ALL2' : (prod nat (prod nat (prod nat nat))) -> (A -> B -> Prop) -> (seq A) -> (seq B) -> Prop => forall _18166 : prod nat (prod nat (prod nat nat)), (forall P : A -> B -> Prop, forall l2 : seq B, (ALL2' _18166 P (@nil A) l2) = (l2 = (@nil B))) /\ (forall h1' : A, forall P : A -> B -> Prop, forall t1 : seq A, forall l2 : seq B, (ALL2' _18166 P (@cons A h1' t1) l2) = (@COND Prop (l2 = (@nil B)) False ((P h1' (@HD B l2)) /\ (ALL2' _18166 P t1 (@TL B l2)))))) (@pair nat (prod nat (prod nat nat)) ((BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) ((BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat ((BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) ((BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0))))))))))).
Proof.
  total_align=> [? | ???] ; first by case=>* ; rewrite (@eqP _ _ [::])**.
  rewrite/ALL2/=; case=>*; if_seq; [exact:falseE | by rewrite -andP** asboolE].
Qed.

Definition LAST_HOL {A : Type'} := (@ε ((prod nat (prod nat (prod nat nat))) -> (seq A) -> A) (fun LAST' : (prod nat (prod nat (prod nat nat))) -> (seq A) -> A => forall _18117 : prod nat (prod nat (prod nat nat)), forall h : A, forall t : seq A, (LAST' _18117 (@cons A h t)) = (@COND A (t = (@nil A)) h (LAST' _18117 t))) (@pair nat (prod nat (prod nat nat)) ((BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) ((BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat ((BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) ((BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))).

Definition LAST {A : Type'} (s : seq A) :=
  if s is x::s' then last x s' else LAST_HOL [::].

Lemma LAST_def {A : Type'} : LAST = (@ε ((prod nat (prod nat (prod nat nat))) -> (seq A) -> A) (fun LAST' : (prod nat (prod nat (prod nat nat))) -> (seq A) -> A => forall _18117 : prod nat (prod nat (prod nat nat)), forall h : A, forall t : seq A, (LAST' _18117 (@cons A h t)) = (@COND A (t = (@nil A)) h (LAST' _18117 t))) (@pair nat (prod nat (prod nat nat)) ((BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) ((BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat ((BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) ((BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))).
Proof.
  by partial_align (is_nil A) => ? ; case=>* ; if_seq.
Qed.

Fixpoint MAP2 {A B C : Type'} (f : A -> B -> C) (s : seq A) (s' : seq B) : seq C := 
match s with
|[::] => [::]
|a::s => f a (HD s') :: MAP2 f s (TL s') end.

Lemma MAP2_def {A B C : Type'} : MAP2 = (@ε ((prod nat (prod nat (prod nat nat))) -> (A -> B -> C) -> (seq A) -> (seq B) -> seq C) (fun MAP2' : (prod nat (prod nat (prod nat nat))) -> (A -> B -> C) -> (seq A) -> (seq B) -> seq C => forall _18174 : prod nat (prod nat (prod nat nat)), (forall f : A -> B -> C, forall l : seq B, (MAP2' _18174 f (@nil A) l) = (@nil C)) /\ (forall h1' : A, forall f : A -> B -> C, forall t1 : seq A, forall l : seq B, (MAP2' _18174 f (@cons A h1' t1) l) = (@cons C (f h1' (@HD B l)) (MAP2' _18174 f t1 (@TL B l))))) (@pair nat (prod nat (prod nat nat)) ((BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) ((BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat ((BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) ((BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0))))))))))).
Proof. by total_align. Qed.

(* There is no way that EL 1 (TL [::]) can be found using nth alone. *)
Fixpoint EL {A : Type'} n (s: seq A) :=
  if n - size s is k.+1 then EL k (TL_HOL [::]) else nth (HD_HOL [::]) s n.

Lemma EL_def {A : Type'} : EL = (@ε ((prod nat nat) -> nat -> (seq A) -> A) (fun EL' : (prod nat nat) -> nat -> (seq A) -> A => forall _18178 : prod nat nat, (forall l : seq A, (EL' _18178 0 l) = (@HD A l)) /\ (forall n : nat, forall l : seq A, (EL' _18178 (S n) l) = (EL' _18178 n (@TL A l)))) (@pair nat nat ((BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) ((BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))))).
Proof.
  by total_align ; [case | case => [|?] ; case].
Qed.

(* ASSOC a l gets the first b such that (a,b) \in l *)
(* If needed, one can try to weakly align finite maps with such a representation,
   if actually used in hol-light *)
Definition ASSOC_HOL {A B : Type'} := (@ε ((prod nat (prod nat (prod nat (prod nat nat)))) -> A -> (seq (prod A B)) -> B) (fun ASSOC' : (prod nat (prod nat (prod nat (prod nat nat)))) -> A -> (seq (prod A B)) -> B => forall _18192 : prod nat (prod nat (prod nat (prod nat nat))), forall h : prod A B, forall a : A, forall t : seq (prod A B), (ASSOC' _18192 a (@cons (prod A B) h t)) = (@COND B ((@fst A B h) = a) (@snd A B h) (ASSOC' _18192 a t))) (@pair nat (prod nat (prod nat (prod nat nat))) ((BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) ((BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) ((BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat nat ((BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) ((BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0))))))))))))).

Fixpoint ASSOC {A B : Type'} (a : A) (l : seq (A * B)) := 
match l with
|[::] => ASSOC_HOL a [::]
|(a0,b0)::l => if a0=a then b0 else ASSOC a l end.

Lemma ASSOC_def {A B : Type'} : ASSOC = (@ε ((prod nat (prod nat (prod nat (prod nat nat)))) -> A -> (seq (prod A B)) -> B) (fun ASSOC' : (prod nat (prod nat (prod nat (prod nat nat)))) -> A -> (seq (prod A B)) -> B => forall _18192 : prod nat (prod nat (prod nat (prod nat nat))), forall h : prod A B, forall a : A, forall t : seq (prod A B), (ASSOC' _18192 a (@cons (prod A B) h t)) = (@COND B ((@fst A B h) = a) (@snd A B h) (ASSOC' _18192 a t))) (@pair nat (prod nat (prod nat (prod nat nat))) ((BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) ((BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) ((BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat nat ((BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) ((BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0))))))))))))).
Proof. by partial_align (is_nil (A*B)) ; case. Qed.

(*
(* mathcomp's zip s s' stops when s or s' is empty,
   but hol-light only looks at s. In order to make it work,
   fill s' so that it never goes empty before s. *)
Fixpoint preZIP {A B : Type'} (s : seq A) (s' : seq B) (currentfill : seq B)
  (continuity : seq B -> seq B) := match s with
  | [::] => continuity [::]
  | a::s0 => match s' with
    | [::] => preZIP s0 [::] (TL currentfill) (fun r =>
      continuity (HD currentfill::r))
    | b::s'0 => preZIP s0 s'0 currentfill (fun r => continuity (b::r))
  end end.

Definition ZIP {A B : Type'} (s : seq A) (s' : seq B) :=
  zip s (preZIP s s' [::] id).
  *)

(* attempts including the one above were unfruitful, did not manage to use
   mathcomp's zip in some form *)

Fixpoint ZIP {A B : Type'} (s : seq A) (s' : seq B) :=
  if s is a::s0 then (a,HD s')::ZIP s0 (TL s') else [::].

Lemma ZIP_def {A B : Type'} : ZIP = (@ε ((prod nat (prod nat nat)) -> (seq A) -> (seq B) -> seq (prod A B)) (fun ZIP' : (prod nat (prod nat nat)) -> (seq A) -> (seq B) -> seq (prod A B) => forall _18205 : prod nat (prod nat nat), (forall l2 : seq B, (ZIP' _18205 (@nil A) l2) = (@nil (prod A B))) /\ (forall h1' : A, forall t1 : seq A, forall l2 : seq B, (ZIP' _18205 (@cons A h1' t1) l2) = (@cons (prod A B) (@pair A B h1' (@HD B l2)) (ZIP' _18205 t1 (@TL B l2))))) (@pair nat (prod nat nat) ((BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat nat ((BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) ((BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0))))))))))).
Proof. by total_align. Qed.

Lemma ZIP_zip {A B : Type'} (s : seq A) (s' : seq B) : size s <= size s' ->
  zip s s' = ZIP s s'.
Proof.
  elim:s s' => [|? ? IHs] [|? ?] //=; rewrite ltnS=> ?; f_equal ; exact:IHs.
Qed.

Definition ALLPAIRS {A B: Type'}: (A -> B -> Prop) -> seq A -> seq B -> Prop :=
  allrel.

Lemma ALLPAIRS_def {A B : Type'} : ALLPAIRS = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> (A -> B -> Prop) -> (seq A) -> (seq B) -> Prop) (fun ALLPAIRS' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> (A -> B -> Prop) -> (seq A) -> (seq B) -> Prop => forall _18213 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))), (forall f : A -> B -> Prop, forall l : seq B, (ALLPAIRS' _18213 f (@nil A) l) = True) /\ (forall h : A, forall f : A -> B -> Prop, forall t : seq A, forall l : seq B, (ALLPAIRS' _18213 f (@cons A h t) l) = ((@ALL B (f h) l) /\ (ALLPAIRS' _18213 f t l)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) ((BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) ((BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) ((BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) ((BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) ((BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) ((BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat nat ((BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) ((BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))))))).
Proof.
  by total_align => * ; [rewrite is_True | rewrite/ALLPAIRS/ALL -andP**].
Qed.

Lemma list_of_seq_def {A : Type'} : @mkseq A = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (nat -> A) -> nat -> seq A) (fun list_of_seq' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (nat -> A) -> nat -> seq A => forall _18227 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))), (forall s : nat -> A, (list_of_seq' _18227 s 0) = (@nil A)) /\ (forall s : nat -> A, forall n : nat, (list_of_seq' _18227 s (S n)) = (@cat A (list_of_seq' _18227 s n) (@cons A (s n) (@nil A))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) ((BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) ((BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) ((BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) ((BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) ((BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) ((BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) ((BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) ((BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) ((BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0)))))))) (@pair nat nat ((BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))) ((BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 0))))))))))))))))))).
Proof.
  by total_align=> // * ; rewrite mkseqS cats1.
Qed.

Fixpoint ITLIST2 {A B C : Type'} (f : A -> B -> C -> C) 
(l : seq A) (l' : seq B) (c : C) : C := 
match l with
|[::] => c
|a::l => (f a (HD l') (ITLIST2 f l (TL l') c)) end.

Lemma ITLIST2_def {A B C : Type'} : ITLIST2 = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> (A -> B -> C -> C) -> (seq A) -> (seq B) -> C -> C) (fun ITLIST2' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> (A -> B -> C -> C) -> (seq A) -> (seq B) -> C -> C => forall _18201 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))), (forall f : A -> B -> C -> C, forall l2 : seq B, forall b : C, (ITLIST2' _18201 f (@nil A) l2 b) = b) /\ (forall h1' : A, forall f : A -> B -> C -> C, forall t1 : seq A, forall l2 : seq B, forall b : C, (ITLIST2' _18201 f (@cons A h1' t1) l2 b) = (f h1' (@HD B l2) (ITLIST2' _18201 f t1 (@TL B l2) b)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) ((BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) ((BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) ((BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat (prod nat nat)) ((BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 0)))))))) (@pair nat (prod nat nat) ((BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) (@pair nat nat ((BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))) ((BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 0)))))))))))))).
Proof. by total_align. Qed.

(****************************************************************************)
(* Alignment of the type of ASCII characters. *)
(****************************************************************************)

(* Note the mismatch between Rocq's ascii which takes booleans as arguments
and HOL-Light's char which takes propositions as arguments. *)

HB.instance Definition _ := is_Type' Ascii.zero.

Definition _dest_char : ascii -> recspace (Prop*(Prop*(Prop*(Prop*(Prop*(Prop*(Prop*(Prop)))))))) :=
  fun a => match a with
  | Ascii a0 a1 a2 a3 a4 a5 a6 a7 => CONSTR 0
    ((fun a0 a1 a2 a3 a4 a5 a6 a7 : Prop => (a0,(a1,(a2,(a3,(a4,(a5,(a6,(a7)))))))))
    a0 a1 a2 a3 a4 a5 a6 a7) []_rec end.

Definition _mk_char := finv _dest_char.

Lemma axiom_17 : forall (a : ascii), (_mk_char (_dest_char a)) = a.
Proof.
  by finv_inv_l ; intros [] [] [=] * ; f_equal ; AllProp.
Qed.

Definition char_pred (r : recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))) :=
  forall char' : (recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))) -> Prop, (forall a' : recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))), (exists a0 : Prop, exists a1 : Prop, exists a2 : Prop, exists a3 : Prop, exists a4 : Prop, exists a5 : Prop, exists a6 : Prop, exists a7 : Prop, a' =
    ((fun a0' : Prop => fun a1' : Prop => fun a2' : Prop => fun a3' : Prop => fun a4' : Prop => fun a5' : Prop => fun a6' : Prop => fun a7' : Prop => @CONSTR (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))) (NUMERAL 0) (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))) a0' (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))) a1' (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))) a2' (@pair Prop (prod Prop (prod Prop (prod Prop Prop))) a3' (@pair Prop (prod Prop (prod Prop Prop)) a4' (@pair Prop (prod Prop Prop) a5' (@pair Prop Prop a6' a7'))))))) (fun n : nat => @BOTTOM (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))))) a0 a1 a2 a3 a4 a5 a6 a7)) -> char' a') -> char' r.

Inductive char_ind : recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))) -> Prop :=
| char_ind_cons a0 a1 a2 a3 a4 a5 a6 a7 :
  char_ind (CONSTR (NUMERAL 0) (is_true a0, (is_true a1, (is_true a2, (is_true a3, (is_true a4, (is_true a5, (is_true a6, is_true a7))))))) (fun _ => BOTTOM)).

Lemma axiom_18' : forall (r : recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))),
char_pred r = ((_dest_char (_mk_char r)) = r).
Proof.
  _dest_mk_inductive.
  by exists (Ascii x0 x1 x2 x3 x4 x5 x6 x7) ; rewrite/= 8!asboolE.
Qed.

Lemma axiom_18 : forall (r : recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))), ((fun a : recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))) => forall char' : (recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))) -> Prop, (forall a' : recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))), (exists a0 : Prop, exists a1 : Prop, exists a2 : Prop, exists a3 : Prop, exists a4 : Prop, exists a5 : Prop, exists a6 : Prop, exists a7 : Prop, a' =
((fun a0' : Prop => fun a1' : Prop => fun a2' : Prop => fun a3' : Prop => fun a4' : Prop => fun a5' : Prop => fun a6' : Prop => fun a7' : Prop => @CONSTR (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))) (NUMERAL 0) (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))) a0' (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))) a1' (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))) a2' (@pair Prop (prod Prop (prod Prop (prod Prop Prop))) a3' (@pair Prop (prod Prop (prod Prop Prop)) a4' (@pair Prop (prod Prop Prop) a5' (@pair Prop Prop a6' a7'))))))) (fun n : nat => @BOTTOM (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))))) a0 a1 a2 a3 a4 a5 a6 a7)) -> char' a') -> char' a) r) = ((_dest_char (_mk_char r)) = r).
Proof. exact axiom_18'. Qed.

(*****************************************************************************)
(* Alignment of the type nadd of nearly additive sequences of naturals. *)
(*****************************************************************************)

Definition dist := fun p : prod nat nat => addn (subn (@fst nat nat p) (@snd nat nat p)) (subn (@snd nat nat p) (@fst nat nat p)).

Lemma dist_def : dist = (fun _22947 : prod nat nat => addn (subn (@fst nat nat _22947) (@snd nat nat _22947)) (subn (@snd nat nat _22947) (@fst nat nat _22947))).
Proof. exact erefl. Qed.

Lemma DIST_REFL : forall n : nat, dist (n,n) = 0.
Proof. by move=> n ; rewrite/dist/= subnn. Qed.

Lemma DIST_SYM x y : dist (x,y) = dist (y,x).
Proof. by rewrite/dist/= addnC. Qed.

Lemma ltn_sub_telescope x y z : x - z <= x - y + (y - z).
Proof.
  elim: y x z => [|y IHy] x z ; first by rewrite subn0 sub0n addn0 leq_subr.
  case:x=> [|x] ; [by rewrite sub0n leq0n | case:z=> [|z]].
  - by rewrite subSS addnS ltnS -{1}(subn0 x) -{2}(subn0 y).
  - by rewrite 3! subSS.
Qed.

Lemma DIST_TRIANGLE x y z : dist (x,z) <= dist (x,y) + dist (y,z).
Proof.
  rewrite/dist/= addnACA (addnC (y-x)); apply leq_add; exact:ltn_sub_telescope.
Qed.

Definition is_nadd := fun f : nat -> nat => exists B : nat, forall m : nat, forall n : nat, leqn (dist (@pair nat nat (muln m (f n)) (muln n (f m)))) (muln B (addn m n)).

Lemma is_nadd_def : is_nadd = (fun _23257 : nat -> nat => exists B : nat, forall m : nat, forall n : nat, leqn (dist (@pair nat nat (muln m (_23257 n)) (muln n (_23257 m)))) (muln B (addn m n))).
Proof. exact erefl. Qed.

Lemma is_nadd_times n : is_nadd (fun x => n * x).
Proof.
  by exists 0 => x ?; rewrite (mulnC n) mulnCA (mulnC x) DIST_REFL.
Qed.

Lemma is_nadd_0 : is_nadd (fun _ => 0).
Proof. exact (is_nadd_times 0). Qed.

Definition nadd := subtype is_nadd_0.

Definition mk_nadd := mk is_nadd_0.
Definition dest_nadd := dest is_nadd_0.

Lemma axiom_19 : forall (a : nadd), (mk_nadd (dest_nadd a)) = a.
Proof. exact (mk_dest is_nadd_0). Qed.

Lemma axiom_20_aux : forall (r : nat -> nat), (is_nadd r) -> ((dest_nadd (mk_nadd r)) = r).
Proof. exact (dest_mk_aux is_nadd_0). Qed.

Lemma axiom_20 : forall (r : nat -> nat), (is_nadd r) = ((dest_nadd (mk_nadd r)) = r).
Proof. exact (dest_mk is_nadd_0). Qed.

Definition nadd_of_num : nat -> nadd := fun _23288 : nat => mk_nadd (fun n : nat => muln _23288 n).

Lemma nadd_of_num_def : nadd_of_num = (fun _23288 : nat => mk_nadd (fun n : nat => muln _23288 n)).
Proof. exact erefl. Qed.

Definition nadd_le : nadd -> nadd -> Prop := fun _23295 : nadd => fun _23296 : nadd => exists B : nat, forall n : nat, leqn (dest_nadd _23295 n) (addn (dest_nadd _23296 n) B).

Lemma nadd_le_def : nadd_le = (fun _23295 : nadd => fun _23296 : nadd => exists B : nat, forall n : nat, leqn (dest_nadd _23295 n) (addn (dest_nadd _23296 n) B)).
Proof. exact erefl. Qed.

Lemma nadd_le_refl x : nadd_le x x.
Proof.
  by exists 0 => ? ; rewrite/leqn addn0 leqnn.
Qed.

Lemma  nadd_le_trans x y z : nadd_le x y -> nadd_le y z -> nadd_le x z.
Proof.
  move=> [B h] [C i]. exists (B+C) => n.
  apply:(leq_trans (h _)) ; rewrite (addnC B) addnA leq_add2r ; exact:i.
Qed.

Add Relation _ nadd_le
    reflexivity proved by nadd_le_refl
    transitivity proved by nadd_le_trans
as nadd_le_rel.

Definition nadd_add : nadd -> nadd -> nadd := fun _23311 : nadd => fun _23312 : nadd => mk_nadd (fun n : nat => addn (dest_nadd _23311 n) (dest_nadd _23312 n)).

Lemma nadd_add_def : nadd_add = (fun _23311 : nadd => fun _23312 : nadd => mk_nadd (fun n : nat => addn (dest_nadd _23311 n) (dest_nadd _23312 n))).
Proof. exact erefl. Qed.

Lemma is_nadd_add_aux f g : is_nadd f -> is_nadd g -> is_nadd (fun n => f n + g n).
Proof.
  rewrite/is_nadd/leqn/dist => /= -[b i] [c j]. exists (b+c) => x y.
  have:= (conj (i x y) (j x y)) ; lia.
Qed.

Lemma is_nadd_add f g : is_nadd (fun n => dest_nadd f n + dest_nadd g n).
Proof.
  destruct f as [f hf]. destruct g as [g hg]. simpl.
  apply is_nadd_add_aux. exact hf. exact hg.
Qed.

Lemma nadd_of_num_add p q :
  nadd_of_num (p + q) = nadd_add (nadd_of_num p) (nadd_of_num q).
Proof.
  unfold nadd_add, nadd_of_num. f_equal. ext=> x.
  rewrite axiom_20_aux. 2: apply is_nadd_times.
  rewrite axiom_20_aux. 2: apply is_nadd_times.
  exact: mulnDl.
Qed.

Lemma NADD_ADD_SYM p q : nadd_add p q = nadd_add q p.
Proof. unfold nadd_add. f_equal. ext=>x. exact: addnC. Qed.

Lemma NADD_ADD_ASSOC p q r :
  nadd_add (nadd_add p q) r = nadd_add p (nadd_add q r).
Proof.
  rewrite/nadd_add ; f_equal => /` x. rewrite !axiom_20_aux.
  2,3 : exact: is_nadd_add. by rewrite addnA.
Qed.

Definition nadd_mul : nadd -> nadd -> nadd := fun _23325 : nadd => fun _23326 : nadd => mk_nadd (fun n : nat => dest_nadd _23325 (dest_nadd _23326 n)).

Lemma nadd_mul_def : nadd_mul = (fun _23325 : nadd => fun _23326 : nadd => mk_nadd (fun n : nat => dest_nadd _23325 (dest_nadd _23326 n))).
Proof. exact erefl. Qed.

Definition nadd_rinv : nadd -> nat -> nat := fun _23462 : nadd => fun n : nat => divn (muln n n) (dest_nadd _23462 n).

Lemma nadd_rinv_def : nadd_rinv = (fun _23462 : nadd => fun n : nat => divn (muln n n) (dest_nadd _23462 n)).
Proof. exact erefl. Qed.

Definition nadd_eq : nadd -> nadd -> Prop := fun _23276 : nadd => fun _23277 : nadd => exists B : nat, forall n : nat, leqn (dist (@pair nat nat (dest_nadd _23276 n) (dest_nadd _23277 n))) B.

Lemma nadd_eq_def : nadd_eq = (fun _23276 : nadd => fun _23277 : nadd => exists B : nat, forall n : nat, leqn (dist (@pair nat nat (dest_nadd _23276 n) (dest_nadd _23277 n))) B).
Proof. exact erefl. Qed.

Lemma NADD_EQ_REFL f : nadd_eq f f.
Proof.
  by exists 0=> n ; rewrite/dist/leqn/= subnn addn0.
Qed.

Lemma nadd_eq_sym f g : nadd_eq f g -> nadd_eq g f.
Proof. intros [b fg]. exists b. intro n. rewrite DIST_SYM. apply fg. Qed.

Lemma nadd_eq_trans f g h : nadd_eq f g -> nadd_eq g h -> nadd_eq f h.
Proof.
  intros [b fg] [c gh]. exists (b+c). intro n.
  apply (leq_trans (@DIST_TRIANGLE _ (dest_nadd g n) _)).
  apply leq_add ; [exact: fg | exact: gh].
Qed.

Add Relation _ nadd_eq
    reflexivity proved by NADD_EQ_REFL
    symmetry proved by nadd_eq_sym
    transitivity proved by nadd_eq_trans
as nadd_eq_rel.

Add Morphism nadd_add : nadd_add_morph.
Proof.
  intros f f' [b ff'] g g' [c gg']. exists (b+c). intro n.
  generalize (ff' n); intro ff'n. generalize (gg' n); intro gg'n.
  unfold nadd_add. rewrite !axiom_20_aux. 2,3 : exact: is_nadd_add.
  unfold leqn,dist,dest_nadd,dest in *. simpl in *. lia.
Qed.

(*Add Morphism nadd_le
    with signature nadd_eq ==> nadd_eq ==> iff
      as nadd_le_morph.
Proof.
  intros f f' [b ff'] g g' [c gg'].
Abort.*)

Lemma nadd_add_lcancel : forall x y z, nadd_add x y = nadd_add x z -> y = z.
Proof.
  case => x naddx [y naddy] [z naddz] ; rewrite/nadd_add/=.
  move/(mk_inj (is_nadd_add_aux naddx naddy) (is_nadd_add_aux naddx naddz)).
  move:naddy=> /[swap]/[gen] eqzy. 
  have -> : y = z by ext=> n ; apply: addnI ; exact:eqzy.
  move=>? ; f_equal ; exact: proof_irrelevance.
Qed.

Lemma NADD_ADD_LCANCEL : forall x y z,
  nadd_eq (nadd_add x y) (nadd_add x z) -> nadd_eq y z.
Proof.
  case => x naddx [y naddy] [z naddz] [B h]. exists B=> n ; have:= h n.
  rewrite/nadd_add/dest_nadd/mk_nadd/= !dest_mk_aux. 2,3: exact:is_nadd_add_aux.
  rewrite/leqn/dist/= ; lia.
Qed.

Definition nadd_inv : nadd -> nadd := fun _23476 : nadd => @COND nadd (nadd_eq _23476 (nadd_of_num (NUMERAL 0))) (nadd_of_num (NUMERAL 0)) (mk_nadd (nadd_rinv _23476)).

Lemma nadd_inv_def : nadd_inv = (fun _23476 : nadd => @COND nadd (nadd_eq _23476 (nadd_of_num (NUMERAL 0))) (nadd_of_num (NUMERAL 0)) (mk_nadd (nadd_rinv _23476))).
Proof. exact erefl. Qed.

(*****************************************************************************)
(* Alignment of the type hreal of non-negative real numbers. *)
(*****************************************************************************)

Definition hreal := quotient nadd_eq.

Definition mk_hreal := mk_quotient nadd_eq.
Definition dest_hreal := dest_quotient nadd_eq.

Lemma axiom_21 : forall (a : hreal), (mk_hreal (dest_hreal a)) = a.
Proof. exact (mk_dest_quotient nadd_eq). Qed.

Lemma axiom_22_aux : forall r : nadd -> Prop, (exists x : nadd, r = nadd_eq x) -> dest_hreal (mk_hreal r) = r.
Proof. exact (dest_mk_aux_quotient nadd_eq). Qed.

Lemma axiom_22 : forall (r : nadd -> Prop), ((fun s : nadd -> Prop => exists x : nadd, s = (nadd_eq x)) r) = ((dest_hreal (mk_hreal r)) = r).
Proof. exact (dest_mk_quotient nadd_eq). Qed.

Definition hreal_of_num : nat -> hreal := fun m : nat => mk_hreal (nadd_eq (nadd_of_num m)).

Lemma hreal_of_num_def : hreal_of_num = (fun m : nat => mk_hreal (fun u : nadd => nadd_eq (nadd_of_num m) u)).
Proof. exact erefl. Qed.

Definition hreal_add : hreal -> hreal -> hreal := fun x : hreal => fun y : hreal => mk_hreal (fun u : nadd => exists x' : nadd, exists y' : nadd, (nadd_eq (nadd_add x' y') u) /\ ((dest_hreal x x') /\ (dest_hreal y y'))).

Lemma hreal_add_def : hreal_add = (fun x : hreal => fun y : hreal => mk_hreal (fun u : nadd => exists x' : nadd, exists y' : nadd, (nadd_eq (nadd_add x' y') u) /\ ((dest_hreal x x') /\ (dest_hreal y y')))).
Proof. exact erefl. Qed.

Lemma hreal_add_of_num p q :
  hreal_of_num (p + q) = hreal_add (hreal_of_num p) (hreal_of_num q).
Proof.
  unfold hreal_add, hreal_of_num. f_equal. ext=>x h.
  exists (nadd_of_num p). exists (nadd_of_num q). split.
  rewrite <- nadd_of_num_add. exact h. split.
  rewrite axiom_22_aux. 2: exists (nadd_of_num p); reflexivity. apply NADD_EQ_REFL.
  rewrite axiom_22_aux. 2: exists (nadd_of_num q); reflexivity. apply NADD_EQ_REFL.
  destruct h as [f [g [h1 [h2 h3]]]].
  rewrite axiom_22_aux in h2. 2: exists (nadd_of_num p); reflexivity.
  rewrite axiom_22_aux in h3. 2: exists (nadd_of_num q); reflexivity.
  rewrite nadd_of_num_add. rewrite h2 h3. exact h1.
Qed.

Lemma succ_eq_add_1 n : S n = n + 1. Proof. lia. Qed.

Lemma hreal_of_num_S n : hreal_of_num (S n) = hreal_add (hreal_of_num n) (hreal_of_num 1).
Proof. rewrite succ_eq_add_1 hreal_add_of_num. reflexivity. Qed.

Lemma hreal_add_sym p q : hreal_add p q = hreal_add q p.
Proof.
  unfold hreal_add. f_equal. ext=>x [y [z [h1 [h2 h3]]]].
  exists z. exists y. split. rewrite NADD_ADD_SYM. exact h1. auto.
  exists z. exists y. split. rewrite NADD_ADD_SYM. exact h1. auto.
Qed.

Lemma hreal_add_of_mk_hreal p q :
  hreal_add (mk_hreal (nadd_eq p)) (mk_hreal (nadd_eq q))
  = mk_hreal (nadd_eq (nadd_add p q)).
Proof.
  unfold hreal_add. apply f_equal. ext=> x h.

  unfold dest_hreal, mk_hreal in h. destruct h as [p' [q' [h1 [h2 h3]]]].
  rewrite dest_mk_aux_quotient in h2. 2: apply is_eq_class_of.
  rewrite dest_mk_aux_quotient in h3. 2: apply is_eq_class_of.
  rewrite h2 h3. exact h1.

  exists p. exists q. split. exact h. unfold dest_hreal, mk_hreal.
  rewrite !dest_mk_aux_quotient. split; reflexivity.
  apply is_eq_class_of. apply is_eq_class_of.
Qed.

Lemma mk_hreal_nadd_eq p : mk_hreal (nadd_eq (elt_of p)) = p.
Proof.
  unfold mk_hreal. apply mk_quotient_elt_of.
  apply NADD_EQ_REFL. apply nadd_eq_sym. apply nadd_eq_trans.
Qed.

(*Lemma hreal_add_is_mk_hreal p q :
  hreal_add p q = mk_hreal (nadd_eq (nadd_add (elt_of p) (elt_of q))).
Proof.
  rewrite <- (mk_hreal_nadd_eq p), <- (mk_hreal_nadd_eq q), hreal_add_of_mk_hreal.
  unfold mk_hreal at 3. unfold mk_hreal at 3. rewrite !mk_quotient_elt_of.
  reflexivity.
  apply NADD_EQ_REFL. apply nadd_eq_sym. apply nadd_eq_trans.
  apply NADD_EQ_REFL. apply nadd_eq_sym. apply nadd_eq_trans.
Qed.*)

Lemma hreal_add_ASSOC p q r :
  hreal_add (hreal_add p q) r = hreal_add p (hreal_add q r).
Proof.
  rewrite <- (mk_hreal_nadd_eq p), <- (mk_hreal_nadd_eq q),
    <- (mk_hreal_nadd_eq r), !hreal_add_of_mk_hreal.
  f_equal. rewrite NADD_ADD_ASSOC. reflexivity.
Qed.

Lemma hreal_add_lcancel p q r : hreal_add p r = hreal_add q r -> p = q.
Proof.
  rewrite <- (mk_hreal_nadd_eq p), <- (mk_hreal_nadd_eq q),
    <- (mk_hreal_nadd_eq r), !hreal_add_of_mk_hreal; intro e.
  unfold mk_hreal, mk_quotient in e. apply mk_inj in e.
  2: apply is_eq_class_of. 2: apply is_eq_class_of.
  apply eq_class_elim in e. 2: apply NADD_EQ_REFL.
  rewrite NADD_ADD_SYM (NADD_ADD_SYM (elt_of q)) in e.
  apply NADD_ADD_LCANCEL in e.
  f_equal. apply eq_class_intro. apply nadd_eq_sym. apply nadd_eq_trans.
  exact e.
Qed.

Definition hreal_mul : hreal -> hreal -> hreal := fun x : hreal => fun y : hreal => mk_hreal (fun u : nadd => exists x' : nadd, exists y' : nadd, (nadd_eq (nadd_mul x' y') u) /\ ((dest_hreal x x') /\ (dest_hreal y y'))).

Lemma hreal_mul_def : hreal_mul = (fun x : hreal => fun y : hreal => mk_hreal (fun u : nadd => exists x' : nadd, exists y' : nadd, (nadd_eq (nadd_mul x' y') u) /\ ((dest_hreal x x') /\ (dest_hreal y y')))).
Proof. exact erefl. Qed.

Definition hreal_le : hreal -> hreal -> Prop := fun x : hreal => fun y : hreal => @ε Prop (fun u : Prop => exists x' : nadd, exists y' : nadd, ((nadd_le x' y') = u) /\ ((dest_hreal x x') /\ (dest_hreal y y'))).

Lemma hreal_le_def : hreal_le = (fun x : hreal => fun y : hreal => @ε Prop (fun u : Prop => exists x' : nadd, exists y' : nadd, ((nadd_le x' y') = u) /\ ((dest_hreal x x') /\ (dest_hreal y y')))).
Proof. exact erefl. Qed.

(*Lemma hreal_le_refl x : hreal_le x x.
Proof.
  unfold hreal_le.
  match goal with [|- ε ?x] => set (Q := x); set (q := ε Q) end.
  assert (i: exists x, Q x). exists True. set (t := elt_of x). exists t. exists t. split.
  rewrite is_True. apply nadd_le_refl.
  assert (h: dest_hreal x t). apply dest_quotient_elt_of. apply NADD_EQ_REFL.
  auto.
  generalize (ε_spec i); intros [x1 [x2 [h1 [h2 h3]]]].
  unfold reverse_coercion. rewrite <- h1.
  apply dest_quotient_elim in h2.
  2: apply NADD_EQ_REFL. 2: apply nadd_eq_sym. 2: apply nadd_eq_trans.
  apply dest_quotient_elim in h3.
  2: apply NADD_EQ_REFL. 2: apply nadd_eq_sym. 2: apply nadd_eq_trans.
  rewrite <- h2, <- h3. reflexivity.
Qed.

Add Relation _ hreal_le
    reflexivity proved by hreal_le_refl
    (*transitivity proved by hreal_le_trans*)
as hreal_le_rel.*)

Definition hreal_inv : hreal -> hreal := fun x : hreal => mk_hreal (fun u : nadd => exists x' : nadd, (nadd_eq (nadd_inv x') u) /\ (dest_hreal x x')).

Lemma hreal_inv_def : hreal_inv = (fun x : hreal => mk_hreal (fun u : nadd => exists x' : nadd, (nadd_eq (nadd_inv x') u) /\ (dest_hreal x x'))).
Proof. exact erefl. Qed.

(*****************************************************************************)
(* Operations on treal (pairs of hreal's). *)
(*****************************************************************************)

Definition treal_of_num : nat -> prod hreal hreal := fun _23721 : nat => @pair hreal hreal (hreal_of_num _23721) (hreal_of_num (NUMERAL 0)).

Lemma treal_of_num_def : treal_of_num = (fun _23721 : nat => @pair hreal hreal (hreal_of_num _23721) (hreal_of_num (NUMERAL 0))).
Proof. exact erefl. Qed.

Definition treal_neg : (prod hreal hreal) -> prod hreal hreal := fun _23726 : prod hreal hreal => @pair hreal hreal (@snd hreal hreal _23726) (@fst hreal hreal _23726).

Lemma treal_neg_def : treal_neg = (fun _23726 : prod hreal hreal => @pair hreal hreal (@snd hreal hreal _23726) (@fst hreal hreal _23726)).
Proof. exact erefl. Qed.

Definition treal_add : (prod hreal hreal) -> (prod hreal hreal) -> prod hreal hreal := fun _23735 : prod hreal hreal => fun _23736 : prod hreal hreal => @pair hreal hreal (hreal_add (@fst hreal hreal _23735) (@fst hreal hreal _23736)) (hreal_add (@snd hreal hreal _23735) (@snd hreal hreal _23736)).

Lemma treal_add_def : treal_add = (fun _23735 : prod hreal hreal => fun _23736 : prod hreal hreal => @pair hreal hreal (hreal_add (@fst hreal hreal _23735) (@fst hreal hreal _23736)) (hreal_add (@snd hreal hreal _23735) (@snd hreal hreal _23736))).
Proof. exact erefl. Qed.

Lemma treal_add_of_num p q :
  treal_of_num (p + q) = treal_add (treal_of_num p) (treal_of_num q).
Proof.
  unfold treal_of_num, treal_add; simpl.
  f_equal; rewrite <- hreal_add_of_num; reflexivity.
Qed.

Lemma treal_add_sym  p q : treal_add p q = treal_add q p.
Proof. unfold treal_add. f_equal; apply hreal_add_sym. Qed.

Definition treal_mul : (prod hreal hreal) -> (prod hreal hreal) -> prod hreal hreal := fun _23757 : prod hreal hreal => fun _23758 : prod hreal hreal => @pair hreal hreal (hreal_add (hreal_mul (@fst hreal hreal _23757) (@fst hreal hreal _23758)) (hreal_mul (@snd hreal hreal _23757) (@snd hreal hreal _23758))) (hreal_add (hreal_mul (@fst hreal hreal _23757) (@snd hreal hreal _23758)) (hreal_mul (@snd hreal hreal _23757) (@fst hreal hreal _23758))).

Lemma treal_mul_def : treal_mul = (fun _23757 : prod hreal hreal => fun _23758 : prod hreal hreal => @pair hreal hreal (hreal_add (hreal_mul (@fst hreal hreal _23757) (@fst hreal hreal _23758)) (hreal_mul (@snd hreal hreal _23757) (@snd hreal hreal _23758))) (hreal_add (hreal_mul (@fst hreal hreal _23757) (@snd hreal hreal _23758)) (hreal_mul (@snd hreal hreal _23757) (@fst hreal hreal _23758)))).
Proof. exact erefl. Qed.

Definition treal_le : (prod hreal hreal) -> (prod hreal hreal) -> Prop := fun _23779 : prod hreal hreal => fun _23780 : prod hreal hreal => hreal_le (hreal_add (@fst hreal hreal _23779) (@snd hreal hreal _23780)) (hreal_add (@fst hreal hreal _23780) (@snd hreal hreal _23779)).

Lemma treal_le_def : treal_le = (fun _23779 : prod hreal hreal => fun _23780 : prod hreal hreal => hreal_le (hreal_add (@fst hreal hreal _23779) (@snd hreal hreal _23780)) (hreal_add (@fst hreal hreal _23780) (@snd hreal hreal _23779))).
Proof. exact erefl. Qed.

(*Lemma treal_le_refl x : treal_le x x.
Proof.
  unfold treal_le. destruct x as [x1 x2]. simpl. apply hreal_le_refl.
Qed.

Add Relation _ treal_le
    reflexivity proved by treal_le_refl
    (*transitivity proved by treal_le_trans*)
as treal_le_rel.*)

Definition treal_inv : (prod hreal hreal) -> prod hreal hreal := fun _23801 : prod hreal hreal => @COND (prod hreal hreal) ((@fst hreal hreal _23801) = (@snd hreal hreal _23801)) (@pair hreal hreal (hreal_of_num (NUMERAL 0)) (hreal_of_num (NUMERAL 0))) (@COND (prod hreal hreal) (hreal_le (@snd hreal hreal _23801) (@fst hreal hreal _23801)) (@pair hreal hreal (hreal_inv (@ε hreal (fun d : hreal => (@fst hreal hreal _23801) = (hreal_add (@snd hreal hreal _23801) d)))) (hreal_of_num (NUMERAL 0))) (@pair hreal hreal (hreal_of_num (NUMERAL 0)) (hreal_inv (@ε hreal (fun d : hreal => (@snd hreal hreal _23801) = (hreal_add (@fst hreal hreal _23801) d)))))).

Lemma treal_inv_def : treal_inv = (fun _23801 : prod hreal hreal => @COND (prod hreal hreal) ((@fst hreal hreal _23801) = (@snd hreal hreal _23801)) (@pair hreal hreal (hreal_of_num (NUMERAL 0)) (hreal_of_num (NUMERAL 0))) (@COND (prod hreal hreal) (hreal_le (@snd hreal hreal _23801) (@fst hreal hreal _23801)) (@pair hreal hreal (hreal_inv (@ε hreal (fun d : hreal => (@fst hreal hreal _23801) = (hreal_add (@snd hreal hreal _23801) d)))) (hreal_of_num (NUMERAL 0))) (@pair hreal hreal (hreal_of_num (NUMERAL 0)) (hreal_inv (@ε hreal (fun d : hreal => (@snd hreal hreal _23801) = (hreal_add (@fst hreal hreal _23801) d))))))).
Proof. exact erefl. Qed.

Definition treal_eq : (prod hreal hreal) -> (prod hreal hreal) -> Prop := fun _23810 : prod hreal hreal => fun _23811 : prod hreal hreal => (hreal_add (@fst hreal hreal _23810) (@snd hreal hreal _23811)) = (hreal_add (@fst hreal hreal _23811) (@snd hreal hreal _23810)).

Lemma treal_eq_def : treal_eq = (fun _23810 : prod hreal hreal => fun _23811 : prod hreal hreal => (hreal_add (@fst hreal hreal _23810) (@snd hreal hreal _23811)) = (hreal_add (@fst hreal hreal _23811) (@snd hreal hreal _23810))).
Proof. exact erefl. Qed.

Lemma treal_eq_refl x : treal_eq x x.
Proof. reflexivity. Qed.

Lemma treal_eq_sym x y : treal_eq x y -> treal_eq y x.
Proof.
  unfold treal_eq. destruct x as [x1 x2]; destruct y as [y1 y2]; simpl.
  intro e. symmetry. exact e.
Qed.

Lemma treal_eq_trans x y z : treal_eq x y -> treal_eq y z -> treal_eq x z.
Proof.
  unfold treal_eq.
  destruct x as [x1 x2]; destruct y as [y1 y2]; destruct z as [z1 z2]; simpl.
  intros xy yz.
  assert (h: hreal_add (hreal_add x1 z2) (hreal_add y1 y2)
             = hreal_add (hreal_add z1 x2) (hreal_add y1 y2)).
  rewrite hreal_add_ASSOC. rewrite <- (hreal_add_ASSOC z2).
  rewrite (hreal_add_sym _ y2). rewrite <- hreal_add_ASSOC.
  rewrite (hreal_add_sym z2). rewrite xy yz.

  rewrite hreal_add_ASSOC. rewrite (hreal_add_sym (hreal_add z1 x2)).
  rewrite hreal_add_ASSOC. rewrite (hreal_add_sym y2).
  rewrite (hreal_add_sym z1 x2). rewrite hreal_add_ASSOC.
  reflexivity. apply hreal_add_lcancel in h. exact h.
Qed.

Add Relation _ treal_eq
    reflexivity proved by treal_eq_refl
    symmetry proved by treal_eq_sym
    transitivity proved by treal_eq_trans
as treal_eq_rel.

Add Morphism treal_add : treal_add_morph.
Proof.
  intros f f' ff' g g' gg'. unfold treal_eq, treal_add; simpl.
  unfold treal_eq in ff', gg'.
  destruct f as [x1 x2]; destruct f' as [x'1 x'2];
    destruct g as [y1 y2]; destruct g' as [y'1 y'2]; simpl in *.
  rewrite (hreal_add_sym x1). rewrite hreal_add_ASSOC.
  rewrite <- (hreal_add_ASSOC x1). rewrite ff'.
  rewrite (hreal_add_sym x2). rewrite (hreal_add_ASSOC x'1 y'1).
  rewrite <- (hreal_add_ASSOC y'1). rewrite <- gg'.
  rewrite (hreal_add_ASSOC y1). rewrite (hreal_add_sym y'2).
  rewrite <- (hreal_add_ASSOC x'1). rewrite (hreal_add_sym x'1 y1).
  rewrite !hreal_add_ASSOC. reflexivity.
Qed.

(*Add Morphism treal_le
    with signature treal_eq ==> treal_eq ==> iff
      as treal_le_morph.
Proof.
Abort.*)

(*****************************************************************************)
(* HOL-Light definition of real numbers. *)
(*****************************************************************************)

Definition real := quotient treal_eq.

Module Export HL.

Definition mk_real := mk_quotient treal_eq.
Definition dest_real := dest_quotient treal_eq.

Lemma axiom_23 : forall (a : real), (mk_real (dest_real a)) = a.
Proof. exact (mk_dest_quotient treal_eq). Qed.

Lemma axiom_24_aux : forall r, (exists x, r = treal_eq x) -> dest_real (mk_real r) = r.
Proof. exact (dest_mk_aux_quotient treal_eq). Qed.

Lemma axiom_24 : forall (r : (prod hreal hreal) -> Prop), ((fun s : (prod hreal hreal) -> Prop => exists x : prod hreal hreal, s = (treal_eq x)) r) = ((dest_real (mk_real r)) = r).
Proof. exact (dest_mk_quotient treal_eq). Qed.

End HL.
