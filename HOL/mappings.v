From fourcolor.reals Require Import real realcategorical.
(* Importing things in an order so that real.Real does not override important
   definitions. *)
Import real.Real.
From Corelib Require Import Datatypes.
From HB Require Import structures.
From Stdlib Require Import List Reals.Reals Lra Permutation.
From Equations Require Import Equations.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype finset finfun order ssralg ssrnum matrix.
From mathcomp Require Import interval ssrint intdiv archimedean finmap.
From mathcomp Require Import interval_inference all_classical.
From HOLLight Require Import morepointedtypes.
From mathcomp Require Import topology normedtype reals Rstruct_topology derive.
From mathcomp Require Import realfun.
Import preorder.Order Order.TTheory GRing GRing.Theory Num.Theory Logic.
Require Export HOLLight.Real_With_nat.mappings.
From HOLLight.Real_With_nat Require Import terms theorems.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

(*****************************************************************************)
(* Proof that Rocq's R is a fourcolor.model of real numbers. *)
(*****************************************************************************)

Open Scope ring_scope.
Delimit Scope ring_scope with mcR.

Definition Rsup (s : set R) : R := if s = set0 then ε (fun _ => False) else sup s.

Definition R_struct : structure := {|
  Real.val := R;
  Real.le := le;
  Real.sup := Rsup;
  Real.add := add;
  Real.zero := 0;
  Real.opp := opp;
  Real.mul := mul;
  Real.one := 1;
  Real.inv := inv
|}.

Canonical R_struct.

(* Remark: in fourcolor, le is primitive and eq is defined as the
intersection of le and the inverse of le, but in coq, lt is primitive
and le is defined from lt and Logic.eq. *)

Lemma eq_R_struct : @Real.eq R_struct = @eq R.
Proof.
  ext=> [x y [h i]| x y h].
  - by apply le_anti ; apply/andP.
  - subst y. split ; exact: le_refl.
Qed.

Lemma R_ltNge {x y : R} : ((x < y) : Prop) = ~ (y <= x).
Proof.
  rewrite real_ltNge ; try exact:num_real.
  symmetry ; exact: negP**.
Qed.

Lemma R_leNgt {x y : R} : (~(x < y)) = (y <= x).
Proof.
  rewrite R_ltNge. exact:notE.
Qed.

Lemma neqE {A : eqType} {x y : A} : (x <> y) = (x != y).
Proof. by ext ; move/eqP. Qed.

Ltac simp_R_struct := rewrite/Real.set/Real.val/Real.le/Real.sup/Real.add/Real.zero
  /Real.opp/Real.mul/Real.one/Real.inv/R_struct/=-/R_struct-/(set R).

Lemma R_axioms : axioms R_struct.
Proof.
  apply Axioms.
  - exact: le_refl.
  - move/[swap]. exact: le_trans.
  - rewrite/Real.has_sup/Real.has_ub/Real.nonempty/ub. simp_R_struct.
    rewrite/Rsup => E [NemptE boundedE] x Ex.
    have : E <> set0 by apply/eqP/set0P.
    rewrite -is_False => -> ; if_triv.
    by apply reals.ub_le_sup.
  - rewrite/down/has_sup/has_ub/ub/nonempty. simp_R_struct.
    rewrite/Rsup => E x [NemptE boundedE].
    case (pselect (exists2 y : R, E y & x <= y)) ; first tauto.
    move/forall2NP => ubound_E_x ; right. have : E <> set0 by apply/eqP/set0P.
    rewrite -is_False => -> ; if_triv. apply reals.ge_sup ; first by [].
    move => /= y ; case: (ubound_E_x y) => // +_.
    by rewrite -R_ltNge ; move/andP=>[].
  - move=> *; exact: lerD.
  - rewrite eq_R_struct. exact: addrC.
  - rewrite eq_R_struct. exact: addrA.
  - rewrite eq_R_struct. exact: add0r.
  - rewrite eq_R_struct. exact: subrr.
  - move=> * ; exact: ler_wpM2l.
  - rewrite eq_R_struct. exact:mulrC.
  - rewrite eq_R_struct. exact:mulrA.
  - rewrite eq_R_struct. exact: mulrDr.
  - rewrite eq_R_struct. exact: mul1r.
  - move=> ? ; rewrite eq_R_struct eqP** negP** => ? ; exact: divrr.
  - rewrite eq_R_struct eqP** negP**. exact: oner_neq0.
Qed.

Definition R_model : model := {|
  model_structure := R_struct;
  model_axioms := R_axioms;
|}.

Lemma eq_R_model :
  @Real.eq (model_structure R_model) = @eq R.
Proof. exact eq_R_struct. Qed.

(*****************************************************************************)
(* Proof that real is a fourcolor.model of real numbers. *)
(*****************************************************************************)

Lemma real_add_of_num p q :
  real_of_num (p + q) = real_add (real_of_num p) (real_of_num q).
Proof.
  unfold real_of_num, real_add.
  f_equal. rewrite treal_add_of_num. ext=> [x h | x [p' [q' [h1 [h2 h3]]]]].

  exists (treal_of_num p). exists (treal_of_num q). split. exact h. split.
  rewrite axiom_24_aux. reflexivity. exists (treal_of_num p). reflexivity.
  rewrite axiom_24_aux. reflexivity. exists (treal_of_num q). reflexivity.

  rewrite axiom_24_aux in h2. 2: exists (treal_of_num p); reflexivity.
  rewrite axiom_24_aux in h3. 2: exists (treal_of_num q); reflexivity.
  rewrite h2 h3. exact h1.
Qed.

Definition real_sup : (real -> Prop) -> real.
Proof.
  intro P. case (pselect (exists x, P x)); intro h.
  case (pselect (exists M, forall x, (P x) -> real_le x M)); intro i.
  set (Q := fun M => (forall x : real, P x -> real_le x M) /\
                    (forall M' : real, (forall x : real, P x -> real_le x M')
                                  -> real_le M M')).
  exact (ε Q). exact (real_of_num 0). exact (real_of_num 0).
Defined.

Definition real_struct : structure := {|
  Real.val := real;
  Real.le := real_le;
  Real.sup := real_sup;
  Real.add := real_add;
  Real.zero := real_of_num 0;
  Real.opp := real_neg;
  Real.mul := real_mul;
  Real.one := real_of_num 1;
  Real.inv := real_inv
|}.

Canonical real_struct.

Lemma real_sup_is_lub E :
  Real.has_sup E -> ub E (real_sup E) /\ (forall b, ub E b -> real_le (real_sup E) b).
Proof.
  intros [i j]. unfold real_sup.
  case (pselect (exists x : real, E x)) ; last contradiction.
  case (pselect (exists M : real, forall x : real, E x -> real_le x M)) ; last contradiction.
  set (Q := fun M : real =>
              (forall x : real, E x -> real_le x M) /\
                (forall M' : real, (forall x : real, E x -> real_le x M') -> real_le M M')).
  have k: exists M : real, Q M by exact: (thm_REAL_COMPLETE E (conj i j)).
  by case (ε_spec k).
Qed.

Lemma real_sup_upper_bound E : Real.has_sup E -> ub E (real_sup E).
Proof. intro h. apply (proj1 (real_sup_is_lub h)). Qed.

Lemma real_sup_total E x : Real.has_sup E -> Real.down E x \/ real_le (real_sup E) x.
Proof.
  intro h. case (pselect (Real.down E x)); intro k. auto. right.
  generalize (real_sup_is_lub h); intros [i j]. apply j.
  intros y hy.
  rewrite/Real.down exists2E -forallNE in k.
  generalize (k y); intro k'. rewrite not_andE orNp in k'.
  apply thm_REAL_LT_IMP_LE. apply k'. apply hy.
Qed.

Lemma eq_real_struct: @Real.eq real_struct = @eq real.
Proof.
  by ext => x y ; rewrite/Real.eq thm_REAL_LE_ANTISYM.
Qed.

Lemma real_axioms : axioms real_struct.
Proof.
  apply Axioms.
  apply thm_REAL_LE_REFL.
  intros x y z xy yz; apply (thm_REAL_LE_TRANS x y z (conj xy yz)).
  apply real_sup_upper_bound.
  apply real_sup_total.
  intros x y z yz; rewrite -> thm_REAL_LE_LADD; exact yz.
  intros x y. rewrite eq_real_struct. apply thm_REAL_ADD_SYM.
  intros x y z. rewrite eq_real_struct. apply thm_REAL_ADD_ASSOC.
  intro x. rewrite eq_real_struct. apply thm_REAL_ADD_LID.
  intro x. rewrite eq_real_struct. rewrite -> thm_REAL_ADD_SYM. apply thm_REAL_ADD_LINV.
  intros x y z hx yz. apply thm_REAL_LE_LMUL. auto.
  intros x y. rewrite eq_real_struct. apply thm_REAL_MUL_SYM.
  intros x y z. rewrite eq_real_struct. apply thm_REAL_MUL_ASSOC.
  intros x y z. rewrite eq_real_struct. apply thm_REAL_ADD_LDISTRIB.
  intro x. rewrite eq_real_struct. apply thm_REAL_MUL_LID.
  intro x. rewrite eq_real_struct. rewrite -> thm_REAL_MUL_SYM. apply thm_REAL_MUL_LINV.
  by rewrite/= eq_real_struct thm_REAL_OF_NUM_EQ.
Qed.

Definition real_model : model := {|
  model_structure := real_struct;
  model_axioms := real_axioms;
|}.

Lemma eq_real_model:
  @Real.eq (model_structure real_model) = @eq real.
Proof. exact eq_real_struct. Qed.

Definition R_of_real := @Rmorph_to real_model R_model.
Definition real_of_R := @Rmorph_to R_model real_model.

Lemma R_of_real_of_R r : R_of_real (real_of_R r) = r.
Proof. rewrite -eq_R_model. exact: Rmorph_to_inv. Qed.

Lemma real_of_R_of_real (r : real) : real_of_R (R_of_real r) = r.
Proof. rewrite -eq_real_model. exact: Rmorph_to_inv. Qed.

Lemma real_injE x y :  (x = R_of_real y) = (real_of_R x = y).
Proof.
  ext=> ?.
  - by rewrite -(real_of_R_of_real y) ; f_equal.
  - by rewrite -(R_of_real_of_R x) ; f_equal.
Qed.

(*****************************************************************************)
(* Mapping of HOL-Light reals to Rocq reals. *)
(*****************************************************************************)

Definition mk_real : ((prod hreal hreal) -> Prop) -> R := fun x => R_of_real (mk_real x).

Definition dest_real : R -> (prod hreal hreal) -> Prop := fun x => dest_real (real_of_R x).

Lemma axiom_23 : forall (a : R), (mk_real (dest_real a)) = a.
Proof.
  by move=> ? ; rewrite/mk_real/dest_real axiom_23 R_of_real_of_R.
Qed.

Lemma axiom_24_aux : forall r, (exists x, r = treal_eq x) -> dest_real (mk_real r) = r.
Proof.
  intros c [x h]. unfold dest_real, mk_real.
  rewrite real_of_R_of_real -axiom_24.
  exists x. exact h.
Qed.

Lemma axiom_24 : forall (r : (prod hreal hreal) -> Prop), ((fun s : (prod hreal hreal) -> Prop => exists x : prod hreal hreal, s = (treal_eq x)) r) = ((dest_real (mk_real r)) = r).
Proof.
  intro c. unfold dest_real, mk_real. rewrite real_of_R_of_real -axiom_24.
  reflexivity.
Qed.

Lemma real_of_R_morph : morphism real_of_R.
Proof. exact: Rmorph_toP. Qed.

Lemma R_of_real_morph : morphism R_of_real.
Proof. exact: Rmorph_toP. Qed.

Definition ler : R -> R -> Prop := le.
Definition ger (x y : R) : Prop := x >= y.
Definition ltr : R -> R -> Prop := lt.
Definition gtr (x y : R) : Prop := x > y.
Definition addr : R -> R -> R := add.
Definition oppr : R -> R := opp.
Definition subr (x y : R) : R := (x - y)%mcR.
Definition mulr : R -> R -> R := mul.
Definition invr : R -> R := inv.
Definition divr (x y : R) : R := (x/y)%mcR.
Definition expr (r : R) n : R := r ^+ n.
Definition normr : R -> R := Num.norm.
Definition sgr : R -> R := Num.sg.
Definition maxr : R -> R -> R := max.
Definition minr : R -> R -> R := min.

Lemma real_le_def : ler = (fun x1 : R => fun y1 : R => @ε Prop (fun u : Prop => exists x1' : prod hreal hreal, exists y1' : prod hreal hreal, ((treal_le x1' y1') = u) /\ ((dest_real x1 x1') /\ (dest_real y1 y1')))).
Proof.
  funext => x y. rewrite-[X in _ = X]/(real_le (real_of_R x) (real_of_R y)).
  by ext ; case (morph_le real_of_R_morph x y).
Qed.

Lemma real_add_def : addr = (fun x1 : R => fun y1 : R => mk_real (fun u : prod hreal hreal => exists x1' : prod hreal hreal, exists y1' : prod hreal hreal, (treal_eq (treal_add x1' y1') u) /\ ((dest_real x1 x1') /\ (dest_real y1 y1')))).
Proof.
  ext=> x y.
  rewrite -[X in _ = X]/(R_of_real (real_add (real_of_R x) (real_of_R y))).
  rewrite real_injE -eq_real_model. exact: (Real.morph_add real_of_R_morph).
Qed.

Lemma real_mul_def : mulr = (fun x1 : R => fun y1 : R => mk_real (fun u : prod hreal hreal => exists x1' : prod hreal hreal, exists y1' : prod hreal hreal, (treal_eq (treal_mul x1' y1') u) /\ ((dest_real x1 x1') /\ (dest_real y1 y1')))).
Proof.
  ext=> x y.
  rewrite -[X in _ = X]/(R_of_real (real_mul (real_of_R x) (real_of_R y))).
  rewrite real_injE -eq_real_model. exact: (Real.morph_mul real_of_R_morph).
Qed.

Lemma zero_eq : 0 = R_of_real (real_of_num 0).
Proof.
  rewrite real_injE -eq_real_model. exact: (morph_zero real_of_R_morph).
Qed.

Lemma real_inv_def : invr = (fun x : R => mk_real (fun u : prod hreal hreal => exists x' : prod hreal hreal, (treal_eq (treal_inv x') u) /\ (dest_real x x'))).
Proof.
  ext=> x. rewrite -[X in _ = X]/(R_of_real (real_inv (real_of_R x))).
  rewrite real_injE. case (EM (x = 0)) => [->|h].
  - by rewrite/invr invr0 zero_eq real_of_R_of_real thm_REAL_INV_0.
  - rewrite -eq_real_model. apply (morph_inv real_of_R_morph).
    rewrite eq_R_model. exact h.
Qed.

Lemma real_neg_def : oppr = (fun x1 : R => mk_real (fun u : prod hreal hreal => exists x1' : prod hreal hreal, (treal_eq (treal_neg x1') u) /\ (dest_real x1 x1'))).
Proof.
  ext=> x. rewrite -[X in _ = X]/(R_of_real (real_neg (real_of_R x))).
  rewrite real_injE -eq_real_model. exact: (Real.morph_opp real_of_R_morph).
Qed.

Lemma one_eq : 1%R = R_of_real (real_of_num 1).
Proof.
  rewrite real_injE -eq_real_model. exact: (morph_one real_of_R_morph).
Qed.

Definition R_of_nat (n : nat) : R := n%:R.

Lemma real_of_num_def : R_of_nat = (fun m : nat => mk_real (fun u : prod hreal hreal => treal_eq (treal_of_num m) u)).
Proof.
  ext=>n. rewrite/R_of_nat/mk_real-/(real_of_num n).
  induction n ; first exact: zero_eq.
  rewrite/R_of_nat-addn1 natrD IHn -thm_REAL_OF_NUM_ADD one_eq sym -eq_R_model.
  exact:(Real.morph_add R_of_real_morph).
Qed.

Lemma real_abs_def :
  normr = (fun y0 : R => @COND R (ler (R_of_nat (NUMERAL 0)) y0) y0 (oppr y0)).
Proof.
  ext=> /= r ; rewrite/ler/normr ; if_intro => ?.
  - by rewrite ger0_norm.
  - by rewrite ltr0_norm ?R_ltNge.
Qed.

Lemma real_div_def : divr = (fun y0 : R => fun y1 : R => mulr y0 (invr y1)).
Proof. reflexivity. Qed.

Lemma real_sub_def : subr = (fun y0 : R => fun y1 : R => addr y0 (oppr y1)).
Proof. reflexivity. Qed.

Lemma real_ge_def : ger = (fun y0 : R => fun y1 : R => ler y1 y0).
Proof. reflexivity. Qed.

Lemma real_lt_def : ltr = (fun y0 : R => fun y1 : R => ~ (ler y1 y0)).
Proof.
  funext => x y. exact: R_ltNge.
Qed.

Lemma real_gt_def : gtr = (fun y0 : R => fun y1 : R => ltr y1 y0).
Proof. reflexivity. Qed.

Lemma real_max_def : max = (fun y0 : R => fun y1 : R => @COND R (ler y0 y1) y1 y0).
Proof.
  ext=> x y. if_intro.
  - rewrite/max lt_neqAle => ->.
    case (EM (x=y)) ; last by move/eqP=>->.
    by move =>-> ; rewrite eqtype.eq_refl.
  - by move/negP/negbTE ; rewrite/max lt_neqAle Bool.andb_comm => ->.
Qed.

Lemma real_min_def : min = (fun y0 : R => fun y1 : R => @COND R (ler y0 y1) y0 y1).
Proof.
  ext=> x y. if_intro.
  - rewrite/min lt_neqAle => ->.
    case (EM (x=y)) ; last by move/eqP=>->.
    by move =>-> ; rewrite eqtype.eq_refl.
  - by move/negP/negbTE ; rewrite/min lt_neqAle Bool.andb_comm => ->.
Qed.

Lemma real_pow_def : expr = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> R -> nat -> R) (fun expr' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> R -> nat -> R => forall _24085 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))), (forall x : R, (expr' _24085 x (NUMERAL O)) = (R_of_nat (NUMERAL (BIT1 O)))) /\ (forall x : R, forall n : nat, (expr' _24085 x (S n)) = (mulr x (expr' _24085 x n)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 O)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 O)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 O)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 O)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 O)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 O)))))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 O)))))))))))))))).
Proof.
  by total_align => * ; rewrite/expr // exprS.
Qed.

Variant sgr_spec (r : R) : R -> R -> Type :=
  | sgr_pos_spec : (0 < r)%mcR -> sgr_spec r r 1%mcR
  | sgr_neg_spec : (r < 0)%mcR -> sgr_spec r r (-1)%mcR
  | sgr0_spec : sgr_spec r 0 0.

Lemma sgr_elim (r : R) : sgr_spec r r (sgr r).
Proof.
  rewrite/sgr. case (pselect (0<r)).
    { move/[dup]/gtr0_sg =>-> ; exact: sgr_pos_spec. }
  case (pselect (r<0)%mcR).
    { move/[dup]/ltr0_sg =>-> + _ ; exact: sgr_neg_spec. }
  rewrite 2!R_leNgt => ? ?; have -> : r = 0 by apply le_anti ; apply/andP.
  rewrite sgr0 ; exact:sgr0_spec.
Qed.

Lemma real_sgn_def : sgr = (fun _26598 : R => @COND R (ltr (R_of_nat (NUMERAL O)) _26598) (R_of_nat (NUMERAL (BIT1 O))) (@COND R (ltr _26598 (R_of_nat (NUMERAL O))) (oppr (R_of_nat (NUMERAL (BIT1 O)))) (R_of_nat (NUMERAL O)))).
Proof.
  rewrite/COND/ltr ; ext => /= r ; case (sgr_elim r).
  - by move=>? ; if_triv.
  - move=> neg_0 ; rewrite if_triv_False ; first by if_triv.
    by move/(lt_trans neg_0) ; rewrite lt_irreflexive.
  - by rewrite lt_irreflexive ; do 2 if_triv.
Qed.

Lemma inj_square_pos (r r' : R) : r ^+ 2 = r' ^+ 2 ->
  (0 < r)%mcR -> (0 < r')%mcR -> r = r'.
Proof.
  move=> eqsq pos_r pos_r'. apply: (@pexpIrn _ 2%N).
  - by [].
  - by move: pos_r ; rewrite lt_neqAle -andP** => -[].
  - by move: pos_r' ; rewrite lt_neqAle -andP** => -[].
  - by [].
Qed.

Definition hol_sqrt (r : R) := if 0 <= r then Num.sqrt r else -Num.sqrt (-r).

Lemma sqrt_def : hol_sqrt = (fun _27149 : R => @ε R (fun y : R => ((sgr y) = (sgr _27149)) /\ ((expr y ((BIT0 (BIT1 O)))) = (normr _27149)))).
Proof.
  funext=> /= r. align_ε.
  - rewrite/hol_sqrt -(asboolb (0 <= r)%mcR).
    apply if_intro with (P := fun r' => sgr r' = sgr r /\ expr r' 2 = `|r|);
    [move=>pos_r | rewrite -R_ltNge => neg_r] ; split.
    + case (pselect (r = 0)) => [-> | neq_r_0] ; first by rewrite sqrtr0.
      have spos_r : 0 < r by rewrite lt_neqAle -andP** -negP** -eqP** sym.
      by rewrite/sgr !gtr0_sg // sqrtr_gt0.
    + rewrite/expr; case (sqrtrP r); [by rewrite R_ltNge|] => /={}r{}pos_r.
      rewrite ger0_norm ; [exact: erefl | exact: sqr_ge0].
    + rewrite/sgr ltr0_sg ; first by rewrite ltr0_sg ?RltE.
      by rewrite oppr_lt0 sqrtr_gt0 -oppr_lt0 opprK.
    + rewrite/expr -{2}(opprK r). set k := -r. case (sqrtrP (k)) => /=.
      * rewrite oppr_lt0 => pos_r. have := lt_trans neg_r pos_r.
        by rewrite lt_irreflexive.
      * move =>{k neg_r}r pos_r.
        rewrite sqrrN normrN ger0_norm ; [exact: erefl | exact: sqr_ge0].
  - set (s_r := hol_sqrt r : R) ; move=> s_r' [<- <-] [].
    rewrite/expr ; case (sgr_elim s_r) ; case (sgr_elim s_r') => //=.
    2-4,6-8: cbn ; lra.
    + by move=> * ; apply inj_square_pos.
    + move=> neg_s_r' neg_s_r _ ; rewrite -sqrrN -(sqrrN s_r) => eqsq.
      by apply oppr_inj ; apply inj_square_pos ; rewrite ?oppr_gt0.
Qed.

(*****************************************************************************)
(* Mapping of integers. *)
(*****************************************************************************)

Open Scope int_scope.
HB.instance Definition _ := isPointed.Build int 0.

Definition int_of_real : R -> int := Num.floor.
Definition real_of_int : int -> R := intr.
Definition lez : int -> int -> Prop := le.
Definition gez (x y : int) : Prop := x >= y.
Definition ltz : int -> int -> Prop := lt.
Definition gtz (x y : int) : Prop := x > y.
Definition addz : int -> int -> int := add.
Definition oppz : int -> int := opp.
Definition subz (x y : int) : int := x-y.
Definition mulz : int -> int -> int := mul.
Definition expz (r : int) n : int := r ^+ n.
Definition normz : int -> int := Num.norm.
Definition sgz : int -> int := Num.sg.
Definition maxz : int -> int -> int := max.
Definition minz : int -> int -> int := min.

Lemma axiom_25 : forall (a : int), (int_of_real (real_of_int a)) = a.
Proof. exact: intrKfloor. Qed.

Definition Rint (r : R) : Prop := r \is a Num.int.

Lemma integer_def : Rint = (fun _28715 : R => exists n : nat, (normr _28715) = (R_of_nat n)).
Proof.
  ext => r ; rewrite/Rint intrE -orP** -2!natrP**.
  - move=>[[n ->]|[n nreq]]; exists n ; first by rewrite/normr normr_nat.
    by rewrite/normr -(opprK r) normrN nreq normr_nat.
  - case=>n; rewrite/normr eqP** eqr_norml-andP**-orP**-2!eqP**=> -[[->|->] _].
    + by left ; exists n.
    + by right ; exists n ; rewrite opprK.
Qed.

Lemma axiom_26 : forall (r : R), ((fun x : R => Rint x) r) = ((real_of_int (int_of_real r)) = r).
Proof.
  by move=>r ; rewrite/Rint intrEfloor -eqP**.
Qed.

Definition int_of_nat n : int := n%:Z.

Lemma floor_natz {R : archiNumDomainType} (n : nat) : @Num.floor R n%:R = n.
Proof.
  by rewrite pmulrn intrKfloor.
Qed.

Lemma int_of_num_def : int_of_nat = (fun _28789 : nat => int_of_real (R_of_nat _28789)).
Proof.
  by ext => n ; rewrite/R_of_nat/int_of_real floor_natz.
Qed.

Lemma int_le_def :
  lez = (fun _28741 : int => fun _28742 : int => ler (real_of_int _28741) (real_of_int _28742)).
Proof.
  by funext =>* ; rewrite/ler/real_of_int ler_int.
Qed.

Lemma int_lt_def :
  ltz = (fun _28753 : int => fun _28754 : int => ltr (real_of_int _28753) (real_of_int _28754)).
Proof.
  by funext =>* ; rewrite/ltr/real_of_int ltr_int.
Qed.

Lemma int_ge_def :
  gez = (fun _28765 : int => fun _28766 : int => ger (real_of_int _28765) (real_of_int _28766)).
Proof.
  by funext =>* ; rewrite/ger/real_of_int ler_int.
Qed.

Lemma int_gt_def :
  gtz = (fun _28777 : int => fun _28778 : int => gtr (real_of_int _28777) (real_of_int _28778)).
Proof.
  by funext =>* ; rewrite/gtr/real_of_int ltr_int.
Qed.

Lemma int_neg_def :
  oppz = (fun _28794 : int => int_of_real (oppr (real_of_int _28794))).
Proof.
  by ext=>* ; rewrite/oppr/real_of_int/int_of_real -intrN intrKfloor.
Qed.

Lemma int_add_def :
  addz = (fun _28803 : int => fun _28804 : int => int_of_real (addr (real_of_int _28803) (real_of_int _28804))).
Proof.
  by ext=>* ; rewrite/addr/real_of_int/int_of_real -intrD intrKfloor.
Qed.

Lemma int_sub_def :
  subz = (fun _28835 : int => fun _28836 : int => int_of_real (subr (real_of_int _28835) (real_of_int _28836))).
Proof.
  by ext=>* ; rewrite/subr/real_of_int/int_of_real -intrB intrKfloor.
Qed.

Lemma int_mul_def :
  mulz =
  (fun _28847 : int => fun _28848 : int => int_of_real (mulr (real_of_int _28847) (real_of_int _28848))).
Proof.
  by ext=>* ; rewrite/mulr/real_of_int/int_of_real -intrM intrKfloor.
Qed.

Lemma int_abs_def :
  normz = (fun _28867 : int => int_of_real (normr (real_of_int _28867))).
Proof.
  by ext=>* ; rewrite/normr/real_of_int/int_of_real -intr_norm intrKfloor.
Qed.

Lemma int_sgn_def :
  sgz = (fun _28878 : int => int_of_real (sgr (real_of_int _28878))).
Proof.
  by ext=>* ; rewrite/sgr/real_of_int/int_of_real -intr_sg intrKfloor.
Qed.

Lemma intr_max (R : numDomainType) (n m : int) :
  @intmul R 1 (max n m) = max n%:~R m%:~R.
Proof.
  by rewrite/max ltr_int ; case (n<m).
Qed.

Lemma intr_min (R : numDomainType) (n m : int) :
  @intmul R 1 (min n m) = min n%:~R m%:~R.
Proof.
  by rewrite/min ltr_int ; case (n<m).
Qed.

Lemma int_max_def :
  maxz = (fun _28938 : int => fun _28939 : int => int_of_real (maxr (real_of_int _28938) (real_of_int _28939))).
Proof.
  by ext=>* ; rewrite/maxr/real_of_int/int_of_real -intr_max intrKfloor.
Qed.

Lemma int_min_def :
  minz = (fun _28956 : int => fun _28957 : int => int_of_real (minr (real_of_int _28956) (real_of_int _28957))).
Proof.
  by ext=>* ; rewrite/minr/real_of_int/int_of_real -intr_min intrKfloor.
Qed.

Lemma intr_exp (R : pzRingType) (z : int) (n : nat) :
  @intmul R 1 (z ^+ n) = z%:~R ^+ n.
Proof.
  by elim:n=>[|n IHn] ; [rewrite expr0 | rewrite 2!exprS intrM IHn].
Qed.

Lemma int_pow_def :
  expz = (fun _28974 : int => fun _28975 : nat => int_of_real (expr (real_of_int _28974) _28975)).
Proof.
  by ext=>* ; rewrite/expr/real_of_int/int_of_real -intr_exp intrKfloor.
Qed.

Lemma div_def :
  divz = (@ε ((prod nat (prod nat nat)) -> int -> int -> int) (fun q : (prod nat (prod nat nat)) -> int -> int -> int => forall _29326 : prod nat (prod nat nat), exists r : int -> int -> int, forall m : int, forall n : int, @COND Prop (n = (int_of_nat (NUMERAL O))) (((q _29326 m n) = (int_of_nat (NUMERAL O))) /\ ((r m n) = m)) ((lez (int_of_nat (NUMERAL O)) (r m n)) /\ ((ltz (r m n) (normz n)) /\ (m = (addz (mulz (q _29326 m n) n) (r m n)))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 O)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 O)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 O))))))))))).
Proof.
  rewrite/ltz/normz/addz/mulz/int_of_nat/lez/=. align_ε.
  - exists modz => n m ; if_intro.
    + move=>-> ; split ; [exact: divz0 | exact: modz0].
    + move/eqP; repeat split; [exact: modz_ge0|exact: ltz_mod|exact: divz_eq].
  - move=> div _ [rem div_def] ; ext=> m n ; specialize (div_def m n).
    eapply if_elim with (1 := div_def) ; first (move=>->[-> _] ; exact: divz0).
    move=> ? [? [? {1}->]]; rewrite divzMDl ; last by apply/eqP.
    by rewrite divz_small -?andP** ?addr0.
Qed.

Lemma rem_def :
  modz = (@ε ((prod nat (prod nat nat)) -> int -> int -> int) (fun r : (prod nat (prod nat nat)) -> int -> int -> int => forall _29327 : prod nat (prod nat nat), forall m : int, forall n : int, @COND Prop (n = (int_of_nat (NUMERAL O))) (((divz m n) = (int_of_nat (NUMERAL O))) /\ ((r _29327 m n) = m)) ((lez (int_of_nat (NUMERAL O)) (r _29327 m n)) /\ ((ltz (r _29327 m n) (normz n)) /\ (m = (addz (mulz (divz m n) n) (r _29327 m n)))))) (@pair nat (prod nat nat) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 O)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 O)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 O))))))))))).
Proof.
  rewrite/ltz/normz/addz/mulz/int_of_nat/lez/=. align_ε.
  - move=> n m ; if_intro.
    + move=>-> ; split ; [exact: divz0 | exact: modz0].
    + move/eqP; repeat split; [exact: modz_ge0|exact: ltz_mod|exact: divz_eq].
  - move=> rem _ rem_def ; ext => n m ; specialize (rem_def n m).
    eapply if_elim with (1 := rem_def) ; first(move=>->[_ ->]; exact:modz0).
    by move => ? [? [? {1}->]] ; rewrite modzMDl -modz_abs modz_small -?andP**.
Qed.

(* I have not found a notion of congruence modulo a submodule in mathcomp *)

Definition congruent_modz {R : pzRingType} (a b c : R) :=
  exists k : int, b - c = a *~ k.

Notation "x = y %[modz z ]" := (congruent_modz z x y) : ring_scope.

Definition congruent_modzr : R -> R -> R -> Prop := congruent_modz.

Lemma real_mod_def :
  congruent_modzr = (fun _29623 : R => fun _29624 : R => fun _29625 : R => exists q : R, (Rint q) /\ ((subr _29624 _29625) = (mulr q _29623))).
Proof.
  ext=> a b c; rewrite/congruent_modzr/congruent_modz.
  - case=> k e ; exists (real_of_int k) ; split ; first exact: intr_int.
    by rewrite/mulr/real_of_int mulrzl.
  - by case=>?; rewrite/Rint -intrP**=> -[[k ->] ?]; exists k; rewrite -mulrzl.
Qed.

Definition dividez d n : Prop := d %| n.

Lemma int_divides_def :
  dividez = (fun _29644 : int => fun _29645 : int => exists x : int, _29645 = (mulz _29644 x)).
Proof.
  funext=>a b. have ->: ((exists x, b = mulz a x) = exists x, b = x * a).
  - by ext => -[x] ; rewrite/mulz mulrC ; exists x.
  - symmetry ; exact: dvdzP**.
Qed.

Definition pair_coprimez : int * int -> Prop := uncurry coprimez.

Lemma int_coprime_def :
  pair_coprimez = (fun _29691 : prod int int => exists x : int, exists y : int, (addz (mulz (@fst int int _29691) x) (mulz (@snd int int _29691) y)) = (int_of_nat (NUMERAL (BIT1 O)))).
Proof.
  funext =>-[n m]. unshelve eapply (eq_trans (eq_sym (coprimezP _ _)**)). ext.
  - by case=>-[/= u v] ? ; exist u v ; rewrite/mulz (mulrC m) (mulrC n).
  - by case=>u [v ?] ; exists (u,v) ; rewrite/= (mulrC u) (mulrC v).
Qed.

Definition pair_gcdz := uncurry gcdz.

Lemma absz_pos_inj (n m : int) : 0 <= n -> 0 <= m -> absz n = absz m -> n = m.
Proof.
  by case:n => // ; case:m => // ? ? _ _ ; rewrite 2!absz_nat=>->.
Qed.

Lemma dvdz_pos_antisym (n m : int) :
  0 <= n -> 0 <= m -> n %| m -> m %| n -> n = m.
Proof.
  move=>*; apply:absz_pos_inj=> //; apply:Order.NatDvd.dvdn_anti; exact/andP.
Qed.

Lemma natz_lt0 (n : nat) : (n%:Z <= 0) = (n == 0%nat).
Proof.
  by case n.
Qed.

Lemma absz_neg_inj (n m : int) : n <= 0 -> m <= 0 -> absz n = absz m -> n = m.
Proof.
  case:n; case:m => n m ; rewrite ?natz_lt0 -?eqP** ; first by move=> -> ->.
  - by move=> -> ; rewrite absz0 sym eqP** absz_eq0 -eqP** sym.
  - by move=> _ -> ; rewrite absz0 eqP** absz_eq0 -eqP** sym.
  - by rewrite 6!(NegzE,abszN,absz_nat) => _ _ ->.
Qed.

Lemma dvdz_neg_antisym (n m : int) :
  n <= 0 -> m <= 0 -> n %| m -> m %| n -> n = m.
Proof.
  move=>*; apply:absz_neg_inj=> //; apply:Order.NatDvd.dvdn_anti; exact/andP.
Qed.

Lemma int_gcd_def :
  pair_gcdz = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> (prod int int) -> int) (fun d : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> (prod int int) -> int => forall _30960 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))), forall a : int, forall b : int, (lez (int_of_nat (NUMERAL O)) (d _30960 (@pair int int a b))) /\ ((dividez (d _30960 (@pair int int a b)) a) /\ ((dividez (d _30960 (@pair int int a b)) b) /\ (exists x : int, exists y : int, (d _30960 (@pair int int a b)) = (addz (mulz a x) (mulz b y)))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 O)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 O)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 O)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 O)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 O)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 O))))))))))))))).
Proof.
  rewrite/pair_gcdz/lez/int_of_nat/dividez/addz/mulz/=. align_ε.
  - move=>n m /= ; repeat split ; [exact:dvdz_gcdl|exact:dvdz_gcdr|].
    case (Bezoutz n m)=>u [v <-] ; exist u v ; f_equal ; exact:mulrC.
  - move=> gcd _ gcd_def ; ext => -[a b /=].
    case:(gcd_def a b)=> {gcd_def}gcd_pos [gcd_dvdl] [gcd_dvdr] [u] [v] bezout.
    apply:dvdz_pos_antisym;[by[]|exact: gcd_pos| |by rewrite dvdz_gcd -andP**].
    rewrite bezout; apply intdiv.GRing_isZmodClosed__to__Algebra_isAddClosed.
     + apply dvdz_mulr ; exact: dvdz_gcdl.
     + apply dvdz_mulr ; exact: dvdz_gcdr.
Qed.

Definition pair_lcmz := uncurry lcmz.

Lemma int_lcm_def :
  pair_lcmz = (fun y0 : prod int int => @COND int ((mulz (@fst int int y0) (@snd int int y0)) = (int_of_nat (NUMERAL O))) (int_of_nat (NUMERAL O)) (divz (normz (mulz (@fst int int y0) (@snd int int y0))) (pair_gcdz (@pair int int (@fst int int y0) (@snd int int y0))))).
Proof.
  rewrite/mulz/int_of_nat/pair_gcdz/normz/COND ; ext => -[a b] /=.
  if_intro ; last by rewrite divz_nat abszM.
  move/intUnitRing.idomain_axiomz/orP=> -[]/eqP -> ; [exact:lcm0z|exact:lcmz0].
Qed.

Close Scope int_scope.

(*****************************************************************************)
(* Sets. *)
(*****************************************************************************)

Open Scope classical_set_scope.
Import classical_sets.

Definition IN (A : Type) (a : A) (s : set A) : Prop := in_set s a.

Lemma IN_def {A : Type'} : @IN A = (fun _32317 : A => fun _32318 : A -> Prop => _32318 _32317).
Proof.
  exact (funext (fun a => funext (fun s => in_setE s a))).
Qed.

Lemma EMPTY_def (A : Type') : set0 = (fun x : A => False).
Proof.
  ext=>x H ; inversion H.
Qed.

Definition INSERT (A : Type) (a : A) s := a |` s.

Lemma INSERT_def (A : Type') : @INSERT A = (fun _32373 : A => fun _32374 : A -> Prop => fun y : A => (@IN A y _32374) \/ (y = _32373)).
Proof.
  by ext=>a E a'; rewrite thm_DISJ_SYM IN_def.
Qed.

Lemma UNIV_def (A : Type') : [set : A] = (fun x : A => True).
Proof. reflexivity. Qed.

Definition GSPEC (A : Type') := @id (set A).

Lemma GSPEC_def (A : Type') : @GSPEC A = (fun _32329 : A -> Prop => _32329).
Proof. reflexivity. Qed.

Definition SETSPEC (A : Type) (x : A) P := [set x' | P /\ x=x'].

Lemma SETSPEC_def (A : Type') : (@SETSPEC A) = (fun _32334 : A => fun _32335 : Prop => fun _32336 : A => _32335 /\ (_32334 = _32336)).
Proof. exact erefl. Qed.

(* Eliminating useless GSPEC and SETSPEC combination *)
Lemma SPEC_elim (A : Type') {P : A -> Prop} : GSPEC (fun x => exists x', SETSPEC x (P x') x') = P.
Proof.
  ext=> x H. destruct H as (x', (HP , e)). now subst x'.
  now exists x.
Qed.

Lemma SUBSET_def (A : Type') : subset = (fun _32443 : A -> Prop => fun _32444 : A -> Prop => forall x : A, (@IN A x _32443) -> @IN A x _32444).
Proof. now rewrite IN_def. Qed.

Lemma UNION_def (A : Type') : setU = (fun _32385 : A -> Prop => fun _32386 : A -> Prop => @GSPEC A (fun GEN_PVAR_0 : A => exists x : A, @SETSPEC A GEN_PVAR_0 ((@IN A x _32385) \/ (@IN A x _32386)) x)).
Proof.
  by ext=> B C x ; rewrite SPEC_elim IN_def.
Qed.

Lemma INTER_def (A : Type') : setI = (fun _32402 : A -> Prop => fun _32403 : A -> Prop => @GSPEC A (fun GEN_PVAR_2 : A => exists x : A, @SETSPEC A GEN_PVAR_2 ((@IN A x _32402) /\ (@IN A x _32403)) x)).
Proof.
  by ext=> B C x ; rewrite SPEC_elim IN_def.
Qed.

Definition UNIONS (A : Type') (s : set (set A)) :=
  [set a | exists s0, in_set s s0 /\ in_set s0 a].

Lemma UNIONS_def (A : Type') : (@UNIONS A) = (fun _32397 : (A -> Prop) -> Prop => @GSPEC A (fun GEN_PVAR_1 : A => exists x : A, @SETSPEC A GEN_PVAR_1 (exists u : A -> Prop, (@IN (A -> Prop) u _32397) /\ (@IN A x u)) x)).
Proof.
  apply funext=>s. symmetry. exact SPEC_elim.
Qed.

Definition INTERS (A : Type') (s : set (set A)) :=
  [set a | forall s0, in_set s s0 -> in_set s0 a].

Lemma INTERS_def (A : Type') : @INTERS A = (fun _32414 : (A -> Prop) -> Prop => @GSPEC A (fun GEN_PVAR_3 : A => exists x : A, @SETSPEC A GEN_PVAR_3 (forall u : A -> Prop, (@IN (A -> Prop) u _32414) -> @IN A x u) x)).
Proof.
  apply funext => E. symmetry. exact SPEC_elim.
Qed.

Definition IMAGE {A B : Type} (f : A -> B) s := [set (f x) | x in s].

Lemma IMAGE_def {A B : Type'} : (@IMAGE A B) = (fun _32493 : A -> B => fun _32494 : A -> Prop => @GSPEC B (fun GEN_PVAR_7 : B => exists y : B, @SETSPEC B GEN_PVAR_7 (exists x : A, (@IN A x _32494) /\ (y = (_32493 x))) y)).
Proof.
  ext 3 => f E b. unfold IMAGE,image. simpl. rewrite SPEC_elim exists2E.
  apply prop_ext ; intros (a, (H,H')) ; rewrite -> IN_def in * ; eauto.
Qed.

(* Variant *)
Lemma SPEC_IMAGE {A B : Type'} {f : A -> B} {s : set A} :
  GSPEC (fun x => exists x', SETSPEC x (IN x' s) (f x')) = [set (f x) | x in s].
Proof. fold (IMAGE f s). now rewrite IMAGE_def SPEC_elim. Qed.

Lemma DIFF_def (A : Type') : setD = (fun _32419 : A -> Prop => fun _32420 : A -> Prop => @GSPEC A (fun GEN_PVAR_4 : A => exists x : A, @SETSPEC A GEN_PVAR_4 ((@IN A x _32419) /\ (~ (@IN A x _32420))) x)).
Proof.
  by ext=> B C ; rewrite SPEC_elim IN_def.
Qed.

Definition DELETE (A : Type') s (a : A) := s `\ a.

Lemma DELETE_def (A : Type') : @DELETE A = (fun _32431 : A -> Prop => fun _32432 : A => @GSPEC A (fun GEN_PVAR_6 : A => exists y : A, @SETSPEC A GEN_PVAR_6 ((@IN A y _32431) /\ (~ (y = _32432))) y)).
Proof.
  by ext=> s a ; rewrite SPEC_elim IN_def.
Qed.

Lemma PSUBSET_def (A : Type') : proper = (fun _32455 : A -> Prop => fun _32456 : A -> Prop => (@subset A _32455 _32456) /\ (~ (_32455 = _32456))).
Proof.
  ext 2 => s s'. rewrite properEneq thm_CONJ_SYM. f_equal.
  now rewrite <- asboolE, asbool_neg.
Qed.

Definition DISJOINT T : set T -> set T -> Prop := disj_set.

Lemma DISJOINT_def (A : Type') : @DISJOINT A = (fun _32467 : A -> Prop => fun _32468 : A -> Prop => (@setI A _32467 _32468) = (@set0 A)) :> (set A -> set A -> Prop).
Proof.
  by ext 2 => B C ; rewrite <- asboolE.
Qed.

Definition is_set1 (A : Type) (s : set A) := exists a, s = [set a].

Lemma SING_def (A : Type') : @is_set1 A = (fun _32479 : A -> Prop => exists x : A, _32479 = (@INSERT A x (@set0 A))).
Proof.
  ext => s [x H] ; exists x.
  by rewrite/INSERT setU0. by rewrite/INSERT setU0 in H.
Qed.

(* pattern /3= simplifies HOL_Light set objects to rocq ones in, I believe,
   the most suitable way. Maybe it would be better for some to unfold IN
   as the boolean predicate instead of rewriting it to the Prop one. *)
Ltac ssrsimpl3 :=
  rewrite ?SPEC_IMAGE?SPEC_elim/GSPEC/SETSPEC/DELETE/IMAGE/INTERS/UNIONS/
  INSERT/BIT1/BIT0/NUMERAL?setU0?IN_def.

(*****************************************************************************)
(* Finite sets. *)
(*****************************************************************************)

(* mathcomp : in bijection with {0 ; ... ; n-1} for some n *)

Lemma FINITE_def (A : Type') : finite_set = (fun a : A -> Prop => forall FINITE' : (A -> Prop) -> Prop, (forall a' : A -> Prop, ((a' = (@set0 A)) \/ (exists x : A, exists s : A -> Prop, (a' = (@INSERT A x s)) /\ (FINITE' s))) -> FINITE' a') -> FINITE' a).
Proof.
  move=>/3= ; ind_align.
  - revert x H ; elim:x0=>[s|n IHn s /eq_cardSP [a sa s_min_a]].
    by rewrite II0 card_eq0 => /eqP-> ; left.
    right ; exist a (s `\ a) ; split ; first by rewrite setD1K.
    exact (H' _ (IHn _ s_min_a)).
  - by rewrite finite_setU.
Qed.

(* Inductive version, like the one in HOL-Light and in Rocq's Stdlib : *)
Inductive finite' (A : Type) : set A -> Prop :=
|finite'_set0 : finite' set0
|finite'_setU1 s a : finite' s -> finite' (a |` s).

Lemma finite_setE (A : Type') : finite_set = @finite' A.
Proof. by symmetry ; rewrite FINITE_def ; ind_align. Qed.

(* Version using lists *)
Open Scope list_scope.
Definition set_of_list (A : Type') (l : seq A) : A -> Prop := [set` l].

Lemma set_cons (A : Type') (a : A) (s : seq A) :
  [set` a::s] = a |` [set` s].
Proof.
  rewrite predeqP /= => x.
  rewrite in_cons ; split ; first move/orP ; move => [Hxa | Hxl] ; only 2 : by auto.
  - by left ; apply/eqP :Hxa.
  - by rewrite Hxa -orP** ; left.
  - by rewrite Hxl Bool.orb_comm.
Qed.

Lemma set_of_list_def (A : Type') : (@set_of_list A) = (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (list A) -> A -> Prop) (fun set_of_list' : (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))) -> (list A) -> A -> Prop => forall _56425 : prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))), ((set_of_list' _56425 (@nil A)) = (@set0 A)) /\ (forall h : A, forall t : list A, (set_of_list' _56425 (@cons A h t)) = (@INSERT A h (set_of_list' _56425 t)))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 O)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 O)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 O)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 O)))))))) (@pair nat (prod nat (prod nat (prod nat (prod nat nat)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 O)))))))) (@pair nat (prod nat (prod nat (prod nat nat))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 O)))))))) (@pair nat (prod nat (prod nat nat)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 O)))))))) (@pair nat (prod nat nat) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 O)))))))) (@pair nat nat (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 O)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 O))))))))))))))))))).
Proof.
  by move=>/3= ; total_align; first apply set_nil ; last apply set_cons.
Qed.

(* Can be usefull for some finiteness proofs. *)
Lemma finite_seqE {T : eqType} A :
   finite_set A = exists s : list T, A = [set` s].
Proof. apply propext ; exact (finite_seqP A). Qed.

Lemma finite_witness (A : Type') (l : list A) (s : set A) : s = [set` l] -> finite_set s.
Proof. by rewrite/set_of_list=>->. Qed.

Arguments finite_witness {_} _.

Lemma in_In (A : eqType) (x : A) (s : seq A) : (x \in s) = In x s :> Prop.
Proof.
  ext ; elim:s=>[|a s IHs] //= H.
  - by move/orP:H=>[Hax | ?] ; first move/eqP:Hax=>-> ; auto.
  - by rewrite in_cons ; case:H=>[-> | ?] ; apply/orP ; auto.
Qed.

Lemma uniq_NoDup (A : eqType) (l : list A) : uniq l = NoDup l :> Prop.
Proof.
  ext ; elim:l=>[|a l IHl] //= H.
  - by apply NoDup_nil.
  - apply NoDup_cons ; move/andP:H ; last by move=>[_ H] ; auto.
    by rewrite -in_In =>[[H _]] ; apply/negP.
  - inversion_clear H ; apply/andP ; split ; last by auto.
    by apply/negP ; rewrite in_In.
Qed.

Definition list_of_set (A : Type') (s : set A) : list A :=
  ε (fun s' : seq A => [set` s'] = s /\ uniq s').

Notation "[ 'list' 'of' s ]" := (list_of_set s) (format "[ 'list'  'of'  s ]") : classical_set_scope.

Lemma list_of_set_spec (A:Type') (s : set A) (H : finite_set s):
  [set` [list of s]] = s /\ uniq (list_of_set s).
Proof.
  rewrite finite_setE in H ; rewrite/list_of_set.
  match goal with [|- [set` (ε ?Q)] = _ /\ _] => have ex : exists l, Q l end.
  - elim: {s}H => [|s a _ [l [<- ndl]]]; first by exists nil; rewrite set_nil.
    case: (EM (a \in l))=>H.
    + exists l ; split ; last by assumption.
      by rewrite predeqP =>x /= ; split ; first auto ; last move=>[->|].
    + exists (a::l) ; rewrite set_cons ; split ; first by [].
      by rewrite cons_uniq -andP** -negP**.
  - exact (ε_spec ex).
Qed.

Lemma In_list_of_set (A:Type') (s : set A) :
  finite_set s -> forall x, In x [list of s] = s x.
Proof.
  by move=>fin_s x ; rewrite -{2}(proj1 (list_of_set_spec fin_s)) -in_In.
Qed.

Lemma list_of_set0 (A:Type') (s : set A) : (s = set0) -> ([list of s] = nil).
Proof.
  move: (list_of_set_spec (finite_set0 A)) => [e _] ->.
  destruct (list_of_set set0) as [|a l] ; first by reflexivity.
  rewrite set_cons setU_eq0 in e.
  have contra : set0 a by move:e=>[<- _] ; reflexivity.
  by inversion contra.
Qed.

Lemma eq_mod_permut A (l: list A):
  forall l', (forall x, List.In x l = List.In x l') -> NoDup l -> NoDup l' -> Permutation l l'.
Proof.
  induction l; destruct l'.

  intros. apply perm_nil.

  intro e. generalize (e a). simpl. intro h. symmetry in h.
  apply False_rec. rewrite <- h. left. reflexivity.

  intro e. generalize (e a). simpl. intro h.
  apply False_rec. rewrite <- h. left. reflexivity.

  intros e n n'. inversion n; inversion n'; subst.
  destruct (pselect (a = a0)).

  (* case a = a0 *)
  subst a0. apply perm_skip. apply IHl.

  intro x. apply prop_ext; intro h.
  assert (i: List.In x (a::l)). right. exact h.
  rewrite e in i. destruct i. subst x. contradiction. exact H.
  assert (i: List.In x (a::l')). right. exact h.
  rewrite <- e in i. destruct i. subst x. contradiction. exact H.
  assumption.
  assumption.

  (* case a <> a0 *)
  assert (i: In a (a0 :: l')). rewrite <- (e a). left. reflexivity.
  apply in_split in i. destruct i as [l1 [l2 i]]. rewrite i.
  rewrite <- Permutation_middle. apply perm_skip. apply IHl.
  2: assumption.
  2: apply NoDup_remove_1 with a; rewrite <- i; apply NoDup_cons; assumption.

  intro x. apply prop_ext; intro h.

  assert (j: List.In x (a::l)). right. exact h.
  rewrite e i in j. apply in_elt_inv in j. destruct j as [j|j].
  subst x. contradiction. exact j.
  assert (j: In x (l1 ++ a :: l2)%list). apply in_or_app. apply in_app_or in h.
    destruct h as [h|h]. left. exact h. right. right. exact h.
  rewrite <- i, <- e in j. destruct j as [j|j].
  subst x. rewrite i in n'. apply NoDup_remove in n'. destruct n' as [h1 h2].
  contradiction. exact j.
Qed.

Lemma list_of_setU1 {A:Type'} (a:A) {s} :
  finite_set s -> exists l', Permutation l' (a :: [list of s]) /\
                     [list of a |` s] = if s a then [list of s] else l'.
Proof.
  intro H.
  exists (if s a then a :: [list of s] else [list of a |` s]).
  if_intro=>H' ; split ; auto.
  - f_equal. rewrite setUidr. reflexivity. now intros _ ->.
  - apply eq_mod_permut.
    + intro x. rewrite In_list_of_set.
      ext. inversion 1 as [->|]. 3 : intros [i | i].
      * now left.
      * right. now rewrite In_list_of_set.
      * left. now symmetry.
      * right. now rewrite <- In_list_of_set.
      * rewrite -> finite_setE in *. now apply finite'_setU1.
    + rewrite -uniq_NoDup. apply list_of_set_spec. rewrite -> finite_setE in *.
      exact: finite'_setU1.
    + apply NoDup_cons. now rewrite In_list_of_set.
      rewrite -uniq_NoDup. now apply list_of_set_spec.
Qed.

Definition ITSET {A B : Type'} : (A -> B -> B) -> (A -> Prop) -> B -> B := fun _43025 : A -> B -> B => fun _43026 : A -> Prop => fun _43027 : B => @ε ((A -> Prop) -> B) (fun g : (A -> Prop) -> B => ((g (@set0 A)) = _43027) /\ (forall x : A, forall s : A -> Prop, (@finite_set A s) -> (g (@INSERT A x s)) = (@COND B (@IN A x s) (g s) (_43025 x (g s))))) _43026.

Definition permut_inv {A B:Type} (f:A -> B -> B) :=
  forall b y x, f x (f y b) = f y (f x b).

Definition fold_set {A B:Type'} (f : A -> B -> B) (s : set A) (b : B) :=
  if permut_inv f /\ finite_set s then fold_right f b [list of s] else ITSET f s b.

Lemma permut_inv_fold_right {A B : Type} {f : A -> B -> B} {b : B} {l : list A} l' :
  Permutation l l' -> permut_inv f -> fold_right f b l = fold_right f b l'.
Proof.
  intros H H'. induction H.
  - reflexivity.
  - simpl. now f_equal.
  - apply H'.
  - now rewrite IHPermutation1.
Qed.

(* Note the structure, could definitely be generalized to
   partial functions on subsets with a definition similar to finite. *)
Lemma ITSET_def {A B : Type'} : (@fold_set A B) = ITSET.
Proof.
  rewrite/fold_set/ITSET. ext=> f s b.
  case (EM (permut_inv f))=> ? ; last by if_triv by easy.
  revert s. align_ε_if.
  - split. now rewrite list_of_set0. intros a E H'. unfold INSERT.
    destruct (list_of_setU1 a H') as (l, (Hl, ->))=> /3= /c` H.
    reflexivity. now rewrite (permut_inv_fold_right Hl).
  - rewrite finite_setE. intros f' (HEmpty,HINSERT) (HEmpty', HINSERT') E (_, Hfin).
    induction Hfin. now rewrite HEmpty HEmpty'.
    unfold INSERT in *. now rewrite -> HINSERT, HINSERT', IHHfin.
Qed.

Open Scope fset_scope.
Open Scope nat_scope.

Definition CARD_HOL (A : Type') (s : set A) := fold_set (fun _ => S) s 0.

Lemma permut_inv_succ (A : Type) : permut_inv (fun _ : A => S).
Proof. by []. Qed.

Definition CARD (A : Type') (s : set A) :=
  if finite_set s then (#|` fset_set s|) else CARD_HOL s.

Lemma in_fset_list {A : Type'} (l : list A) :
  [fset x in l] =i l.
Proof.
  by elim:l=>[|a l IHl] x /= ; rewrite !in_fset_.
Qed.

Lemma fset_set_list {A : Type'} (l : list A) :
  fset_set [set` l] = [fset x in l].
Proof.
  apply fsetP=>x ; rewrite in_fset_set ; last by apply (finite_witness l).
  by rewrite in_fset_list mem_setE.
Qed.

Lemma CARD_def (A : Type') : (@CARD A) = (fun _43228 : A -> Prop => @fold_set A nat (fun x : A => fun n : nat => S n) _43228 (NUMERAL O)).
Proof.
  rewrite/3=/CARD/fold_set; ext=>s ; if_intro =>fin_s ; last by [].
  if_triv using permut_inv_succ.
  move:(list_of_set_spec fin_s)=>[eq nd] ; rewrite -{1}eq.
  rewrite fset_set_list card_fseq undup_id ; last by [].
  by elim:[list of s] => [|a l IHl] ; last (simpl ; f_equal).
Qed.

Definition dimindex (A : Type') (_ : set A) :=
  if finite_set [set: A] then CARD [set: A] else 1.

Lemma dimindex_def (A : Type') : (@dimindex A) = (fun _94156 : A -> Prop => @COND nat (@finite_set A (@setT A)) (@CARD A (@setT A)) (NUMERAL (BIT1 O))).
Proof. exact erefl. Qed.

Lemma dimindex_gt0 (A : Type') (s : set A) : 0 < dimindex s.
Proof.
  rewrite/dimindex/CARD lt0n => /c` fin_A // /1= ; rewrite cardfs_eq0.
  apply/fset0Pn ; exists point ; rewrite in_fset_set // ; exact: in_setT.
Qed.

(* seq_fset seems intended only for internal use in mathcomp but has useful results. *)
Lemma fset_set_seq_fset (A: Type') (l : list A) : [fset x in l] = seq_fset tt l.
Proof.
  by apply fsetP=>x ; rewrite in_fset_list seq_fsetE.
Qed.

Lemma CARD_set_of_list (A : Type') (l : list A) : CARD [set` l] = size (undup l).
Proof.
  rewrite/CARD fset_set_list fset_set_seq_fset ; if_triv using (finite_witness l).
  exact: size_seq_fset.
Qed.

Lemma size_undup_uniq (A: Type') (s: seq A): uniq s = (size (undup s) == size s).
Proof.
  elim:s=> //= a s -> ; set (b := a \in s) ; rewrite-/b ; case b => //=.
  rewrite sym; apply: negbTE ; have:= size_undup s.
  by elim: (size s) (size (undup s))=> [[] | ? ? []].
Qed.

Lemma list_of_set_def (A : Type') : (@list_of_set A) = (fun _56426 : A -> Prop => @ε (list A) (fun l : list A => ((@set_of_list A l) = _56426) /\ ((@size A l) = (@CARD A _56426)))).
Proof.
  rewrite/list_of_set/set_of_list=> /` s ; f_equal=> /` l [<- Hl] ; split=>//.
  all : by move:Hl ; rewrite size_undup_uniq CARD_set_of_list -eqP**=> ->.
Qed.

(* Could be useful for cardinal proofs. *)
Lemma CARD_witness {A : Type'} (l : list A) (s : set A) (n : nat) : s = [set` l] ->
  n = size (undup l) -> CARD s = n.
Proof.
  by move=>->-> ; apply CARD_set_of_list.
Qed.

Arguments CARD_witness {_} _.
Close Scope fset_scope.

(*****************************************************************************)
(* A type for natural numbers between 1 and n for n > 0 *)
(*****************************************************************************)

(* Integer interval [( n ; m )] *)

Definition dotdot (n m : nat) : set nat := `[n, m].

(* The one to actually use in proofs, to take advantage of lia
   for example. *)
Lemma dotdotE : dotdot = fun n m k => n <= k <= m.
Proof. by []. Qed.

(* Add rewriting dotdotE to pattern /3=. *)
Ltac ssrsimpl3 ::=
  rewrite ?SPEC_IMAGE?SPEC_elim/GSPEC/SETSPEC/DELETE/IMAGE/INTERS/UNIONS/
  INSERT/BIT1/BIT0/NUMERAL?setU0?IN_def?dotdotE.

Lemma dotdot_def : dotdot = (fun _66922 : nat => fun _66923 : nat => @GSPEC nat (fun GEN_PVAR_231 : nat => exists x : nat, @SETSPEC nat GEN_PVAR_231 ((leqn _66922 x) /\ (leqn x _66923)) x)).
Proof. by funext=> * /3= ; rewrite/leqn andP**. Qed.

Section enum_type.
(* Basically finite ordinal arithmetic with types. *)

Context (n : nat) (H : 0 < n).

Definition enum_type : Type := let _ := H in 'I_n.

Local Definition inhabits (k : nat) := IN k (dotdot 1 n).

HB.instance Definition _ := Equality.on enum_type.
HB.instance Definition _ := Choice.on enum_type.
HB.instance Definition _ := isPointed.Build enum_type (Ordinal H).

Local Lemma inhabits_to_ord k : inhabits k -> k.-1 < n.
Proof. by rewrite/inhabits/3= ; elim: k. Qed.

Definition mk_enum (k : nat) : enum_type :=
  match pselect (inhabits k) with
  | left p => Ordinal (inhabits_to_ord p)
  | _ => Ordinal H end.

Definition dest_enum (k : enum_type) : nat := k.+1.

Lemma mk_dest_enum : forall k : enum_type, mk_enum (dest_enum k) = k.
Proof.
  case=> k ink. rewrite/dest_enum/mk_enum.
  case (pselect (inhabits (Ordinal ink).+1)) ; last by rewrite/inhabits/3=.
  move=> ink' ; move:{ink'}(inhabits_to_ord ink').
  rewrite -pred_Sn => ? ; f_equal ; exact: proof_irrelevance.
Qed.

Lemma dest_mk_enum : forall k : nat, inhabits k = (dest_enum (mk_enum k) = k).
Proof.
  move => k ; rewrite/dest_enum/mk_enum ; case (pselect (inhabits k)).
  - move/[dup] => ink ; rewrite/= -{1}(is_True (inhabits k)) => ->.
    by rewrite sym is_True ; case: k ink ; rewrite // /inhabits/3=.
  - move/[dup] => nink ; rewrite/= -is_False => -> ; rewrite sym is_False.
    by move:nink=>/[swap] <- ; apply ; rewrite/inhabits/3= ; move:H ; case n.
Qed.

End enum_type.
Arguments dest_enum {_} _.
Arguments mk_dest_enum {_} _.

(*****************************************************************************)
(* Cart.finite_image: natural numbers between 1 and the CARDinal of A,
if A is finite, and 1 otherwise. *)
(*****************************************************************************)

Lemma finite_image_gen (A : Type') : 0 < dimindex [set: A].
Proof. exact: dimindex_gt0. Qed.

Definition finite_image A := enum_type (finite_image_gen A).

Definition finite_index A := mk_enum (finite_image_gen A).

Definition dest_finite_image A := dest_enum (finite_image_gen A).

Definition axiom_27 A : forall a : finite_image A, (@finite_index A (@dest_finite_image A a)) = a :=
  mk_dest_enum (finite_image_gen A).

Definition axiom_28 A : forall r : nat, ((fun x : nat => @IN nat x (dotdot (NUMERAL (BIT1 0)) (@dimindex A [set: A]))) r) = ((@dest_finite_image A (@finite_index A r)) = r) :=
  dest_mk_enum (finite_image_gen A).

(*****************************************************************************)
(* Cart.cart A B represents A ^ (card B) *)
(*****************************************************************************)

(* The same type in mathcomp is defined using column matrices. *)
Definition cart (A B : Type') : Type' := 'rV[A]_(dimindex [set:B]).

Definition mk_cart (A B : Type') (f : finite_image B -> A) : cart A B :=
  \row_i f i.

Definition dest_cart (A B : Type') (M : cart A B) : finite_image B -> A :=
  M ord0.

(* I believe the first makes sense to be defined, the second comes
   from extensionality. *)
Lemma fun_of_matrixK R m n k : cancel (@fun_of_matrix R m n) (matrix_of_fun k).
Proof.
  by move=> M ; apply/matrixP => ? ? ; rewrite mxE.
Qed.

Lemma matrix_of_funK R m n k : cancel (matrix_of_fun k) (@fun_of_matrix R m n).
Proof.
  move=> f /f` ; exact:mxE.
Qed.

Lemma axiom_29 : forall (A B : Type') (a : cart A B), (@mk_cart A B (@dest_cart A B a)) = a.
Proof.
  by rewrite/mk_cart/dest_cart=> *; apply/matrixP=> -[[]] *; rewrite mxE !ord1.
Qed.

Lemma axiom_30 : forall (A B : Type') (r : (finite_image B) -> A), ((fun f : (finite_image B) -> A => True) r) = ((@dest_cart A B (@mk_cart A B r)) = r).
Proof.
  by move=> * ; rewrite/dest_cart/mk_cart sym is_True matrix_of_funK.
Qed.

(* To be able to use HOL Light objects on row vectors *)
Lemma fset_setT (T : finType) : fset_set [set: T] = [fset i in finset.setT]%fset.
Proof.
  apply/fsetP => x ; rewrite in_fset_set ; last exact: finite_finset.
  by rewrite in_setT 2!inE.
Qed.

Lemma card_fset_setT (T : finType) : #|`fset_set [set: T]| = #|T|.
Proof.
  by rewrite fset_setT card_finset cardsT.
Qed.

Lemma card_fset_set_ord n : #|`fset_set [set: 'I_n]| = n.
Proof.
  by rewrite card_fset_setT card_ord.
Qed.

Lemma row_to_cart (A : Type') (n : nat) (gt0n : (0 < n)%N) :
  'rV[A]_n = cart A (enum_type gt0n).
Proof.
  rewrite/cart/dimindex/CARD/enum_type; f_equal.
  have ?: finite_set [set:'I_n] by exact: finite_finset.
  by rewrite /1= card_fset_set_ord.
Qed.

(*****************************************************************************)
(* Cart.finite_sum *)
(*****************************************************************************)

Lemma finite_sum_key (A B : Type') : 0 < dimindex [set: A] + dimindex [set: B].
Proof. by rewrite addn_gt0 dimindex_gt0. Qed.

Definition finite_sum A B := enum_type (finite_sum_key A B).

Definition mk_finite_sum A B := mk_enum (finite_sum_key A B).

Definition dest_finite_sum A B := dest_enum (finite_sum_key A B).

Definition axiom_31 A B : forall a : finite_sum A B, (@mk_finite_sum A B (@dest_finite_sum A B a)) = a :=
  mk_dest_enum (finite_sum_key A B).

Definition axiom_32 A B : forall r : nat, ((fun x : nat => @IN nat x (dotdot (NUMERAL (BIT1 0)) (addn (@dimindex A [set: A]) (@dimindex B [set: B])))) r) = ((@dest_finite_sum A B (@mk_finite_sum A B r)) = r) :=
  dest_mk_enum (finite_sum_key A B).

(*****************************************************************************)
(* Cart.finite_diff *)
(*****************************************************************************)

Lemma finite_diff_key (A B : Type') :
  0 < maxn (dimindex [set: A] - dimindex [set: B]) 1.
Proof. exact: leq_maxr. Qed.

Definition finite_diff A B := enum_type (finite_diff_key A B).

Definition mk_finite_diff A B := mk_enum (finite_diff_key A B).

Definition dest_finite_diff A B := dest_enum (finite_diff_key A B).

Definition axiom_33 A B : forall a : finite_diff A B, (@mk_finite_diff A B (@dest_finite_diff A B a)) = a :=
  mk_dest_enum (finite_diff_key A B).

Lemma ltn1 n : n < 1 = (n == 0).
Proof. by case: n. Qed.

Lemma axiom_34 A B : forall r : nat, ((fun x : nat => @IN nat x (dotdot (NUMERAL (BIT1 0)) (@COND nat (ltn (@dimindex B [set: B]) (@dimindex A [set: A])) (subn (@dimindex A [set: A]) (@dimindex B [set: B])) (NUMERAL (BIT1 0))))) r) = ((@dest_finite_diff A B (@mk_finite_diff A B r)) = r).
Proof.
  move=> n /2= ; rewrite -dest_mk_enum/inhabits ; do 2 f_equal.
  by rewrite/maxn/ltn ltn1 subn_eq0 ; case: leqP => /1=.
Qed.

(*****************************************************************************)
(* Cart.finite_prod *)
(*****************************************************************************)

Lemma finite_prod_key (A B: Type') : 0 < dimindex [set: A] * dimindex [set: B].
Proof. by rewrite muln_gt0 2!dimindex_gt0. Qed.

Definition finite_prod A B := enum_type (finite_prod_key A B).

Definition mk_finite_prod A B := mk_enum (finite_prod_key A B).

Definition dest_finite_prod A B := dest_enum (finite_prod_key A B).

Definition axiom_35 A B : forall a : finite_prod A B, (@mk_finite_prod A B (@dest_finite_prod A B a)) = a :=
  mk_dest_enum (finite_prod_key A B).

Definition axiom_36 A B : forall r : nat, ((fun x : nat => @IN nat x (dotdot (NUMERAL (BIT1 0)) (muln (@dimindex A (@setT A)) (@dimindex B (@setT B))))) r) = ((@dest_finite_prod A B (@mk_finite_prod A B r)) = r) :=
  dest_mk_enum (finite_prod_key A B).

(*****************************************************************************)
(* Mapping of a subtype of recspace (embedding of any type A into recspace A) *)
(*****************************************************************************)

Unset Implicit Arguments.
Section copy_type.

  Variable A : Type'.

  Definition cp_dest (a:A) : recspace A := CONSTR 0 a Fnil.

  Definition cp_pred (r : recspace A) := exists a, r = cp_dest a.

  Definition cp_mk := finv cp_dest.

  Lemma cp_mk_dest : forall a : A, (cp_mk (cp_dest a)) = a.
  Proof.
    by finv_inv_l => ? ? ; inversion 1.
  Qed.

  Lemma cp_dest_mk : forall r : recspace A, (forall P : recspace A -> Prop, (forall r' : recspace A, cp_pred r' -> P r') -> P r) = (cp_dest (cp_mk r) = r).
  Proof.
    intro r. apply (@finv_inv_r _ _ _ (fun r0 => (forall P : recspace A -> Prop,
      (forall r' : recspace A, cp_pred r' -> P r') -> P r0))) ; intro H.
    - apply H. clear r H. intros r (a,H). now exists a.
    - destruct H as (a,<-). intros P H. apply H. now exists a.
  Qed.

End copy_type.
Set Implicit Arguments.

(*****************************************************************************)
(* Cart.tybit0 *)
(*****************************************************************************)

Definition tybit0 A := finite_sum A A.

Definition _mk_tybit0 A := cp_mk (tybit0 A).

Definition _dest_tybit0 A := cp_dest (tybit0 A).

Definition axiom_37 A : forall a : tybit0 A, (@_mk_tybit0 A (@_dest_tybit0 A a)) = a :=
  cp_mk_dest (tybit0 A).

Definition axiom_38 A : forall r : recspace (finite_sum A A), ((fun a : recspace (finite_sum A A) => forall tybit0' : (recspace (finite_sum A A)) -> Prop, (forall a' : recspace (finite_sum A A), (exists a'' : finite_sum A A, a' = ((fun a''' : finite_sum A A => @mappings.CONSTR (finite_sum A A) (NUMERAL 0) a''' (fun n : nat => @mappings.BOTTOM (finite_sum A A))) a'')) -> tybit0' a') -> tybit0' a) r) = ((@_dest_tybit0 A (@_mk_tybit0 A r)) = r) :=
  cp_dest_mk (tybit0 A).

(*****************************************************************************)
(* Cart.tybit1 *)
(*****************************************************************************)

Definition tybit1 A := finite_sum (finite_sum A A) Datatypes.unit.

Definition _mk_tybit1 A := cp_mk (tybit1 A).

Definition _dest_tybit1 A := cp_dest (tybit1 A).

Definition axiom_39 A : forall (a : tybit1 A), (@_mk_tybit1 A (@_dest_tybit1 A a)) = a :=
  cp_mk_dest (tybit1 A).

Definition axiom_40 A : forall r : recspace (finite_sum (finite_sum A A) Datatypes.unit), ((fun a : recspace (finite_sum (finite_sum A A) Datatypes.unit) => forall tybit1' : (recspace (finite_sum (finite_sum A A) Datatypes.unit)) -> Prop, (forall a' : recspace (finite_sum (finite_sum A A) Datatypes.unit), (exists a'' : finite_sum (finite_sum A A) Datatypes.unit, a' = ((fun a''' : finite_sum (finite_sum A A) Datatypes.unit => @mappings.CONSTR (finite_sum (finite_sum A A) Datatypes.unit) (NUMERAL 0) a''' (fun n : nat => @mappings.BOTTOM (finite_sum (finite_sum A A) Datatypes.unit))) a'')) -> tybit1' a') -> tybit1' a) r) = ((@_dest_tybit1 A (@_mk_tybit1 A r)) = r) :=
  cp_dest_mk (tybit1 A).

(*****************************************************************************)
(* functions from iterate.ml to define the euclidean norm *)
(*****************************************************************************)

Definition neutral {A : Type'} (prod : A -> A -> A) := @ε A (fun x : A => forall y : A, ((prod x y) = y) /\ ((prod y x) = y)).
Lemma neutral_def {A : Type'} : (@neutral A) = (fun prod : A -> A -> A => @ε A (fun x : A => forall y : A, ((prod x y) = y) /\ ((prod y x) = y))).
Proof. exact (REFL (@neutral A)). Qed.

(* Would prove it for groups but they are less used than zmodTypes *)
Lemma neutralE (G : zmodType) : @neutral G +%R = 0%R.
Proof.
  rewrite/neutral sym ; align_ε ; first by move=> ? ; rewrite addr0 add0r.
  by move=> x /[spec x] -[{5}<- _] /[spec 0%R : G] -[_ ->].
Qed.

Definition monoidal {A : Type'} : (A -> A -> A) -> Prop := fun f : A -> A -> A => (forall x : A, forall y : A, (f x y) = (f y x)) /\ ((forall x : A, forall y : A, forall z : A, (f x (f y z)) = (f (f x y) z)) /\ (forall x : A, (f (@neutral A f) x) = x)).
Lemma monoidal_def {A : Type'} : (@monoidal A) = (fun f : A -> A -> A => (forall x : A, forall y : A, (f x y) = (f y x)) /\ ((forall x : A, forall y : A, forall z : A, (f x (f y z)) = (f (f x y) z)) /\ (forall x : A, (f (@neutral A f) x) = x))).
Proof. exact (REFL (@monoidal A)). Qed.

Lemma add_monoidal (M : nmodType) : @monoidal M%' +%R.
Proof.
  repeat split => * ; [exact: addrC | exact: addrA |].
  rewrite/neutral ; have N0: exists x : M, forall y, (x+y = y /\ y+x = y)%mcR.
  - by exists 0%R => ? ; rewrite addr0 add0r.
  - by apply (@ε_spec M%' _ N0).
Qed.

Definition support {A B : Type'} (prod : B -> B -> B) (f : A -> B) (s : set A) :=
  [set x | s x /\ f x <> neutral prod].

Lemma support_def {A B : Type'} : (@support A B) = (fun _69010 : B -> B -> B => fun _69011 : A -> B => fun _69012 : A -> Prop => @GSPEC A (fun GEN_PVAR_239 : A => exists x : A, @SETSPEC A GEN_PVAR_239 ((@IN A x _69012) /\ (~ ((_69011 x) = (@neutral B _69010)))) x)).
Proof. by funext=> * /3=. Qed.

Definition iterate {A B : Type'} (prod : B -> B -> B) (s : set A) (f : A -> B) :=
  let sup := support prod f s in
    if finite_set sup then fold_set (fun a b => prod (f a) b) sup (neutral prod)
    else neutral prod.

Lemma iterate_def {A B : Type'} : (@iterate A B) = (fun _69031 : B -> B -> B => fun _69032 : A -> Prop => fun _69033 : A -> B => @COND B (@finite_set A (@support A B _69031 _69033 _69032)) (@fold_set A B (fun x : A => fun a : B => _69031 (_69033 x) a) (@support A B _69031 _69033 _69032) (@neutral B _69031)) (@neutral B _69031)).
Proof. exact (REFL (@iterate A B)). Qed.

(* sum s f = Σ_(x in s) f x *)
Definition sum {A : Type'} (s : set A) (f : A -> R) : R := iterate addr s f.
Lemma sum_def {A : Type'} : (@sum A) = (@iterate A R addr).
Proof. exact (REFL (@sum A)). Qed.

Definition coord (A : Type') (n : nat) (M : 'rV[A]_n) (m : nat) : A.
Proof.
  case:n M => [|n] M ; [exact point | exact (M ord0 (inord m))].
Defined.

Lemma inord_lt n m (ltnSm : n < m.+1) : inord n = Ordinal ltnSm.
Proof.
  rewrite/inord/insubd/oapp/insub/Sub ; case (@idP (n < m.+1)) => //= ?.
  f_equal ; exact: proof_irrelevance.
Qed.

Lemma inord_gt n m (gtnm : m < n) : inord n = ord0 :> 'I_m.+1.
Proof.
  rewrite/inord/insubd/oapp/insub/Sub ; case (@idP (n < m.+1)) => //=.
  by move=> ltnSm ; contradict ltnSm ; elim:m n gtnm=> [| ? ?] [].
Qed.

Lemma coordE (A : Type') n m (ltmn : m < n) (M : 'rV[A]_n) :
  coord M m = M ord0 (Ordinal ltmn).
Proof.
  case:n ltmn M=> // n * ; rewrite/coord ; f_equal ; exact:inord_lt.
Qed.

Lemma coord_ord (A : Type') n (M : 'rV[A]_n) (m : 'I_n) :
  coord M m = M ord0 m.
Proof.
  rewrite coordE ; case:m=>* ; do 2 f_equal ; exact: proof_irrelevance.
Qed.

(* HOL Light takes coordinates starting at 1. *)
Definition dollar (A n : Type') (M : cart A n) (m : nat) : A := coord M m.-1.

Lemma dollar_def {A N' : Type'} : (@dollar A N') = (fun _94652 : cart A N' => fun _94653 : nat => @dest_cart A N' _94652 (@finite_index N' _94653)).
Proof.
  rewrite/cart/finite_index/dest_cart/mk_cart/mk_enum/enum_type/dollar=> /`M n.
  case (pselect (inhabits (dimindex [set: N']) n)).
  - move=>? ; exact: coordE.
  - case: {N'}(dimindex [set: N']) (finite_image_gen N') M ; first by [].
    rewrite/inhabits/coord/3= => m mgt0 M ; rewrite -andP** not_andE 2!negP**.
    rewrite -2!ltnNge ltnS leqn0 ; case.
    + move/eqP=> -> /= ; f_equal ; exact: inord_lt.
    + move=> ltSmn ; rewrite inord_gt ; last by elim:n ltSmn.
      rewrite/ord0 ; do 2 f_equal ; exact:proof_irrelevance.
Qed.

(*  !!! TODO: move somewhere, alignment of Libraries/analysis.ml !!!

(*****************************************************************************)
(* Disambiguate mathcomp and stdlib notations for reals. *)
(*****************************************************************************)

Delimit Scope ring_scope with mcR.

Delimit Scope R_scope with coqR.

Lemma R1E : (Rdefinitions.IZR (BinNums.Zpos BinNums.xH)) = 1%mcR.
Proof. by []. Qed.

Lemma R0E : (Rdefinitions.IZR BinNums.Z0) = 0%mcR.
Proof. by []. Qed.

Lemma RltE : Rlt = Order.lt.
Proof. by ext=>* ; apply/RltP. Qed.

Lemma RleE: Rle = Order.le.
Proof. by ext=>* ; apply/RleP. Qed.

Definition coqRE :=
  (R0E, R1E, INRE, IZRposE, RabsE, RltE, RleE,
    RinvE, RoppE, RdivE, RminusE, RplusE, RmultE, RpowE, RsqrtE).


(*****************************************************************************)
(* Topologies (Libraries/analysis.ml) *)
(*****************************************************************************)

Definition re_Union {A : Type'} : ((A -> Prop) -> Prop) -> A -> Prop := fun _114505 : (A -> Prop) -> Prop => fun x : A => exists s : A -> Prop, (_114505 s) /\ (s x).
Lemma re_Union_def {A : Type'} : (@re_Union A) = (fun _114505 : (A -> Prop) -> Prop => fun x : A => exists s : A -> Prop, (_114505 s) /\ (s x)).
Proof. exact (REFL (@re_Union A)). Qed.
Definition re_union {A : Type'} : (A -> Prop) -> (A -> Prop) -> A -> Prop := fun _114510 : A -> Prop => fun _114511 : A -> Prop => fun x : A => (_114510 x) \/ (_114511 x).
Lemma re_union_def {A : Type'} : (@re_union A) = (fun _114510 : A -> Prop => fun _114511 : A -> Prop => fun x : A => (_114510 x) \/ (_114511 x)).
Proof. exact (REFL (@re_union A)). Qed.
Definition re_intersect {A : Type'} : (A -> Prop) -> (A -> Prop) -> A -> Prop := fun _114522 : A -> Prop => fun _114523 : A -> Prop => fun x : A => (_114522 x) /\ (_114523 x).
Lemma re_intersect_def {A : Type'} : (@re_intersect A) = (fun _114522 : A -> Prop => fun _114523 : A -> Prop => fun x : A => (_114522 x) /\ (_114523 x)).
Proof. exact (REFL (@re_intersect A)). Qed.
Definition re_null {A : Type'} : A -> Prop := fun x : A => False.
Lemma re_null_def {A : Type'} : (@re_null A) = (fun x : A => False).
Proof. exact (REFL (@re_null A)). Qed.
Definition re_universe {A : Type'} : A -> Prop := fun x : A => True.
Lemma re_universe_def {A : Type'} : (@re_universe A) = (fun x : A => True).
Proof. exact (REFL (@re_universe A)). Qed.
Definition re_subset {A : Type'} : (A -> Prop) -> (A -> Prop) -> Prop := fun _114534 : A -> Prop => fun _114535 : A -> Prop => forall x : A, (_114534 x) -> _114535 x.
Lemma re_subset_def {A : Type'} : (@re_subset A) = (fun _114534 : A -> Prop => fun _114535 : A -> Prop => forall x : A, (_114534 x) -> _114535 x).
Proof. exact (REFL (@re_subset A)). Qed.
Definition re_compl {A : Type'} : (A -> Prop) -> A -> Prop := fun _114546 : A -> Prop => fun x : A => ~ (_114546 x).
Lemma re_compl_def {A : Type'} : (@re_compl A) = (fun _114546 : A -> Prop => fun x : A => ~ (_114546 x)).
Proof. exact (REFL (@re_compl A)). Qed.


Definition istopology {A : Type'} : ((A -> Prop) -> Prop) -> Prop := fun _114555 : (A -> Prop) -> Prop => (_114555 (@re_null A)) /\ ((_114555 (@re_universe A)) /\ ((forall a : A -> Prop, forall b : A -> Prop, ((_114555 a) /\ (_114555 b)) -> _114555 (@re_intersect A a b)) /\ (forall P : (A -> Prop) -> Prop, (@re_subset (A -> Prop) P _114555) -> _114555 (@re_Union A P)))).
Lemma istopology_def {A : Type'} : (@istopology A) = (fun _114555 : (A -> Prop) -> Prop => (_114555 (@re_null A)) /\ ((_114555 (@re_universe A)) /\ ((forall a : A -> Prop, forall b : A -> Prop, ((_114555 a) /\ (_114555 b)) -> _114555 (@re_intersect A a b)) /\ (forall P : (A -> Prop) -> Prop, (@re_subset (A -> Prop) P _114555) -> _114555 (@re_Union A P))))).
Proof. exact (REFL (@istopology A)). Qed.

Record Topology (A : Type') := {
  opens : set (set A) ;
  opens_empty : opens set0;
  opens_full : opens setT;
  opens_I : forall s s', opens s -> opens s' -> opens (s `&` s');
  opens_U : forall S, S `<=` opens -> opens (\bigcup_(s in S) s) }.


Definition discrete_Topology A : Topology A.
Proof.
  by exists setT.
Defined.

HB.instance Definition _ A := is_Type' (discrete_Topology A).

Definition topology {A : Type'} : ((A -> Prop) -> Prop) -> Topology A :=
  finv (@opens A).

Lemma _mk_dest_Topology : forall {A : Type'} (a : Topology A), (@topology A (@opens A a)) = a.
Proof.
  _mk_dest_record.
Qed.

Lemma andE b b' : b && b' = (b /\ b') :> Prop.
Proof. by ext ; move/andP. Qed.

Lemma re_intersect_eq {A} : @re_intersect A = setI.
Proof.
  funext => s0 s1 a ; rewrite -(in_setE (s0 `&` s1)) in_setI.
  by rewrite andE 2!in_setE.
Qed.

Lemma re_Union_eq {A} S : @re_Union A S = \bigcup_(s in S) s.
Proof.
  by rewrite/bigcup/mkset/re_Union ; funext => a ; rewrite exists2E.
Qed.

Lemma _dest_mk_Topology : forall {A : Type'} (r : (A -> Prop) -> Prop), ((fun t : (A -> Prop) -> Prop => @istopology A t) r) = ((@opens A (@topology A r)) = r).
Proof.
  _dest_mk_record.
  - record_exists {| opens := r |}.
    by rewrite -re_Union_eq ; auto.
  - by rewrite re_Union_eq ; auto.
Qed.

Definition toTopology (T : ptopologicalType) : Topology T.
Proof.
  exists open.
  - exact open0.
  - exact openT.
  - exact openI.
  - move=> S Sopen. by apply bigcup_open.
Defined.

Definition neigh {A : Type'} : (Topology A) -> (prod (A -> Prop) A) -> Prop := fun T : Topology A => fun c : prod (A -> Prop) A => exists P : A -> Prop, (@opens A T P) /\ ((@re_subset A P (@fst (A -> Prop) A c)) /\ (P (@snd (A -> Prop) A c))).
Lemma neigh_def {A : Type'} : (@neigh A) = (fun T : Topology A => fun c : prod (A -> Prop) A => exists P : A -> Prop, (@opens A T P) /\ ((@re_subset A P (@fst (A -> Prop) A c)) /\ (P (@snd (A -> Prop) A c)))).
Proof. exact (REFL (@neigh A)). Qed.

Lemma neigh_align (T : ptopologicalType) : forall x s, nbhs x s = neigh (toTopology T) (s,x).
Proof.
  move=> x s ; rewrite nbhsE/neigh/open_nbhs mksetE exists2E.
  ext => [[s' [[open_s' s'_x] s'_s]] | [s' [open_s' [s'_x s'_s]]]] ; exists s' ; repeat split => //.
Qed.

Definition tends {A B : Type'} : (B -> A) -> A -> (prod (Topology A) (B -> B -> Prop)) -> Prop :=
  fun f : B -> A => fun l : A => fun c : prod (Topology A) (B -> B -> Prop) =>
  let T := fst c in let R := snd c in
   forall N' : A -> Prop, neigh T (N',l) -> exists n : B, R n n /\ forall m : B, R m n -> N' (f m).
Lemma tends_def {A B : Type'} : (@tends A B) = (fun f : B -> A => fun l : A => fun c : prod (Topology A) (B -> B -> Prop) => forall N' : A -> Prop, (@neigh A (@fst (Topology A) (B -> B -> Prop) c) (@pair (A -> Prop) A N' l)) -> exists n : B, (@snd (Topology A) (B -> B -> Prop) c n n) /\ (forall m : B, (@snd (Topology A) (B -> B -> Prop) c m n) -> N' (f m))).
Proof. exact (REFL (@tends A B)). Qed.

(*****************************************************************************)
(* Metric spaces (Libraries/analysis.ml) *)
(*****************************************************************************)
(* Difference with Rocq : Base is an argument instead of a projection *)

(* Cannot manage to map to a subtype of Metric_Space : Universe Inconsistency *)
Unset Implicit Arguments.
Definition discrete_metric A (c : prod A A) : R := if (fst c=snd c) then 0%R else 1%R.

Lemma discr_pos A : forall x y : A, (discrete_metric A (x,y) >= 0)%R.
Proof.
  intros. unfold discrete_metric. if_intro. reflexivity.
  left. exact Rlt_0_1.
Qed.

Lemma discr_sym A : forall x y : A, discrete_metric A (x,y) = discrete_metric A (y,x).
Proof.
  intros. unfold discrete_metric. do 2 if_intro.
  1,4 : reflexivity.
  intros nH H. 2 : intros H nH.
  all : symmetry in H ; destruct (nH H).
Qed.

Lemma discr_refl A : forall x y, discrete_metric A (x,y) = 0%R <-> x = y.
Proof.
  intros. unfold discrete_metric. if_intro;split;intro F;auto.
  destruct (R1_neq_R0 F). contradiction.
Qed.

Lemma discr_tri A : forall x y z,
  (discrete_metric A (x,y) <= discrete_metric A (x,z) + discrete_metric A (z,y))%R.
Proof.
  intros. unfold discrete_metric. do 3 if_intro;try lra.
  intros eq1 eq2 neq. destruct (neq (eq_trans eq2 eq1)).
Qed.

Set Implicit Arguments.

Record Metric (A : Type) := { mdist : prod A A -> R;
    mdist_pos : forall x y : A, (mdist (x,y) >= 0)%R;
    mdist_sym : forall x y : A, mdist (x,y) = mdist (y,x);
    mdist_refl : forall x y : A, mdist (x,y) = 0%R <-> x = y;
    mdist_tri : forall x y z : A, (mdist (x,y) <= mdist (x,z) + mdist (z,y))%R }.

Definition discrete (A : Type) :=
  {| mdist := discrete_metric A;
     mdist_pos := discr_pos A;
     mdist_sym := discr_sym A;
     mdist_refl := discr_refl A;
     mdist_tri := discr_tri A |}.

HB.instance Definition _ (A : Type) := is_Type' (discrete A).

Definition metric {A : Type'} := finv (@mdist A).

Lemma _mk_dest_Metric : forall {A : Type'} (a : Metric A), (@metric A (@mdist A a)) = a.
Proof.
  _mk_dest_record.
Qed.

Definition ismet {A : Type'} : (prod A A -> R) -> Prop := fun d =>
  (forall x y, d (x,y) = 0%R <-> x=y) /\
  forall x y z : A, (d (y,z) <= d (x,y) + d (x,z))%R.

Lemma ismet_def {A : Type'} : (@ismet A) = (fun _114640 : (prod A A) -> R => (forall x : A, forall y : A, ((_114640 (@pair A A x y)) = (R_of_nat (NUMERAL O))) = (x = y)) /\ (forall x : A, forall y : A, forall z : A, ler (_114640 (@pair A A y z)) (Rplus (_114640 (@pair A A x y)) (_114640 (@pair A A x z))))).
Proof.
  ext 1 =>d. unfold ismet. f_equal;auto.
  ext=>H ; intros. now apply propext.
  now rewrite H.
Qed.

Ltac d0 d x := (* automatically replaces all bound instances of d (x,x) with 0 assuming
                  mdist_refl is in the context. *)
  replace (d (x,x)) with (0%R) in * ; [ idtac
  | lazymatch goal with H : forall x y, d (x,y) = 0%R <-> x=y |- 0%R = d (x,x) =>
      symmetry ; now apply H end].

Lemma _dest_mk_Metric : forall {A : Type'} (r : (prod A A) -> R), ((fun m : (prod A A) -> R => @ismet A m) r) = ((@mdist A (@metric A r)) = r).
Proof.
  _dest_mk_record.
  - record_exists {| mdist := r |}.
    + specialize (H0 x y y). d0 r y. lra.
    + assert (H1 := H0 y x y). specialize (H0 x y x). d0 r y. d0 r x. lra.
    + assert (H1 := H0 z x z). assert (H2 := H0 x z x).
      specialize (H0 z x y). d0 r z. d0 r x. lra.
  - rewrite (mdist_sym0 x y). apply mdist_tri0.
Qed.

Definition mtop {A : Type'} : (Metric A) -> Topology A := fun _114835 : Metric A => @topology A (fun S' : A -> Prop => forall x : A, (S' x) -> exists e : R, (Rlt (R_of_nat O) e) /\ (forall y : A, (Rlt (@mdist A _114835 (@pair A A x y)) e) -> S' y)).
Lemma mtop_def {A : Type'} : (@mtop A) = (fun _114835 : Metric A => @topology A (fun S' : A -> Prop => forall x : A, (S' x) -> exists e : R, (Rlt (R_of_nat O) e) /\ (forall y : A, (Rlt (@mdist A _114835 (@pair A A x y)) e) -> S' y))).
Proof. exact (REFL (@mtop A)). Qed.

Definition mr1 : Metric R := metric (fun c => let (x,y) := c in Rabs (subr y x)).
Lemma mr1_def : mr1 = (@metric R (@ε ((prod R R) -> R) (fun f : (prod R R) -> R => forall x : R, forall y : R, @Logic.eq R (f (@pair R R x y)) (Rabs (subr y x))))).
Proof.
  rewrite/mr1 ; f_equal ; align_ε.
  - by [].
  - by move=> d _ d_def // ; funext => -[].
Qed.

Lemma _dest_mk_Metric_if : forall {A : Type'} (r : (prod A A) -> R), ismet r -> mdist (metric r) = r.
Proof.  by move=> A r ; rewrite _dest_mk_Metric. Qed.

Lemma ismet_rdist : ismet (fun c : R * R => let (x, y) := c in Rabs (y - x)).
Proof.
  unfold ismet. split.
  - by move=> x y ; rewrite RabsE eqP** normr_eq0 subr_eq0 eqP** eq_sym.
  - move => x y z ; rewrite !coqRE. rewrite (distrC z x).
    by rewrite (le_trans _ (ler_normD _ _)) // [in leRHS]addrA subrK distrC.
Qed.

Lemma mdist_mr1_align : mdist mr1 = (fun c : R * R => let (x, y) := c in Rabs (y - x)).
Proof.
  rewrite/mr1 ; exact (_dest_mk_Metric_if ismet_rdist).
Qed.

Lemma mtop_mr1_align : mtop mr1 = (toTopology R).
Proof.
  rewrite/mtop mdist_mr1_align -(_mk_dest_Topology (toTopology R)) ; f_equal => /=.
  ext => s /= open_s.
  - rewrite openE /= => r /open_s [e [pos_e sr]].
    exists e => /=; first exact/RltP.
    rewrite/ball_=> y /= rey ; apply sr.
    by rewrite !coqRE distrC.
  - move=> r sr. have [/= e e0 rs] := @normed_module.open_subball R^o R^o _ _ open_s sr.
    exists (e/2)%mcR. have e20 : (0 < e / 2)%mcR by rewrite divr_gt0.
    split ; first exact/RltP.
    move=> r' rr'. apply: (rs _ _ e20) => /=.
    + by rewrite sub0r normrN gtr0_norm // gtr_pMr // invf_lt1 // ltr1n.
    + by rewrite RabsE distrC in rr' ; apply/RltP.
Qed.

Lemma of_nat_inj_le: forall n m, N.of_nat n <= N.of_nat m = (n <= m)%nat.
Proof.
  by move=> n m ; rewrite -{2}(Nnat.Nat2N.id n) -{2}(Nnat.Nat2N.id m) to_nat_inj_le.
Qed.

Import numFieldNormedType.Exports.
Definition tends_num_real (x : nat -> R) (l : R) := (x \o N.of_nat) @ \oo --> l.

Lemma tends_num_real_def : tends_num_real = (fun _115068 : nat -> R => fun _115069 : R => @tends R nat _115068 _115069 (@pair (Topology R) (nat -> nat -> Prop) (@mtop R mr1) N.ge)).
Proof.
  rewrite /tends_num_real mtop_mr1_align /tends /=.
  ext => x l.
  - move/(@cvgrPdist_le R R^o) => /= cvgxl U.
    rewrite -neigh_align => -[e /= e_pos incl_ball_U].
    have e20 : (0 < e/2)%mcR by rewrite divr_gt0.
    have:= (cvgxl (e/2)%R e20) => -[M _ incl_inter_ball] ; exists (N.of_nat M).
    split ; first by rewrite ge_def ; exact: leqn_refl.
    move=> n ; rewrite -(Nnat.N2Nat.id n) => /N.ge_le.
    rewrite of_nat_inj_le ssrnat.leP** => leqMn ; apply incl_ball_U.
    rewrite ball_normE ; apply: (closed_ball_subset e20).
    + by rewrite ltr_pdivrMr // ; rewrite ltr_pMr ; first rewrite ltr1n.
    + by rewrite (closed_ballE _ e20) ; apply (incl_inter_ball (N.to_nat n)).
  - move=> cvgxl ; apply/(@cvgrPdist_le R R^o) => /= e pos_e.
    pose B := closed_ball_ Num.Def.normr l e. have := cvgxl B.
    rewrite -neigh_align. have : nbhs l B.
    + apply/(@nbhs_closedballP _ R^o).
      exists (PosNum pos_e). by rewrite closed_ballE.
    + move => /[swap]/[apply]. case => M [_ MBx]. near=> n.
      apply: MBx. near: n. exists (N.to_nat M) => //=.
      move=> n /=. move/ssrnat.leP.
      by rewrite -of_nat_inj_le Nnat.N2Nat.id ; move/leqn_ge.
  Unshelve. all: by end_near.
Qed.

Definition tendsto {A : Type'} : (prod (Metric A) A) -> A -> A -> Prop := fun _114977 : prod (Metric A) A => fun _114978 : A => fun _114979 : A => (Rlt (R_of_nat O) (@mdist A (@fst (Metric A) A _114977) (@pair A A (@snd (Metric A) A _114977) _114978))) /\ (ler (@mdist A (@fst (Metric A) A _114977) (@pair A A (@snd (Metric A) A _114977) _114978)) (@mdist A (@fst (Metric A) A _114977) (@pair A A (@snd (Metric A) A _114977) _114979))).
Lemma tendsto_def {A : Type'} : (@tendsto A) = (fun _114977 : prod (Metric A) A => fun _114978 : A => fun _114979 : A => (Rlt (R_of_nat O) (@mdist A (@fst (Metric A) A _114977) (@pair A A (@snd (Metric A) A _114977) _114978))) /\ (ler (@mdist A (@fst (Metric A) A _114977) (@pair A A (@snd (Metric A) A _114977) _114978)) (@mdist A (@fst (Metric A) A _114977) (@pair A A (@snd (Metric A) A _114977) _114979)))).
Proof. exact (REFL (@tendsto A)). Qed.

(* represents lim(x (!=)--> x0) f(x) = l *)
Definition tends_real_real (f : R -> R) (l x0 : R) := f @ x0^' --> l.

Lemma tends_real_real_def : tends_real_real = (fun _115511 : R -> R => fun _115512 : R => fun _115513 : R => @tends R R _115511 _115512 (@pair (Topology R) (R -> R -> Prop) (@mtop R mr1) (@tendsto R (@pair (Metric R) R mr1 _115513)))).
Proof.
  rewrite/tends_real_real/tendsto/tends mtop_mr1_align /= mdist_mr1_align.
  ext => f l x0.
  - move/(@cvgrPdist_le R R^o) => /= cvg_f_x0_l U.
    rewrite -neigh_align => -[/= e e_pos incl_ball_U].
    have pos_e2 : (0 < e/2)%mcR by rewrite divr_gt0.
    have:= (cvg_f_x0_l (e/2)%mcR pos_e2) => -[/= d pos_d incl_inter_ball].
    exists (x0 + d/2)%mcR. replace ((x0 + d/2)%mcR - x0)%coqR with (d/2)%mcR.
    split. split ; last by reflexivity.
    + by rewrite RabsE (RltP _ _)** normr_gt0;apply lt0r_neq0;rewrite divr_gt0.
    + move=> x ; rewrite ?coqRE => -[neq_x_x0 ball_x0_d2_x].
      apply incl_ball_U ; rewrite ball_normE ; apply: (closed_ball_subset pos_e2).
      * by rewrite ltr_pdivrMr // ; rewrite ltr_pMr ; first rewrite ltr1n.
      * rewrite (closed_ballE _ pos_e2) ; apply incl_inter_ball.
        { rewrite/= distrC ; apply: (le_lt_trans ball_x0_d2_x).
          by rewrite gtr0_norm ?divr_gt0 // ltr_pdivrMr // ltr_pMr // ltr1n. }
        { rewrite -negP**-eqP** => eq_x_x0. move: neq_x_x0.
          replace `|x - x0|%mcR with (@Algebra.zero R^o).
          by rewrite lt_irreflexive. rewrite -(@normr0 _ R^o).
          f_equal. by rewrite eq_x_x0 -RminusE Rminus_diag. }
    + by rewrite -RplusE Rplus_minus_l.
  - move=> cvgf_x0_l ; apply/(@cvgrPdist_le R R^o) => /= e pos_e.
    pose B := closed_ball_ Num.Def.normr l e.
    have := cvgf_x0_l B. rewrite -neigh_align. have : nbhs l B.
    + apply/(@nbhs_closedballP _ R^o).
      exists (PosNum pos_e). by rewrite closed_ballE.
    + move => /[swap]/[apply]. case => cx0  [[neq_cx0_x0 _] cx0Bx0]. near=> n.
      apply: cx0Bx0. near: n. exists (Rabs (cx0 - x0)) ; first by apply/RltP.
      move=> /= x near_x_x0 neq_x_x0. split.
      * apply Rabs_pos_lt.
        move=>/Rminus_diag_uniq temp; rewrite{}temp in neq_x_x0.
        by move:neq_x_x0 ; move/negP.
      * by left ; rewrite RabsE RminusE distrC (RltP _ _)**.
  Unshelve. all: by end_near.
Qed.

Definition diffl (f : R -> R) (y x : R) :=
  @derivable _ R^o R^o f x 1 /\ @derive1 R^o R^o f x = y.

Lemma diffl_def : diffl = (fun _115541 : R -> R => fun _115542 : R => fun _115543 : R => tends_real_real (fun h : R => Rdiv (Rminus (_115541 (Rplus _115543 h)) (_115541 _115543)) h) _115542 (R_of_nat O)).
Proof.
  rewrite/R_of_nat/diffl/derive1/derivable/tends_real_real/=. funext => f y x.
  under eq_fun; first (move=> h; rewrite (scaler1 h) [(_ *: _)%mcR]mulrC (addrC h) ; over).
  under [in X in _ /\ X]eq_fun; first (move=> h; rewrite [(_ *: _)%mcR]mulrC (addrC h) ; over).
  ext => [[H1 H2]|H].
  - by apply: cvg_toP.
- split.
  + by apply: cvgP H.
  + by apply/cvg_lim.
Qed.

(*
Lemma cvg_toS {A B : Type} (F G : set_system A) (f : A -> B) l : F `<=` G -> f @ [x --> F] --> l -> f @ [x --> G] --> l.
*)

Lemma cvg_dnbhs_at_right (f : R -> R) (p : R) (l : R) :
  f x @[x --> p^'] --> l ->
  f x @[x --> p^'+] --> l.
Proof.
apply: cvg_trans; apply: cvg_app.
by apply: within_subset => r ?; rewrite gt_eqF.
Qed.

Lemma cvg_dnbhs_at_left (f : R -> R) (p : R) (l : R) :
  f x @[x --> p^'] --> l ->
  f x @[x --> p^'-] --> l.
Proof.
apply: cvg_trans; apply: cvg_app.
by apply: within_subset => r ?; rewrite lt_eqF.
Qed.

Definition contl (f : R -> R) (x : R) := {for x, continuous f}.
Lemma contl_def : contl = (fun f : R -> R => fun x : R => tends_real_real (fun h : R => f (Rplus x h)) (f x) (R_of_nat O)).
Proof.
  rewrite/contl. funext => f x /=. rewrite (@continuous_shift _ R^o R^o).
  under [in X in _ = X]eq_fun do (rewrite !coqRE addrC).
  rewrite/tends_real_real/continuous_at/=.
  rewrite -[in X in _ --> X](add0r x) !coqRE.
  transitivity (f (x0 + x)%mcR @[x0 --> (0%mcR)^'-] --> f (0+x)%mcR /\
    f (x0 + x)%mcR @[x0 --> (0%mcR)^'+] --> f (0+x)%mcR).
  - apply propext. apply iff_sym. exact: left_right_continuousP.
  - ext => [[contfxl contfxr]|contfx].
    + exact: cvg_at_right_left_dnbhs.
    + split ; [exact: cvg_dnbhs_at_left | exact: cvg_dnbhs_at_right].
Qed.

Definition differentiable (f : R -> R) (x : R) := @derivable _ R^o R^o f x 1.
Lemma differentiable_def : differentiable = (fun _115574 : R -> R => fun _115575 : R => exists l : R, diffl _115574 l _115575).
Proof.
  rewrite/differentiable/diffl/derivable/=. ext => f x.
  - by move=> ? ; exists (@derive1 R^o R^o f x).
  - by move=>[?[]].
Qed.

*)