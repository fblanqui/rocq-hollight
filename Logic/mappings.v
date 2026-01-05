From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice.
From mathcomp Require Import finmap boolp classical_sets cardinality.
From Stdlib Require Import BinNat Reals List.
From Equations Require Import Equations.
Require Import HOLLight.Real_With_N.mappings.
From HOLLight.Unif Require Import mappings theorems.

Set Bullet Behavior "Strict Subproofs".

Instance WF_CALLORDER : WellFounded CALLORDER := thm_WF_CALLORDER.

Definition istriv_with_witness env n t : {istriv env n t = TT} + {istriv env n t = FF} +
  {istriv env n t = Exception}.
Proof. by case: (istriv env n t) ; auto. Defined.

Lemma lengthN_eqE {A : Type} (l l' : list A) :
  (length l = length l') = (lengthN l = lengthN l').
Proof.
  do 2 rewrite <- length_of_nat_N. apply prop_ext ; intro H.
  now rewrite H. now apply Nnat.Nat2N.inj.
Qed.

Lemma lengthN_gtE {A : Type} (l l' : list A) :
  (length l > length l')%nat = (lengthN l > lengthN l') :> Prop.
Proof.
  rewrite -2!length_of_nat_N/N.gt-Nnat.Nat2N.inj_compare -leP**.
  ext ; apply Compare_dec.nat_compare_gt.
Qed.

Lemma card_setU_min_l {A : Type'} (s1 s2 : set A) :
  finite_set s1 -> finite_set s2 -> card s1 <= card (s1 `|` s2).
Proof.
  intros H1 H2. apply thm_CARD_SUBSET. split.
  apply thm_SUBSET_UNION. now apply thm_FINITE_UNION_IMP.
Qed.

Lemma card_setU_min_r {A : Type'} (s1 s2 : set A) :
  finite_set s1 -> finite_set s2 -> card s2 <= card (s1 `|` s2).
Proof.
  intros H1 H2. apply thm_CARD_SUBSET. split.
  apply thm_SUBSET_UNION. now apply thm_FINITE_UNION_IMP.
Qed.

Lemma finite_set_lUmapfvt : forall l, finite_set (list_Union (map free_variables_term l)).
Proof.
  induction l ; first by [].
  apply thm_FINITE_UNION_IMP. split;auto.
  apply thm_FVT_FINITE.
Qed.

Ltac le_refl := match goal with |- ?a <= ?b => replace b with a ; try reflexivity end.

Opaque card_eq.

Equations? unify (c :list (N*term) * list (term * term)) : 
  option (list (N*term)) by wf c CALLORDER :=
  unify (env,_) with pselect (LOOPFREE env) => {
    unify _ (right _ H) => None;
    unify (env,nil) _ => Some env;
    unify (env , (V n , t') :: eqs) _
    with pselect (In n (map fst env)) => {
      unify (env , (V n , t') :: eqs) (left _ H) (left _ H') =>
        unify (env , (assoc n env , t') :: eqs);
      unify (env , (V n , t') :: eqs) (left _ H) (right _ H')
      with istriv_with_witness env n t' => {
        | inright _ H'' => None;
        | inleft _ (left _ H'') => unify (env,eqs);
        | inleft _ (right _ H'') => unify ((n,t') :: env , eqs)}};
    unify (env , (Fn n l , V n') :: eqs) (left _ H) =>
      unify (env , (V n' , Fn n l) :: eqs);
    unify (env , (Fn n l , Fn n' l') :: eqs) (left _ H)
    with pselect (n = n' /\ length l = length l') => {
      | right _ _ => None;
      | left _ H' => unify (env , zip l l' ++ eqs)}}.
Proof with f_equal.
  1,2,4,5 : right ; repeat split ; auto ; try breakgoal.
  by move:H' ; rewrite lengthN_eqE => [[-> H']] ; breakgoal.
  left. unfold MEASURE. unfold MLEFT. simpl.
  match goal with |- _ < card (setU (setU ?sn ?e1)
    (setU (setU ?e3 ?e2) (setU ?e4 ?e5))) - card ?e5 =>
    remember e1 as s1 ; remember e2 as s2 ; remember e3 as E3 ;
    remember e4 as E4 ; remember e5 as E5 ; remember sn as Sn end.
  assert (Fs1 : finite_set s1). rewrite Heqs1. apply finite_set_lUmapfvt.
  assert (Fs2 : finite_set s2). rewrite Heqs2. apply finite_set_lUmapfvt.
  assert (FE3 : finite_set E3). rewrite HeqE3. apply thm_FVT_FINITE.
  assert (FE4 : finite_set E4). rewrite HeqE4. apply finite_set_lUmapfvt.
  assert (FE5 : finite_set E5). rewrite HeqE5. apply finite_set_lUmapfvt.
  assert (FSn : finite_set Sn). rewrite HeqSn. auto.
  assert (H'0 : ~ IN n E5). intro H1. rewrite HeqE5 in H1.
    rewrite thm_IN_LIST_UNION in H1. unfold Basics.compose in H1.
    rewrite <- (map_map fst V) in H1. induction (map fst env). inversion H1.
    inversion_clear H1. contradiction H'. left. now move:H0 ; ssimpl.
    apply IHl ; auto. intro Hf. apply H'. now right.
  replace (card (setU Sn E5)) with (card E5 + 1).
  match goal with |- ?n - _ < ?m - _ => replace m with n end.
  - rewrite N.sub_add_distr. apply N.sub_lt.
    2 : exact N.lt_0_1.
    assert (Sn_E5 : card (setI Sn E5) = 0).
      match goal with |- card ?a = 0 => replace a with (set0 (T := N)) end.
      rewrite thm_CARD_EQ_0 ; auto.
      ext => k []. rewrite HeqSn => -> H0.
      by move:H'0 ; ssimpl.
    transitivity (card (setU Sn E5) - card E5).
    + le_refl. rewrite thm_CARD_UNION_GEN.
      match goal with |- _ = _ - ?a - _ => replace a with 0 end.
      rewrite <- N.add_sub_assoc. rewrite <- N.add_sub_assoc.
      match goal with |- _ = _ + ?a => replace a with 0 end.
      rewrite N.add_0_r HeqSn. replace [set n] with (INSERT n set0).
      rewrite thm_CARD_SING. reflexivity. by ssimpl.
      generalize (card E5) as k. apply N.peano_ind. auto.
      intros k IHk. rewrite succ_eq_add_1. rewrite {1}N.add_comm.
      rewrite N.sub_add_distr. rewrite <- N.add_sub_assoc.
      rewrite <- N.add_sub_assoc. now rewrite Nadd_sub. now rewrite N.sub_0_r.
      apply N.le_0_l. now rewrite N.sub_0_r. apply N.le_0_l. auto.
    + apply N.sub_le_mono_r. rewrite 2!setUA.
      apply card_setU_min_r. apply thm_FINITE_UNION_IMP.
      split ; apply thm_FINITE_UNION_IMP ; auto.
      apply thm_FINITE_UNION_IMP. auto.
  - f_equal. rewrite ?setUA (setUC Sn)...
    rewrite -?setUA...
    rewrite ?setUA 2!(setUC _ E3) -?setUA...
    rewrite (setUC E4) ?setUA... apply setUC.
  - rewrite HeqSn (proj2 thm_CARD_CLAUSES) ; auto.
    if_intro. easy. lia.
Qed.

Transparent card_eq.

Lemma unify_def : unify = (@ε ((prod N (prod N (prod N (prod N N)))) -> (prod (list (prod N term)) (list (prod term term))) -> option (list (prod N term))) (fun unify' : (prod N (prod N (prod N (prod N N)))) -> (prod (list (prod N term)) (list (prod term term))) -> option (list (prod N term)) => forall _268410 : prod N (prod N (prod N (prod N N))), forall pr : prod (list (prod N term)) (list (prod term term)), (unify' _268410 pr) = (@COND (option (list (prod N term))) (~ (LOOPFREE (@fst (list (prod N term)) (list (prod term term)) pr))) (@None (list (prod N term))) (@COND (option (list (prod N term))) ((@snd (list (prod N term)) (list (prod term term)) pr) = (@nil (prod term term))) (@Some (list (prod N term)) (@fst (list (prod N term)) (list (prod term term)) pr)) (@tpcases (option (list (prod N term))) (fun f : N => fun fargs : list term => fun g : N => fun gargs : list term => @COND (option (list (prod N term))) ((f = g) /\ ((@lengthN term fargs) = (@lengthN term gargs))) (unify' _268410 (@pair (list (prod N term)) (list (prod term term)) (@fst (list (prod N term)) (list (prod term term)) pr) (@app (prod term term) (@zip term term fargs gargs) (@tl (prod term term) (@snd (list (prod N term)) (list (prod term term)) pr))))) (@None (list (prod N term)))) (fun x : N => fun t : term => @COND (option (list (prod N term))) (@List.In N x (@List.map (prod N term) N (@fst N term) (@fst (list (prod N term)) (list (prod term term)) pr))) (unify' _268410 (@pair (list (prod N term)) (list (prod term term)) (@fst (list (prod N term)) (list (prod term term)) pr) (@cons (prod term term) (@pair term term (@assoc N term x (@fst (list (prod N term)) (list (prod term term)) pr)) t) (@tl (prod term term) (@snd (list (prod N term)) (list (prod term term)) pr))))) (@COND (option (list (prod N term))) ((istriv (@fst (list (prod N term)) (list (prod term term)) pr) x t) = Exception) (@None (list (prod N term))) (@COND (option (list (prod N term))) ((istriv (@fst (list (prod N term)) (list (prod term term)) pr) x t) = TT) (unify' _268410 (@pair (list (prod N term)) (list (prod term term)) (@fst (list (prod N term)) (list (prod term term)) pr) (@tl (prod term term) (@snd (list (prod N term)) (list (prod term term)) pr)))) (unify' _268410 (@pair (list (prod N term)) (list (prod term term)) (@cons (prod N term) (@pair N term x t) (@fst (list (prod N term)) (list (prod term term)) pr)) (@tl (prod term term) (@snd (list (prod N term)) (list (prod term term)) pr))))))) (fun f : N => fun args : list term => fun x : N => unify' _268410 (@pair (list (prod N term)) (list (prod term term)) (@fst (list (prod N term)) (list (prod term term)) pr) (@cons (prod term term) (@pair term term (V x) (Fn f args)) (@tl (prod term term) (@snd (list (prod N term)) (list (prod term term)) pr))))) (@mappings.hd (prod term term) (@snd (list (prod N term)) (list (prod term term)) pr)))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 N0))))))))))))).
Proof.
  align_ε.
  - intros (env,eqs). funelim (unify (env,eqs)) ;
    if_triv ; if_triv ; try discriminate ; unfold tpcases ; simpl.
    all : rewrite ?H'' -?lengthN_eqE ; repeat if_triv.
  - intros g _ Hg. ext => [[env eqs]]. funelim (unify (env,eqs)) ;
    rewrite Hg ; (try match goal with H : _ |- _ =>
      specialize (H g Hg) as H ; match type of H with _ = ?b =>
        transitivity b ; auto end end) ; (* rewrite is not working for some reason *)
        clear Hg.
    all : if_triv ; if_triv ; try discriminate ; unfold tpcases ; simpl.
    all : rewrite ?H'' -?lengthN_eqE ; repeat if_triv.
Qed.

Definition unifies v l := Forall (fun c => termsubst v (fst c) = termsubst v (snd c)) l.

Lemma unifies_def : unifies = (fun _268411 : N -> term => fun _268412 : list (prod term term) => @List.Forall (prod term term) (@ε ((prod term term) -> Prop) (fun f : (prod term term) -> Prop => forall s : term, forall t : term, @eq Prop (f (@pair term term s t)) ((termsubst _268411 s) = (termsubst _268411 t)))) _268412).
Proof.
  funext=> v l. unfold unifies. f_equal.
  align_ε. reflexivity.
  intros f' H H'. funext=>[[t t']]. now rewrite H'.
Qed.

Inductive is_None (A : Type) : option A -> Prop :=
  is_None_def : is_None A None.

Definition THE {_211969 : Type'} : (option _211969) -> _211969 := @ε ((prod N (prod N N)) -> (option _211969) -> _211969) (fun THE' : (prod N (prod N N)) -> (option _211969) -> _211969 => forall _274433 : prod N (prod N N), forall x : _211969, (THE' _274433 (@Some _211969 x)) = x) (@pair N (prod N N) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))))).

Definition the {A : Type'} (x : option A) :=
  match x with None => THE None | Some a => a end.

Lemma THE_def {_211969 : Type'} : (@the _211969) = (@ε ((prod N (prod N N)) -> (option _211969) -> _211969) (fun THE' : (prod N (prod N N)) -> (option _211969) -> _211969 => forall _274433 : prod N (prod N N), forall x : _211969, (THE' _274433 (@Some _211969 x)) = x) (@pair N (prod N N) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0))))))))))).
Proof. partial_align (is_None _211969). Qed.

Definition unifier l := fold_right valmod V (SOLVE nil l).

Lemma unifier_def : unifier = (fun _274434 : list (prod N term) => @LET (list (prod N term)) (N -> term) (fun sol : list (prod N term) => @LET_END (N -> term) (@fold_right_with_perm_args (prod N term) (N -> term) (@valmod term N) sol V)) (SOLVE (@nil (prod N term)) _274434)).
Proof erefl.

Definition Unifies subst E := forall f f' : form,
  IN f E /\ IN f' E -> formsubst subst f = formsubst subst f'.

Lemma Unifies_def : Unifies = (fun _275904 : N -> term => fun _275905 : form -> Prop => all (fun p : form => all (fun q : form => ((@IN form p _275905) /\ (@IN form q _275905)) -> eq (formsubst _275904 p) (formsubst _275904 q)))).
Proof erefl.

Definition mgu : (form -> Prop) -> N -> term := fun _276282 : form -> Prop => @ε (N -> term) (fun i : N -> term => (Unifies i _276282) /\ (forall j : N -> term, (Unifies j _276282) -> forall p : form, (qfree p) -> (formsubst j p) = (formsubst j (formsubst i p)))).

Lemma mgu_def : mgu = (fun _276282 : form -> Prop => @ε (N -> term) (fun i : N -> term => (Unifies i _276282) /\ (all (fun j : N -> term => (Unifies j _276282) -> all (fun p : form => (qfree p) -> eq (formsubst j p) (formsubst j (formsubst i p))))))).
Proof erefl.

Definition o {A B C : Type'} : (B -> C) -> (A -> B) -> A -> C := fun f : B -> C => fun g : A -> B => fun x : A => f (g x).

Definition ismgu E subst :=
  Unifies subst E /\
  (forall subst' : N -> term, Unifies subst' E ->
  exists subst'' : N -> term, termsubst subst' = (fun x => termsubst subst'' (termsubst subst x))).

Lemma ismgu_def : ismgu = (fun _276290 : form -> Prop => fun _276291 : N -> term => (Unifies _276291 _276290) /\ (all (fun j : N -> term => (Unifies j _276290) -> ex (fun k : N -> term => eq (termsubst j) (@o term term term (termsubst k) (termsubst _276291)))))).
Proof erefl.

Definition renaming (subst : N -> term) :=
  exists subst' : N -> term, forall t,
  (termsubst subst' (termsubst subst t)) = t /\
  (termsubst subst (termsubst subst' t)) = t.

Lemma renaming_def : renaming = (fun _276319 : N -> term => exists j : N -> term, ((@Basics.compose term term term (termsubst j) (termsubst _276319)) = (@Datatypes.id term)) /\ ((@Basics.compose term term term (termsubst _276319) (termsubst j)) = (@Datatypes.id term))).
Proof.
  ext=> subst [subst' H] ; exists subst'.
  - split ; ext ; apply H.
  - intro t ; split ; revert t ; apply ext_fun ; apply H.
Qed.

(*****************************************************************************)
(* Logic/resolution.ml *)
(*****************************************************************************)

Definition atom f := match f with Atom _ _ => True | _ => False end.

Lemma atom_def : atom = (@ε ((prod N (prod N (prod N N))) -> form -> Prop) (fun atom' : (prod N (prod N (prod N N))) -> form -> Prop => forall _276403 : prod N (prod N (prod N N)), ((atom' _276403 FFalse) = False) /\ ((forall p : N, forall l : list term, (atom' _276403 (Atom p l)) = True) /\ ((forall q : form, forall r : form, (atom' _276403 (FImp q r)) = False) /\ (forall x : N, forall q : form, (atom' _276403 (FAll x q)) = False)))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))))))).
Proof. total_align. Qed.

(* negatomic formulae *)
Definition literal f :=
  match f with
  | Atom _ _ | FImp (Atom _ _) FFalse => True
  | _ => False end.

Lemma literal_def : literal = (fun _276404 : form => (atom _276404) \/ (exists q : form, (atom q) /\ (_276404 = (Not q)))).
Proof.
  ext=>f H.
  - destruct f;auto. destruct f1 ; destruct f2 ; auto. right.
    now exists (Atom n l).
  - destruct H as [H|(f',(H,e))]. induction f;auto. destruct H. rewrite e.
    now induction f'.
Qed.

(* finite set of negatomic formulae *)
Definition clause c := finite_set c /\ c `<=` literal.

Lemma clause_def : clause = (fun _276409 : form -> Prop => (@finite_set form _276409) /\ (forall p : form, (@IN form p _276409) -> literal p)).
Proof. by ssimpl. Qed.

Inductive negative : form -> Prop := negative_intro : forall f, negative (Not f).

#[global]
Hint Constructors negative : core.

Lemma negative_def : negative = (fun _276554 : form => exists q : form, _276554 = (Not q)).
Proof.
  by ext => [f [] | f [f' ->]] ; eauto.
Qed.

Inductive positive : form -> Prop :=
  | positive_FFalse : positive FFalse
  | positive_Atom : forall n l, positive (Atom n l)
  | positive_FImp : forall f f', f' <> FFalse -> positive (FImp f f')
  | positive_FAll : forall n f, positive (FAll n f).

#[global]
Hint Constructors positive : core.

Lemma positive_def : positive = (fun _276559 : form => ~ (negative _276559)).
Proof.
  ext => f H.
  by inversion 1 ; inversion H ; subst f ; inversion H0 ; try injection H3.
  by destruct f ; auto ; destruct f2 ; only 1 : contradiction H ; constructor.
Qed.

Definition FNot f := match f with FImp f' FFalse => f' | _ => Not f end.

Lemma FNot_def : FNot = (fun _276564 : form => @COND form (negative _276564) (@ε form (fun q : form => (Not q) = _276564)) (Not _276564)).
Proof.
  ext => f ; if_intro => [{f}[f]|H] ; first by align_ε => // ? _ [=].
  by move:f H => [] // ? [] // H ; contradiction H.
Qed.

Definition resolve f cl cl' := cl `\ f `|` cl' `\ (FNot f).

Lemma resolve_def : resolve = (fun _276622 : form => fun _276623 : form -> Prop => fun _276624 : form -> Prop => @setU form (@DELETE form _276623 _276622) (@DELETE form _276624 (FNot _276622))).
Proof erefl.

Inductive presproof (hyps : set (set form)) : set form -> Prop :=
  | presproof_assumption : forall cl, hyps cl -> presproof hyps cl
  | presproof_resolve : forall f cl cl', presproof hyps cl ->
                        presproof hyps cl' -> cl f -> cl' (FNot f) ->
                        presproof hyps (resolve f cl cl').

Lemma presproof_def : presproof = (fun hyps' : (form -> Prop) -> Prop => fun a : form -> Prop => forall presproof' : (form -> Prop) -> Prop, (forall a' : form -> Prop, ((@IN (form -> Prop) a' hyps') \/ (exists p : form, exists cl1 : form -> Prop, exists cl2 : form -> Prop, (a' = (resolve p cl1 cl2)) /\ ((presproof' cl1) /\ ((presproof' cl2) /\ ((@IN form p cl1) /\ (@IN form (FNot p) cl2)))))) -> presproof' a') -> presproof' a).
Proof. ssimpl ; ind_align. Qed.

Definition interp cl := fold_right FOr FFalse (list_of_set cl).

Lemma interp_def : interp = (fun _276649 : form -> Prop => @fold_right_with_perm_args form form FOr (@list_of_set form _276649) FFalse).
Proof erefl.

Definition instance_of cl cl' := (exists subst, cl = formsubst subst @` cl').

Lemma instance_of_def : instance_of = (fun _282937 : form -> Prop => fun _282938 : form -> Prop => ex (fun i : N -> term => eq _282937 (@IMAGE form form (formsubst i) _282938))).
Proof erefl.

Definition FVS cl := UNIONS (free_variables @` cl).

Lemma FVS_def : FVS = (fun _282949 : form -> Prop => @UNIONS N (@GSPEC (N -> Prop) (fun GEN_PVAR_527 : N -> Prop => exists p : form, @SETSPEC (N -> Prop) GEN_PVAR_527 (@IN form p _282949) (free_variables p)))).
Proof. by extall ; ssimpl. Qed.

Definition rename : (form -> Prop) -> (N -> Prop) -> N -> term := @ε ((prod N (prod N (prod N (prod N (prod N N))))) -> (form -> Prop) -> (N -> Prop) -> N -> term) (fun i : (prod N (prod N (prod N (prod N (prod N N))))) -> (form -> Prop) -> (N -> Prop) -> N -> term => forall _285948 : prod N (prod N (prod N (prod N (prod N N)))), forall cl : form -> Prop, forall s : N -> Prop, ((@finite_set N s) /\ (clause cl)) -> (renaming (i _285948 cl s)) /\ ((@setI N (FVS (@IMAGE form form (formsubst (i _285948 cl s)) cl)) s) = (@set0 N))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0))))))))))))).

Lemma rename_def : rename = (@ε ((prod N (prod N (prod N (prod N (prod N N))))) -> (form -> Prop) -> (N -> Prop) -> N -> term) (fun i : (prod N (prod N (prod N (prod N (prod N N))))) -> (form -> Prop) -> (N -> Prop) -> N -> term => all (fun _285948 : prod N (prod N (prod N (prod N (prod N N)))) => all (fun cl : form -> Prop => all (fun s : N -> Prop => ((@finite_set N s) /\ (clause cl)) -> (renaming (i _285948 cl s)) /\ (eq (@setI N (FVS (@IMAGE form form (formsubst (i _285948 cl s)) cl)) s) (@set0 N)))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))))))))).
Proof erefl.

Inductive resproof (hyps : set (set form)) : set form -> Prop :=
  | resproof_assumption : forall cl, hyps cl -> resproof hyps cl
  | resproof_rm_opposable :
      forall cl1 cl2 cl2' ps1 ps2 subst, resproof hyps cl1 -> resproof hyps cl2 ->
      formsubst (rename cl2 (FVS cl1)) @` cl2 = cl2' -> ps1 `<=` cl1 ->
      ps2 `<=` cl2' -> ps1 <> set0 -> ps2 <> set0 ->
      (exists subst', Unifies subst' (ps1 `|` FNot @` ps2)) ->
      mgu (ps1 `|` FNot @` ps2) = subst ->
      resproof hyps ([set formsubst subst x | x in (cl1 `\` ps1 `|` cl2' `\` ps2)]).

Lemma resproof_def : resproof = (fun hyps' : (form -> Prop) -> Prop => fun a : form -> Prop => forall resproof' : (form -> Prop) -> Prop, (forall a' : form -> Prop, ((@IN (form -> Prop) a' hyps') \/ (exists cl1 : form -> Prop, exists cl2 : form -> Prop, exists cl2' : form -> Prop, exists ps1 : form -> Prop, exists ps2 : form -> Prop, exists i : N -> term, (a' = (@IMAGE form form (formsubst i) (@setU form (@setD form cl1 ps1) (@setD form cl2' ps2)))) /\ ((resproof' cl1) /\ ((resproof' cl2) /\ (((@IMAGE form form (formsubst (rename cl2 (FVS cl1))) cl2) = cl2') /\ ((@subset form ps1 cl1) /\ ((@subset form ps2 cl2') /\ ((~ (ps1 = (@set0 form))) /\ ((~ (ps2 = (@set0 form))) /\ ((exists i' : N -> term, Unifies i' (@setU form ps1 (@GSPEC form (fun GEN_PVAR_533 : form => exists p : form, @SETSPEC form GEN_PVAR_533 (@IN form p ps2) (FNot p))))) /\ ((mgu (@setU form ps1 (@GSPEC form (fun GEN_PVAR_534 : form => exists p : form, @SETSPEC form GEN_PVAR_534 (@IN form p ps2) (FNot p))))) = i))))))))))) -> resproof' a') -> resproof' a).
Proof.
  ssimpl ; ind_align.
  - breakgoal by rewrite -[fun x => exists p, [set x' | ps2 p /\ x = x'] (FNot p)]/(GSPEC(
      fun x => exists p, [set x' | (fun p' ps2' => ps2' p' ) p ps2 /\ x = x'] (FNot p)))
    -IN_def SPEC_IMAGE.
  - apply resproof_rm_opposable with (cl2 := x1) ; auto.
    1,2 : rewrite -[fun x => exists p, [set x' | x4 p /\ x = x'] (FNot p)]/(GSPEC(
      fun x => exists p, [set x' | (fun p' ps2' => ps2' p' ) p x4 /\ x = x'] (FNot p)))
    -IN_def SPEC_IMAGE in H7,H8.
    by exists x6. by [].
Qed.

Definition isaresolvent cl c := match c with (cl1,cl2) =>
  let y := (formsubst (rename cl2 (FVS cl1))) @` cl2 in
  exists ps1 ps2 : form -> Prop, subset ps1 cl1 /\ subset ps2 y /\
  ps1 <> set0 /\ ps2 <> set0 /\
  (exists subst : N -> term, Unifies subst (ps1 `|` (FNot @` ps2))) /\
  cl = formsubst (mgu (ps1 `|` FNot @` ps2)) @` (cl1 `\` ps1 `|` y `\` ps2) end.

Lemma isaresolvent_def : isaresolvent = (fun _289554 : form -> Prop => fun _289555 : prod (form -> Prop) (form -> Prop) => @LET (form -> Prop) Prop (fun cl2' : form -> Prop => @LET_END Prop (exists ps1 : form -> Prop, exists ps2 : form -> Prop, (@subset form ps1 (@fst (form -> Prop) (form -> Prop) _289555)) /\ ((@subset form ps2 cl2') /\ ((~ (ps1 = (@set0 form))) /\ ((~ (ps2 = (@set0 form))) /\ ((exists i : N -> term, Unifies i (@setU form ps1 (@GSPEC form (fun GEN_PVAR_540 : form => exists p : form, @SETSPEC form GEN_PVAR_540 (@IN form p ps2) (FNot p))))) /\ (@LET (N -> term) Prop (fun i : N -> term => @LET_END Prop (_289554 = (@IMAGE form form (formsubst i) (@setU form (@setD form (@fst (form -> Prop) (form -> Prop) _289555) ps1) (@setD form cl2' ps2))))) (mgu (@setU form ps1 (@GSPEC form (fun GEN_PVAR_541 : form => exists p : form, @SETSPEC form GEN_PVAR_541 (@IN form p ps2) (FNot p)))))))))))) (@IMAGE form form (formsubst (rename (@snd (form -> Prop) (form -> Prop) _289555) (FVS (@fst (form -> Prop) (form -> Prop) _289555)))) (@snd (form -> Prop) (form -> Prop) _289555))).
Proof.
  by ext => cl [cl1 cl2] [ps1 [ps2 H]] ; exist ps1 ps2 ; move: H ; ssimpl=> H ;
    full_destruct ; repeat split ; eauto.
Qed.

(*****************************************************************************)
(* Logic/given.ml *)
(*****************************************************************************)

Definition FIRSTN {A : Type'} (n : N) (l : list A) := firstn (N.to_nat n) l.

Lemma FIRSTN_def {_216234 : Type'} : (@FIRSTN _216234) = (@ε ((prod N (prod N (prod N (prod N (prod N N))))) -> N -> (list _216234) -> list _216234) (fun FIRSTN' : (prod N (prod N (prod N (prod N (prod N N))))) -> N -> (list _216234) -> list _216234 => forall _289585 : prod N (prod N (prod N (prod N (prod N N)))), (forall l : list _216234, (FIRSTN' _289585 (NUMERAL N0) l) = (@nil _216234)) /\ (forall n : N, forall l : list _216234, (FIRSTN' _289585 (N.succ n) l) = (@COND (list _216234) (l = (@nil _216234)) (@nil _216234) (@cons _216234 (@mappings.hd _216234 l) (FIRSTN' _289585 n (@tl _216234 l)))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))))))))).
Proof.
  N_rec_align.
  by if_list ; rewrite/FIRSTN Nnat.N2Nat.inj_succ ; case l.
Qed.

Definition tautologous cl := (exists f : form, cl f /\ cl (FNot f)).

Lemma tautologous_def : tautologous = (fun _290199 : form -> Prop => exists p : form, (@IN form p _290199) /\ (@IN form (FNot p) _290199)).
Proof. by ssimpl. Qed.

Definition subsumes cl cl' := exists subst, formsubst subst @` cl `<=` cl'.

Lemma subsumes_def : subsumes = (fun _290204 : form -> Prop => fun _290205 : form -> Prop => ex (fun i : N -> term => @subset form (@IMAGE form form (formsubst i) _290204) _290205)).
Proof erefl.

Definition SUBSUMES (s s' : set (set form)) := forall cl', s' cl' -> exists cl, s cl /\ subsumes cl cl'.

Lemma SUBSUMES_def : SUBSUMES = (fun _290276 : (form -> Prop) -> Prop => fun _290277 : (form -> Prop) -> Prop => forall cl' : form -> Prop, (@IN (form -> Prop) cl' _290277) -> exists cl : form -> Prop, (@IN (form -> Prop) cl _290276) /\ (subsumes cl cl')).
Proof. by ssimpl. Qed.

Definition allresolvents (s s' : set (set form)) cl :=
  (exists c1 c2, s c1 /\ s' c2 /\ isaresolvent cl (c1, c2)).

Lemma allresolvents_def : allresolvents = (fun _290388 : (form -> Prop) -> Prop => fun _290389 : (form -> Prop) -> Prop => @GSPEC (form -> Prop) (fun GEN_PVAR_542 : form -> Prop => exists c : form -> Prop, @SETSPEC (form -> Prop) GEN_PVAR_542 (exists c1 : form -> Prop, exists c2 : form -> Prop, (@IN (form -> Prop) c1 _290388) /\ ((@IN (form -> Prop) c2 _290389) /\ (isaresolvent c (@pair (form -> Prop) (form -> Prop) c1 c2)))) c)).
Proof. by extall ; ssimpl. Qed.

Definition allntresolvents s s' cl := allresolvents s s' cl /\ ~ tautologous cl.

Lemma allntresolvents_def : allntresolvents = (fun _290400 : (form -> Prop) -> Prop => fun _290401 : (form -> Prop) -> Prop => @GSPEC (form -> Prop) (fun GEN_PVAR_543 : form -> Prop => exists r : form -> Prop, @SETSPEC (form -> Prop) GEN_PVAR_543 ((@IN (form -> Prop) r (allresolvents _290400 _290401)) /\ (~ (tautologous r))) r)).
Proof. by extall ; ssimpl. Qed.

Import seq.
Import List.
Definition resolvents cl (l : list (set form)) := [list of allresolvents [set cl] [set` l]].

Lemma resolvents_def : resolvents = (fun _315994 : form -> Prop => fun _315995 : list (form -> Prop) => @list_of_set (form -> Prop) (allresolvents (@INSERT (form -> Prop) _315994 (@set0 (form -> Prop))) (@set_of_list (form -> Prop) _315995))).
Proof. by extall ; ssimpl. Qed.

Fixpoint replace (cl : form -> Prop) l :=
  match l with
  | nil => cl::nil
  | cl'::l' => if subsumes cl cl' then cl::l' else cl'::(replace cl l') end.

Lemma replace_def : replace = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (form -> Prop) -> (list (form -> Prop)) -> list (form -> Prop)) (fun replace' : (prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (form -> Prop) -> (list (form -> Prop)) -> list (form -> Prop) => forall _316246 : prod N (prod N (prod N (prod N (prod N (prod N N))))), (forall cl : form -> Prop, (replace' _316246 cl (@nil (form -> Prop))) = (@cons (form -> Prop) cl (@nil (form -> Prop)))) /\ (forall c : form -> Prop, forall cl : form -> Prop, forall cls : list (form -> Prop), (replace' _316246 cl (@cons (form -> Prop) c cls)) = (@COND (list (form -> Prop)) (subsumes cl c) (@cons (form -> Prop) cl cls) (@cons (form -> Prop) c (replace' _316246 cl cls))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0))))))))))))))).
Proof. total_align. Qed.

Definition incorporate cl cl' l :=
  if tautologous cl' \/ Exists (fun cl0 : form -> Prop => subsumes cl0 cl') (cl :: l)
    then l else replace cl' l.

Lemma incorporate_def : incorporate =(fun _316633 : form -> Prop => fun _316634 : form -> Prop => fun _316635 : list (form -> Prop) => @COND (list (form -> Prop)) ((tautologous _316634) \/ (@List.Exists (form -> Prop) (fun c : form -> Prop => subsumes c _316634) (@cons (form -> Prop) _316633 _316635))) _316635 (replace _316634 _316635)).
Proof erefl.

Definition insert {A : Type'} (a : A) l := if In a l then l else a :: l.

Lemma insert_def {_218810 : Type'} :  (@insert _218810) = (fun _316826 : _218810 => fun _316827 : list _218810 => @COND (list _218810) (@List.In _218810 _316826 _316827) _316827 (@cons _218810 _316826 _316827)).
Proof erefl.

Definition step c :=
  match snd c with
  | nil => c
  | a::l' => (insert a (fst c), fold_right (incorporate a) l' (resolvents a (a :: (fst c)))) end.

Lemma step_def : step = (fun _316838 : prod (list (form -> Prop)) (list (form -> Prop)) => @COND (prod (list (form -> Prop)) (list (form -> Prop))) ((@snd (list (form -> Prop)) (list (form -> Prop)) _316838) = (@nil (form -> Prop))) (@pair (list (form -> Prop)) (list (form -> Prop)) (@fst (list (form -> Prop)) (list (form -> Prop)) _316838) (@snd (list (form -> Prop)) (list (form -> Prop)) _316838)) (@LET (list (form -> Prop)) (prod (list (form -> Prop)) (list (form -> Prop))) (fun new : list (form -> Prop) => @LET_END (prod (list (form -> Prop)) (list (form -> Prop))) (@pair (list (form -> Prop)) (list (form -> Prop)) (@insert (form -> Prop) (@mappings.hd (form -> Prop) (@snd (list (form -> Prop)) (list (form -> Prop)) _316838)) (@fst (list (form -> Prop)) (list (form -> Prop)) _316838)) (@fold_right_with_perm_args (form -> Prop) (list (form -> Prop)) (incorporate (@mappings.hd (form -> Prop) (@snd (list (form -> Prop)) (list (form -> Prop)) _316838))) new (@mappings.tl (form -> Prop) (@snd (list (form -> Prop)) (list (form -> Prop)) _316838))))) (resolvents (@mappings.hd (form -> Prop) (@snd (list (form -> Prop)) (list (form -> Prop)) _316838)) (@cons (form -> Prop) (@mappings.hd (form -> Prop) (@snd (list (form -> Prop)) (list (form -> Prop)) _316838)) (@fst (list (form -> Prop)) (list (form -> Prop)) _316838))))).
Proof.
  by ext => [[? l']] * ;  if_list ; destruct l'.
Qed.

Fixpoint given n p :=
  match n with
  | O => p
  | S n => step (given n p) end.

Definition giveN n := given (N.to_nat n).

Lemma given_def : giveN = (@ε ((prod N (prod N (prod N (prod N N)))) -> N -> (prod (list (form -> Prop)) (list (form -> Prop))) -> prod (list (form -> Prop)) (list (form -> Prop))) (fun given' : (prod N (prod N (prod N (prod N N)))) -> N -> (prod (list (form -> Prop)) (list (form -> Prop))) -> prod (list (form -> Prop)) (list (form -> Prop)) => forall _316850 : prod N (prod N (prod N (prod N N))), (forall p : prod (list (form -> Prop)) (list (form -> Prop)), (given' _316850 (NUMERAL N0) p) = p) /\ (forall n : N, forall p : prod (list (form -> Prop)) (list (form -> Prop)), (given' _316850 (N.succ n) p) = (step (given' _316850 n p)))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0))))))))))))).
Proof.
  N_rec_align. intros. unfold giveN. now rewrite (Nnat.N2Nat.inj_succ).
Qed.

Definition Used init n := set_of_list (fst (giveN n init)).
Definition Unused init n := set_of_list (snd (giveN n init)).

Lemma Used_def : Used = (fun _316851 : prod (list (form -> Prop)) (list (form -> Prop)) => fun _316852 : N => @set_of_list (form -> Prop) (@fst (list (form -> Prop)) (list (form -> Prop)) (giveN _316852 _316851))).
Proof erefl.
Lemma Unused_def : Unused = (fun _316863 : prod (list (form -> Prop)) (list (form -> Prop)) => fun _316864 : N => @set_of_list (form -> Prop) (@snd (list (form -> Prop)) (list (form -> Prop)) (giveN _316864 _316863))).
Proof erefl.

Fixpoint Subnat init n :=
  match n with
  | O => set0
  | S n => match snd (given n init) with
    | nil => Subnat init n
    | a::l => INSERT a (Subnat init n) end end.

Definition Sub init n : (form -> Prop) -> Prop := Subnat init (N.to_nat n).

Lemma Sub_def : Sub = (@ε ((prod N (prod N N)) -> (prod (list (form -> Prop)) (list (form -> Prop))) -> N -> (form -> Prop) -> Prop) (fun Sub' : (prod N (prod N N)) -> (prod (list (form -> Prop)) (list (form -> Prop))) -> N -> (form -> Prop) -> Prop => forall _316881 : prod N (prod N N), (forall init : prod (list (form -> Prop)) (list (form -> Prop)), (Sub' _316881 init (NUMERAL N0)) = (@set0 (form -> Prop))) /\ (forall init : prod (list (form -> Prop)) (list (form -> Prop)), forall n : N, (Sub' _316881 init (N.succ n)) = (@COND ((form -> Prop) -> Prop) ((@snd (list (form -> Prop)) (list (form -> Prop)) (giveN n init)) = (@nil (form -> Prop))) (Sub' _316881 init n) (@INSERT (form -> Prop) (@mappings.hd (form -> Prop) (@snd (list (form -> Prop)) (list (form -> Prop)) (giveN n init))) (Sub' _316881 init n))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0))))))))))).
Proof.
  N_rec_align ;if_list ; rewrite/Sub Nnat.N2Nat.inj_succ /giveN /=.
  by case:(snd (given (N.to_nat n) init)).
Qed.

Fixpoint breaknat init n :=
  match n with
  | O => lengthN (snd init)
  | S n => let k := breaknat init n in
           k + lengthN (snd (giveN k init)) end.

Definition break init n := breaknat init (N.to_nat n).

Lemma break_def : break = (@ε ((prod N (prod N (prod N (prod N N)))) -> (prod (list (form -> Prop)) (list (form -> Prop))) -> N -> N) (fun break' : (prod N (prod N (prod N (prod N N)))) -> (prod (list (form -> Prop)) (list (form -> Prop))) -> N -> N => forall _328646 : prod N (prod N (prod N (prod N N))), (forall init : prod (list (form -> Prop)) (list (form -> Prop)), (break' _328646 init (NUMERAL N0)) = (@lengthN (form -> Prop) (@snd (list (form -> Prop)) (list (form -> Prop)) (giveN (NUMERAL N0) init)))) /\ (forall n : N, forall init : prod (list (form -> Prop)) (list (form -> Prop)), (break' _328646 init (N.succ n)) = (N.add (break' _328646 init n) (@lengthN (form -> Prop) (@snd (list (form -> Prop)) (list (form -> Prop)) (giveN (break' _328646 init n) init)))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0))))))))))))).
Proof.
  by N_rec_align ; rewrite/break Nnat.N2Nat.inj_succ.
Qed.

Definition level init n := Sub init (break init n).

Lemma level_def : level = (fun _328647 : prod (list (form -> Prop)) (list (form -> Prop)) => fun _328648 : N => Sub _328647 (break _328647 _328648)).
Proof erefl.

(*****************************************************************************)
(* Logic/linear.ml *)
(*****************************************************************************)

Inductive ppresproof : set (set form) -> set form -> Prop :=
  | ppresproof_assumption : forall cl, clause cl -> ppresproof [set cl] cl
  | ppresproof_resolve : forall f hyps hyps' cl cl', ppresproof hyps cl ->
                        ppresproof hyps' cl' -> cl f -> cl' (FNot f) ->
                        ppresproof (hyps `|` hyps') (resolve f cl cl').

Lemma ppresproof_def : ppresproof = (fun a0 : (form -> Prop) -> Prop => fun a1 : form -> Prop => forall ppresproof' : ((form -> Prop) -> Prop) -> (form -> Prop) -> Prop, (forall a0' : (form -> Prop) -> Prop, forall a1' : form -> Prop, (((a0' = (@INSERT (form -> Prop) a1' (@set0 (form -> Prop)))) /\ (clause a1')) \/ (exists p : form, exists asm1 : (form -> Prop) -> Prop, exists asm2 : (form -> Prop) -> Prop, exists c1 : form -> Prop, exists c2 : form -> Prop, (a0' = (@setU (form -> Prop) asm1 asm2)) /\ ((a1' = (resolve p c1 c2)) /\ ((ppresproof' asm1 c1) /\ ((ppresproof' asm2 c2) /\ ((@IN form p c1) /\ (@IN form (FNot p) c2))))))) -> ppresproof' a0' a1') -> ppresproof' a0 a1).
Proof.
  by ssimpl ; ind_align ; ssimpl ; first left ; last apply ppresproof_assumption.
Qed.

Inductive lpresproof (hyps : set (set form)) : list (set form) -> Prop :=
  | lpresproof_assumption : forall cl, hyps cl -> lpresproof hyps (cl::nil)
  | lpresproof_resolve : forall f cl cl' l, lpresproof hyps (cl::l) ->
                        (hyps cl' \/ In cl' l) -> cl f -> cl' (FNot f) ->
                        lpresproof hyps ((resolve f cl cl')::cl::l).

Lemma lpresproof_def : lpresproof = (fun hyps' : (form -> Prop) -> Prop => fun a : list (form -> Prop) => forall lpresproof' : (list (form -> Prop)) -> Prop, (forall a' : list (form -> Prop), ((exists cl : form -> Prop, (a' = (@cons (form -> Prop) cl (@nil (form -> Prop)))) /\ (@IN (form -> Prop) cl hyps')) \/ (exists c1 : form -> Prop, exists c2 : form -> Prop, exists lis : list (form -> Prop), exists p : form, (a' = (@cons (form -> Prop) (resolve p c1 c2) (@cons (form -> Prop) c1 lis))) /\ ((lpresproof' (@cons (form -> Prop) c1 lis)) /\ (((@IN (form -> Prop) c2 hyps') \/ (@List.In (form -> Prop) c2 lis)) /\ ((@IN form p c1) /\ (@IN form (FNot p) c2)))))) -> lpresproof' a') -> lpresproof' a).
Proof. ssimpl ; ind_align. Qed.

Fixpoint suffix {A : Type} (l : list A) l' :=
  match l' with
  | nil => l = nil
  | _::l'0  => l = l' \/ suffix l l'0 end.

Lemma suffix_def {_224872 : Type'} : (@suffix _224872) = (@ε ((prod N (prod N (prod N (prod N (prod N N))))) -> (list _224872) -> (list _224872) -> Prop) (fun suffix' : (prod N (prod N (prod N (prod N (prod N N))))) -> (list _224872) -> (list _224872) -> Prop => forall _374747 : prod N (prod N (prod N (prod N (prod N N)))), (forall lis : list _224872, (suffix' _374747 lis (@nil _224872)) = (lis = (@nil _224872))) /\ (forall s : _224872, forall lis : list _224872, forall cs : list _224872, (suffix' _374747 lis (@cons _224872 s cs)) = ((lis = (@cons _224872 s cs)) \/ (suffix' _374747 lis cs)))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 N0)))))))))))))).
Proof. total_align. Qed.

Inductive lresproof (hyps : set (set form)) : list (set form) -> Prop :=
  | lresproof_assumption : forall cl, hyps cl -> lresproof hyps (cl::nil)
  | lresproof_resolve : forall cl0 cl cl' l, lresproof hyps (cl::l) ->
                        (hyps cl' \/ In cl' l) -> isaresolvent cl0 (cl,cl') ->
                        lresproof hyps (cl0::cl::l).

Lemma lresproof_def : lresproof = (fun hyps' : (form -> Prop) -> Prop => fun a : list (form -> Prop) => forall lresproof' : (list (form -> Prop)) -> Prop, (forall a' : list (form -> Prop), ((exists cl : form -> Prop, (a' = (@cons (form -> Prop) cl (@nil (form -> Prop)))) /\ (@IN (form -> Prop) cl hyps')) \/ (exists c1 : form -> Prop, exists c2 : form -> Prop, exists lis : list (form -> Prop), exists cl : form -> Prop, (a' = (@cons (form -> Prop) cl (@cons (form -> Prop) c1 lis))) /\ ((lresproof' (@cons (form -> Prop) c1 lis)) /\ (((@IN (form -> Prop) c2 hyps') \/ (@List.In (form -> Prop) c2 lis)) /\ (isaresolvent cl (@pair (form -> Prop) (form -> Prop) c1 c2)))))) -> lresproof' a') -> lresproof' a).
Proof. ssimpl ; ind_align. Qed.

(*****************************************************************************)
(* Logic/support.ml *)
(*****************************************************************************)

Inductive npresproof (hyps : set (set form)) : set form -> N -> Prop :=
  | npresproof_assumption : forall cl, hyps cl -> npresproof hyps cl 1
  | npresproof_resolve : forall f cl cl' n n', npresproof hyps cl n ->
                        npresproof hyps cl' n' -> cl f -> cl' (FNot f) ->
                        npresproof hyps (resolve f cl cl') (N.succ (n+n')).

Lemma npresproof_def : npresproof = (fun hyps' : (form -> Prop) -> Prop => fun a0 : form -> Prop => fun a1 : N => forall npresproof' : (form -> Prop) -> N -> Prop, (forall a0' : form -> Prop, forall a1' : N, (((a1' = (NUMERAL (BIT1 N0))) /\ (@IN (form -> Prop) a0' hyps')) \/ (exists p : form, exists n1 : N, exists n2 : N, exists cl1 : form -> Prop, exists cl2 : form -> Prop, (a0' = (resolve p cl1 cl2)) /\ ((a1' = (N.add n1 (N.add n2 (NUMERAL (BIT1 N0))))) /\ ((npresproof' cl1 n1) /\ ((npresproof' cl2 n2) /\ ((@IN form p cl1) /\ (@IN form (FNot p) cl2))))))) -> npresproof' a0' a1') -> npresproof' a0 a1).
Proof.
  ssimpl ; ind_align.
  breakgoal by rewrite N.add_1_r N.add_succ_r.
  by rewrite N.add_1_r N.add_succ_r ; apply npresproof_resolve.
Qed.

Inductive psresproof (hyps sos : set (set form)) : Prop -> set form -> Prop :=
  | psresproof_assumption : forall cl, hyps cl -> ~ tautologous cl ->
                            psresproof hyps sos (sos cl) cl
  | psresproof_resolve : forall f cl cl' P P', psresproof hyps sos P cl ->
                        psresproof hyps sos P' cl' -> cl f -> cl' (FNot f) ->
                        P \/ P' -> ~ tautologous (resolve f cl cl') ->
                        psresproof hyps sos True (resolve f cl cl').

Lemma psresproof_def : psresproof = (fun hyps' : (form -> Prop) -> Prop => fun sos : (form -> Prop) -> Prop => fun a0 : Prop => fun a1 : form -> Prop => forall psresproof' : Prop -> (form -> Prop) -> Prop, (forall a0' : Prop, forall a1' : form -> Prop, (((a0' = (@IN (form -> Prop) a1' sos)) /\ ((@IN (form -> Prop) a1' hyps') /\ (~ (tautologous a1')))) \/ (exists c1 : form -> Prop, exists c2 : form -> Prop, exists s1 : Prop, exists s2 : Prop, exists p : form, (a0' = True) /\ ((a1' = (resolve p c1 c2)) /\ ((psresproof' s1 c1) /\ ((psresproof' s2 c2) /\ ((@IN form p c1) /\ ((@IN form (FNot p) c2) /\ ((s1 \/ s2) /\ (~ (tautologous (resolve p c1 c2))))))))))) -> psresproof' a0' a1') -> psresproof' a0 a1).
Proof. ssimpl ; ind_align. Qed.

Inductive spresproof (hyps sos : set (set form)) : set form -> Prop :=
  | spresproof_assumption : forall cl, hyps cl -> sos cl ->
                            ~ tautologous cl -> spresproof hyps sos cl
  | spresproof_resolve1 : forall f cl cl', spresproof hyps sos cl ->
                        spresproof hyps sos cl' -> cl f ->
                        cl' (FNot f) -> ~ tautologous (resolve f cl cl') ->
                        spresproof hyps sos (resolve f cl cl')
  | spresproof_resolve2 : forall f cl cl', spresproof hyps sos cl ->
                        hyps cl' -> cl f ->
                        cl' (FNot f) -> ~ tautologous (resolve f cl cl') ->
                        spresproof hyps sos (resolve f cl cl').

Lemma spresproof_def : spresproof = (fun hyps' : (form -> Prop) -> Prop => fun sos : (form -> Prop) -> Prop => fun a : form -> Prop => forall spresproof' : (form -> Prop) -> Prop, (forall a' : form -> Prop, (((@IN (form -> Prop) a' hyps') /\ ((@IN (form -> Prop) a' sos) /\ (~ (tautologous a')))) \/ (exists c1 : form -> Prop, exists c2 : form -> Prop, exists p : form, (a' = (resolve p c1 c2)) /\ ((spresproof' c1) /\ (((spresproof' c2) \/ (@IN (form -> Prop) c2 hyps')) /\ ((@IN form p c1) /\ ((@IN form (FNot p) c2) /\ (~ (tautologous (resolve p c1 c2))))))))) -> spresproof' a') -> spresproof' a).
Proof. ssimpl ; ind_align. Qed.

Inductive sresproof (hyps sos : set (set form)) : set form -> Prop :=
  | sresproof_assumption : forall cl, hyps cl -> sos cl ->
    ~ tautologous cl -> sresproof hyps sos cl
  | sresproof_rm_opposable1 :
      forall cl1 cl2 cl2' ps1 ps2 subst, sresproof hyps sos cl1 -> sresproof hyps sos cl2 ->
      formsubst (rename cl2 (FVS cl1)) @` cl2 = cl2' -> ps1 `<=` cl1 ->
      ps2 `<=` cl2' -> ps1 <> set0 -> ps2 <> set0 ->
      (exists subst', Unifies subst' (ps1 `|` (FNot @` ps2))) ->
      mgu (ps1 `|` (FNot @` ps2)) = subst ->
      ~ tautologous (formsubst subst @` (cl1 `\` ps1 `|` cl2' `\` ps2)) ->
      sresproof hyps sos (formsubst subst @` (cl1 `\` ps1 `|` cl2' `\` ps2))
  | sresproof_rm_opposable2 :
      forall cl1 cl2 cl2' ps1 ps2 subst, sresproof hyps sos cl1 -> hyps cl2 ->
      formsubst (rename cl2 (FVS cl1)) @` cl2 = cl2' -> ps1 `<=` cl1 ->
      ps2 `<=` cl2' -> ps1 <> set0 -> ps2 <> set0 ->
      (exists subst', Unifies subst' (ps1 `|` (FNot @` ps2))) ->
      mgu (ps1 `|` (FNot @` ps2)) = subst ->
      ~ tautologous (formsubst subst @` (cl1 `\` ps1 `|` cl2' `\` ps2)) ->
      sresproof hyps sos (formsubst subst @` (cl1 `\` ps1 `|` cl2' `\` ps2)).

Lemma sresproof_def : sresproof = (fun hyps' : (form -> Prop) -> Prop => fun sos : (form -> Prop) -> Prop => fun a : form -> Prop => forall sresproof' : (form -> Prop) -> Prop, (forall a' : form -> Prop, (((@IN (form -> Prop) a' hyps') /\ ((@IN (form -> Prop) a' sos) /\ (~ (tautologous a')))) \/ (exists cl1 : form -> Prop, exists cl2 : form -> Prop, exists cl2' : form -> Prop, exists ps1 : form -> Prop, exists ps2 : form -> Prop, exists i : N -> term, (a' = (@IMAGE form form (formsubst i) (@setU form (@setD form cl1 ps1) (@setD form cl2' ps2)))) /\ ((sresproof' cl1) /\ (((sresproof' cl2) \/ (@IN (form -> Prop) cl2 hyps')) /\ (((@IMAGE form form (formsubst (rename cl2 (FVS cl1))) cl2) = cl2') /\ ((@subset form ps1 cl1) /\ ((@subset form ps2 cl2') /\ ((~ (ps1 = (@set0 form))) /\ ((~ (ps2 = (@set0 form))) /\ ((exists i' : N -> term, Unifies i' (@setU form ps1 (@GSPEC form (fun GEN_PVAR_589 : form => exists p : form, @SETSPEC form GEN_PVAR_589 (@IN form p ps2) (FNot p))))) /\ (((mgu (@setU form ps1 (@GSPEC form (fun GEN_PVAR_590 : form => exists p : form, @SETSPEC form GEN_PVAR_590 (@IN form p ps2) (FNot p))))) = i) /\ (~ (tautologous (@IMAGE form form (formsubst i) (@setU form (@setD form cl1 ps1) (@setD form cl2' ps2)))))))))))))))) -> sresproof' a') -> sresproof' a).
Proof.
  ssimpl ; ind_align.
  1,2 : by right ; destruct H6 ; repeat eexists ; eauto ; by rewrite -[fun x => exists p, [set x' | ps2 p /\ x = x'] (FNot p)]/(GSPEC(
      fun x => exists p, [set x' | (fun p' ps2' => ps2' p' ) p ps2 /\ x = x'] (FNot p)))
    -IN_def SPEC_IMAGE ; eauto.
  1,2 : rewrite -[fun x => exists p, [set x' | x5 p /\ x = x'] (FNot p)]/(GSPEC(
      fun x => exists p, [set x' | (fun p' ps2' => ps2' p' ) p x5 /\ x = x'] (FNot p)))
    -IN_def SPEC_IMAGE in H7,H8 ; econstructor ; by eauto.
Qed.

(*****************************************************************************)
(* Logic/positive.ml *)
(*****************************************************************************)

Definition allpositive cl := cl `<=` positive.

Lemma allpositive_def : allpositive = (fun _460164 : form -> Prop => forall p : form, (@IN form p _460164) -> positive p).
Proof. by ssimpl. Qed.

Inductive pposresproof (hyps : set (set form)) : set form -> Prop :=
  | pposresproof_assumption : forall cl, hyps cl -> pposresproof hyps cl
  | pposresproof_resolve1 : forall f cl cl', pposresproof hyps cl ->
                        pposresproof hyps cl' -> allpositive cl ->
                        cl f -> cl' (FNot f) ->
                        pposresproof hyps (resolve f cl cl')
  | pposresproof_resolve2 : forall f cl cl', pposresproof hyps cl ->
                        pposresproof hyps cl' -> allpositive cl' ->
                        cl f -> cl' (FNot f) ->
                        pposresproof hyps (resolve f cl cl').

Lemma pposresproof_def : pposresproof = (fun hyps' : (form -> Prop) -> Prop => fun a : form -> Prop => forall pposresproof' : (form -> Prop) -> Prop, (forall a' : form -> Prop, ((@IN (form -> Prop) a' hyps') \/ (exists p : form, exists cl1 : form -> Prop, exists cl2 : form -> Prop, (a' = (resolve p cl1 cl2)) /\ ((pposresproof' cl1) /\ ((pposresproof' cl2) /\ (((allpositive cl1) \/ (allpositive cl2)) /\ ((@IN form p cl1) /\ (@IN form (FNot p) cl2))))))) -> pposresproof' a') -> pposresproof' a).
Proof. ssimpl ; ind_align. Qed.

Inductive psemresproof (TrueVar : set form) (hyps : set (set form)) : set form -> Prop :=
  | psemresproof_assumption : forall cl, hyps cl -> psemresproof TrueVar hyps cl
  | psemresproof_resolve1 : forall f cl cl', psemresproof TrueVar hyps cl ->
                        psemresproof TrueVar hyps cl' ->
                        ~pholds TrueVar (interp cl) ->
                        cl f -> cl' (FNot f) ->
                        psemresproof TrueVar hyps (resolve f cl cl')
  | psemresproof_resolve2 : forall f cl cl', psemresproof TrueVar hyps cl ->
                        psemresproof TrueVar hyps cl' ->
                        ~pholds TrueVar (interp cl') ->
                        cl f -> cl' (FNot f) ->
                        psemresproof TrueVar hyps (resolve f cl cl').

Lemma psemresproof_def : psemresproof = (fun v : form -> Prop => fun hyps' : (form -> Prop) -> Prop => fun a : form -> Prop => forall psemresproof' : (form -> Prop) -> Prop, (forall a' : form -> Prop, ((@IN (form -> Prop) a' hyps') \/ (exists p : form, exists cl1 : form -> Prop, exists cl2 : form -> Prop, (a' = (resolve p cl1 cl2)) /\ ((psemresproof' cl1) /\ ((psemresproof' cl2) /\ (((~ (pholds v (interp cl1))) \/ (~ (pholds v (interp cl2)))) /\ ((@IN form p cl1) /\ (@IN form (FNot p) cl2))))))) -> psemresproof' a') -> psemresproof' a).
Proof. ssimpl ; ind_align. Qed.

Definition propflip TrueVar f := if negative f <-> pholds TrueVar f then f else FNot f.

Lemma propflip_def : propflip = (fun _467005 : form -> Prop => fun _467006 : form => @COND form ((negative _467006) = (pholds _467005 _467006)) _467006 (FNot _467006)).
Proof.
  rewrite/COND/propflip.
  apply (f_equal (fun P TrueVar f => if `[< P TrueVar f >] then f else FNot f)).
  by ext => * ; blindrewrite ; firstorder.
Qed.


Inductive posresproof (hyps : set (set form)) : set form -> Prop :=
  | posresproof_assumption : forall cl, hyps cl -> posresproof hyps cl
  | posresproof_rm_opposable1 :
      forall cl1 cl2 cl2' ps1 ps2 subst, posresproof hyps cl1 ->
      posresproof hyps cl2 -> allpositive cl1 ->
      formsubst (rename cl2 (FVS cl1)) @` cl2 = cl2' -> ps1 `<=` cl1 ->
      ps2 `<=` cl2' -> ps1 <> set0 -> ps2 <> set0 ->
      (exists subst', Unifies subst' (ps1 `|` (FNot @` ps2))) ->
      mgu (ps1 `|` (FNot @` ps2)) = subst ->
      posresproof hyps (formsubst subst @` (cl1 `\` ps1 `|` cl2' `\` ps2))
  | posresproof_rm_opposable2 :
      forall cl1 cl2 cl2' ps1 ps2 subst, posresproof hyps cl1 ->
      posresproof hyps cl2 -> allpositive cl2 ->
      formsubst (rename cl2 (FVS cl1)) @` cl2 = cl2' -> ps1 `<=` cl1 ->
      ps2 `<=` cl2' -> ps1 <> set0 -> ps2 <> set0 ->
      (exists subst', Unifies subst' (ps1 `|` (FNot @` ps2))) ->
      mgu (ps1 `|` (FNot @` ps2)) = subst ->
      posresproof hyps (formsubst subst @` (cl1 `\` ps1 `|` cl2' `\` ps2)).

Lemma posresproof_def : posresproof = (fun hyps' : (form -> Prop) -> Prop => fun a : form -> Prop => forall posresproof' : (form -> Prop) -> Prop, (forall a' : form -> Prop, ((@IN (form -> Prop) a' hyps') \/ (exists cl1 : form -> Prop, exists cl2 : form -> Prop, exists cl2' : form -> Prop, exists ps1 : form -> Prop, exists ps2 : form -> Prop, exists i : N -> term, (a' = (@IMAGE form form (formsubst i) (@setU form (@setD form cl1 ps1) (@setD form cl2' ps2)))) /\ ((posresproof' cl1) /\ ((posresproof' cl2) /\ (((allpositive cl1) \/ (allpositive cl2)) /\ (((@IMAGE form form (formsubst (rename cl2 (FVS cl1))) cl2) = cl2') /\ ((@subset form ps1 cl1) /\ ((@subset form ps2 cl2') /\ ((~ (ps1 = (@set0 form))) /\ ((~ (ps2 = (@set0 form))) /\ ((exists i' : N -> term, Unifies i' (@setU form ps1 (@GSPEC form (fun GEN_PVAR_622 : form => exists p : form, @SETSPEC form GEN_PVAR_622 (@IN form p ps2) (FNot p))))) /\ ((mgu (@setU form ps1 (@GSPEC form (fun GEN_PVAR_623 : form => exists p : form, @SETSPEC form GEN_PVAR_623 (@IN form p ps2) (FNot p))))) = i)))))))))))) -> posresproof' a') -> posresproof' a).
Proof.
  ssimpl ; ind_align.
  1,2 : right ; full_destruct ; repeat eexists ; eauto ; by rewrite -[fun x => exists p, [set x' | ps2 p /\ x = x'] (FNot p)]/(GSPEC(
      fun x => exists p, [set x' | (fun p' ps2' => ps2' p' ) p ps2 /\ x = x'] (FNot p)))
    -IN_def SPEC_IMAGE ; eauto.
  1,2 : rewrite -[fun x => exists p, [set x' | x4 p /\ x = x'] (FNot p)]/(GSPEC(
      fun x => exists p, [set x' | (fun p' ps2' => ps2' p' ) p x4 /\ x = x'] (FNot p)))
    -IN_def SPEC_IMAGE in H8,H9 ; econstructor ; by eauto.
Qed.

Inductive semresproof {A : Type'} (M : Structure A) 
  (hyps : set (set form)) : set form -> Prop :=
  | semresproof_assumption : forall cl, hyps cl -> semresproof M hyps cl
  | semresproof_rm_opposable1 :
      forall cl1 cl2 cl2' ps1 ps2 subst, semresproof M hyps cl1 ->
      semresproof M hyps cl2 -> (~ forall v, holds M v (interp cl1)) ->
      formsubst (rename cl2 (FVS cl1)) @` cl2 = cl2' -> ps1 `<=` cl1 ->
      ps2 `<=` cl2' -> ps1 <> set0 -> ps2 <> set0 ->
      (exists subst', Unifies subst' (ps1 `|` (FNot @` ps2))) ->
      mgu (ps1 `|` (FNot @` ps2)) = subst ->
      semresproof M hyps (formsubst subst @` (cl1 `\` ps1 `|` cl2' `\` ps2))
  | semresproof_rm_opposable2 :
      forall cl1 cl2 cl2' ps1 ps2 subst, semresproof M hyps cl1 ->
      semresproof M hyps cl2 -> (~ forall v, holds M v (interp cl2)) ->
      formsubst (rename cl2 (FVS cl1)) @` cl2 = cl2' -> ps1 `<=` cl1 ->
      ps2 `<=` cl2' -> ps1 <> set0 -> ps2 <> set0 ->
      (exists subst', Unifies subst' (ps1 `|` (FNot @` ps2))) ->
      mgu (ps1 `|` (FNot @` ps2)) = subst ->
      semresproof M hyps (formsubst subst @` (cl1 `\` ps1 `|` cl2' `\` ps2)).

Lemma semresproof_def {A : Type'} : (@semresproof A) = (fun M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)) => fun hyps' : (form -> Prop) -> Prop => fun a : form -> Prop => forall semresproof' : (form -> Prop) -> Prop, (forall a' : form -> Prop, ((@IN (form -> Prop) a' hyps') \/ (exists cl1 : form -> Prop, exists cl2 : form -> Prop, exists cl2' : form -> Prop, exists ps1 : form -> Prop, exists ps2 : form -> Prop, exists i : N -> term, (a' = (@IMAGE form form (formsubst i) (@setU form (@setD form cl1 ps1) (@setD form cl2' ps2)))) /\ ((semresproof' cl1) /\ ((semresproof' cl2) /\ (((~ (forall v : N -> A, @holds A M v (interp cl1))) \/ (~ (forall v : N -> A, @holds A M v (interp cl2)))) /\ (((@IMAGE form form (formsubst (rename cl2 (FVS cl1))) cl2) = cl2') /\ ((@subset form ps1 cl1) /\ ((@subset form ps2 cl2') /\ ((~ (ps1 = (@set0 form))) /\ ((~ (ps2 = (@set0 form))) /\ ((exists i' : N -> term, Unifies i' (@setU form ps1 (@GSPEC form (fun GEN_PVAR_629 : form => exists p : form, @SETSPEC form GEN_PVAR_629 (@IN form p ps2) (FNot p))))) /\ ((mgu (@setU form ps1 (@GSPEC form (fun GEN_PVAR_630 : form => exists p : form, @SETSPEC form GEN_PVAR_630 (@IN form p ps2) (FNot p))))) = i)))))))))))) -> semresproof' a') -> semresproof' a).
Proof.
  ext 2 => M hyps ; ssimpl ; ind_align.
  1,2 : right ; full_destruct ; repeat eexists ; eauto ; by rewrite -[fun x => exists p, [set x' | ps2 p /\ x = x'] (FNot p)]/(GSPEC(
      fun x => exists p, [set x' | (fun p' ps2' => ps2' p' ) p ps2 /\ x = x'] (FNot p)))
    -IN_def SPEC_IMAGE ; eauto.
  1,2 : rewrite -[fun x => exists p, [set x' | x3 p /\ x = x'] (FNot p)]/(GSPEC(
      fun x => exists p, [set x' | (fun p' ps2' => ps2' p' ) p x3 /\ x = x'] (FNot p)))
    -IN_def SPEC_IMAGE in H8,H9 ; econstructor ; by eauto.
Qed.

Inductive semresproof2 {A : Type'} (M : Structure A) 
  (hyps : set (set form)) : set form -> Prop :=
  | semresproof2_assumption : forall cl, hyps cl -> semresproof2 M hyps cl
  | semresproof2_rm_opposable1 :
      forall cl1 cl2 cl2' ps1 ps2 subst,
      semresproof2 M hyps cl1 -> semresproof2 M hyps cl2 ->
      (~forall v, valuation M v -> holds M v (interp cl1)) ->
      formsubst (rename cl2 (FVS cl1)) @` cl2 = cl2' -> ps1 `<=` cl1 ->
      ps2 `<=` cl2' -> ps1 <> set0 -> ps2 <> set0 ->
      (exists subst', Unifies subst' (ps1 `|` FNot @` ps2)) ->
      mgu (ps1 `|` FNot @` ps2) = subst ->
      semresproof2 M hyps (formsubst subst @` (cl1 `\` ps1 `|` cl2' `\` ps2))
  | semresproof2_rm_opposable2 :
      forall cl1 cl2 cl2' ps1 ps2 subst,
      semresproof2 M hyps cl1 -> semresproof2 M hyps cl2 ->
      (~forall v, valuation M v -> holds M v (interp cl2)) ->
      formsubst (rename cl2 (FVS cl1)) @` cl2 = cl2' -> ps1 `<=` cl1 ->
      ps2 `<=` cl2' -> ps1 <> set0 -> ps2 <> set0 ->
      (exists subst', Unifies subst' (ps1 `|` FNot @` ps2)) ->
      mgu (ps1 `|` FNot @` ps2) = subst ->
      semresproof2 M hyps (formsubst subst @` (cl1 `\` ps1 `|` cl2' `\` ps2)).

Lemma semresproof2_def {A : Type'} : (@semresproof2 A) = (fun M : prod (A -> Prop) (prod (N -> (list A) -> A) (N -> (list A) -> Prop)) => fun hyps' : (form -> Prop) -> Prop => fun a : form -> Prop => forall semresproof2' : (form -> Prop) -> Prop, (forall a' : form -> Prop, ((@IN (form -> Prop) a' hyps') \/ (exists cl1 : form -> Prop, exists cl2 : form -> Prop, exists cl2' : form -> Prop, exists ps1 : form -> Prop, exists ps2 : form -> Prop, exists i : N -> term, (a' = (@IMAGE form form (formsubst i) (@setU form (@setD form cl1 ps1) (@setD form cl2' ps2)))) /\ ((semresproof2' cl1) /\ ((semresproof2' cl2) /\ (((~ (forall v : N -> A, (@valuation A M v) -> @holds A M v (interp cl1))) \/ (~ (forall v : N -> A, (@valuation A M v) -> @holds A M v (interp cl2)))) /\ (((@IMAGE form form (formsubst (rename cl2 (FVS cl1))) cl2) = cl2') /\ ((@subset form ps1 cl1) /\ ((@subset form ps2 cl2') /\ ((~ (ps1 = (@set0 form))) /\ ((~ (ps2 = (@set0 form))) /\ ((exists i' : N -> term, Unifies i' (@setU form ps1 (@GSPEC form (fun GEN_PVAR_636 : form => exists p : form, @SETSPEC form GEN_PVAR_636 (@IN form p ps2) (FNot p))))) /\ ((mgu (@setU form ps1 (@GSPEC form (fun GEN_PVAR_637 : form => exists p : form, @SETSPEC form GEN_PVAR_637 (@IN form p ps2) (FNot p))))) = i)))))))))))) -> semresproof2' a') -> semresproof2' a).
Proof.
  ext 2 => M hyps ; ssimpl ; ind_align.
  1,2 : right ; full_destruct ; repeat eexists ; eauto ; by rewrite -[fun x => exists p, [set x' | ps2 p /\ x = x'] (FNot p)]/(GSPEC(
      fun x => exists p, [set x' | (fun p' ps2' => ps2' p' ) p ps2 /\ x = x'] (FNot p)))
    -IN_def SPEC_IMAGE ; eauto.
  1,2 : rewrite -[fun x => exists p, [set x' | x3 p /\ x = x'] (FNot p)]/(GSPEC(
      fun x => exists p, [set x' | (fun p' ps2' => ps2' p' ) p x3 /\ x = x'] (FNot p)))
    -IN_def SPEC_IMAGE in H8,H9 ; econstructor ; by eauto.
Qed.

(*****************************************************************************)
(* Logic/givensem.ml *)
(*****************************************************************************)

Definition isaresolvent_sem (M : Structure N) cl (c : set form * set form) :=
  let (cl1,cl2) := c in isaresolvent cl c /\
  (~(forall v, holds M v (interp cl1)) \/ ~forall v, holds M v (interp cl2)).

Lemma isaresolvent_sem_def : isaresolvent_sem = (fun _533128 : prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop)) => fun _533129 : form -> Prop => fun _533130 : prod (form -> Prop) (form -> Prop) => (isaresolvent _533129 (@pair (form -> Prop) (form -> Prop) (@fst (form -> Prop) (form -> Prop) _533130) (@snd (form -> Prop) (form -> Prop) _533130))) /\ ((~ (forall v : N -> N, @holds N _533128 v (interp (@fst (form -> Prop) (form -> Prop) _533130)))) \/ (~ (forall v : N -> N, @holds N _533128 v (interp (@snd (form -> Prop) (form -> Prop) _533130)))))).
Proof. by funext=> + + []. Qed.

Definition allresolvents_sem M s s' :=
  fun cl => (exists c1 c2, s c1 /\ s' c2 /\ isaresolvent_sem M cl (c1, c2)).

Lemma allresolvents_sem_def : allresolvents_sem = (fun _533155 : prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop)) => fun _533156 : (form -> Prop) -> Prop => fun _533157 : (form -> Prop) -> Prop => @GSPEC (form -> Prop) (fun GEN_PVAR_648 : form -> Prop => exists c : form -> Prop, @SETSPEC (form -> Prop) GEN_PVAR_648 (exists c1 : form -> Prop, exists c2 : form -> Prop, (@IN (form -> Prop) c1 _533156) /\ ((@IN (form -> Prop) c2 _533157) /\ (isaresolvent_sem _533155 c (@pair (form -> Prop) (form -> Prop) c1 c2)))) c)).
Proof. by extall ; ssimpl. Qed.

Definition allntresolvents_sem M s s' cl :=
  allresolvents_sem M s s' cl /\ ~ tautologous cl.

Lemma allntresolvents_sem_def : allntresolvents_sem = (fun _533176 : prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop)) => fun _533177 : (form -> Prop) -> Prop => fun _533178 : (form -> Prop) -> Prop => @GSPEC (form -> Prop) (fun GEN_PVAR_649 : form -> Prop => exists r : form -> Prop, @SETSPEC (form -> Prop) GEN_PVAR_649 ((@IN (form -> Prop) r (allresolvents_sem _533176 _533177 _533178)) /\ (~ (tautologous r))) r)).
Proof. by extall ; ssimpl. Qed.

Definition resolvents_sem M cl (l : list (set form)) :=
  [list of allresolvents_sem M [set cl] [set` l]].

Lemma resolvents_sem_def : resolvents_sem = (fun _533232 : prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop)) => fun _533233 : form -> Prop => fun _533234 : list (form -> Prop) => @list_of_set (form -> Prop) (allresolvents_sem _533232 (@INSERT (form -> Prop) _533233 (@set0 (form -> Prop))) (@set_of_list (form -> Prop) _533234))).
Proof. by extall ; ssimpl. Qed.

Definition step_sem M c :=
  match c with
  | (_,nil) => c
  | (l,a::l') => (insert a l,
    fold_right (incorporate a) l' (resolvents_sem M a (a :: l))) end.

Lemma step_sem_def : step_sem = (fun _533275 : prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop)) => fun _533276 : prod (list (form -> Prop)) (list (form -> Prop)) => @COND (prod (list (form -> Prop)) (list (form -> Prop))) ((@snd (list (form -> Prop)) (list (form -> Prop)) _533276) = (@nil (form -> Prop))) (@pair (list (form -> Prop)) (list (form -> Prop)) (@fst (list (form -> Prop)) (list (form -> Prop)) _533276) (@snd (list (form -> Prop)) (list (form -> Prop)) _533276)) (@Basics.apply (list (form -> Prop)) (prod (list (form -> Prop)) (list (form -> Prop))) (fun new : list (form -> Prop) => @Datatypes.id (prod (list (form -> Prop)) (list (form -> Prop))) (@pair (list (form -> Prop)) (list (form -> Prop)) (@insert (form -> Prop) (@HOLLight.Real_With_N.mappings.hd (form -> Prop) (@snd (list (form -> Prop)) (list (form -> Prop)) _533276)) (@fst (list (form -> Prop)) (list (form -> Prop)) _533276)) (@fold_right_with_perm_args (form -> Prop) (list (form -> Prop)) (incorporate (@HOLLight.Real_With_N.mappings.hd (form -> Prop) (@snd (list (form -> Prop)) (list (form -> Prop)) _533276))) new (@HOLLight.Real_With_N.mappings.tl (form -> Prop) (@snd (list (form -> Prop)) (list (form -> Prop)) _533276))))) (resolvents_sem _533275 (@HOLLight.Real_With_N.mappings.hd (form -> Prop) (@snd (list (form -> Prop)) (list (form -> Prop)) _533276)) (@cons (form -> Prop) (@HOLLight.Real_With_N.mappings.hd (form -> Prop) (@snd (list (form -> Prop)) (list (form -> Prop)) _533276)) (@fst (list (form -> Prop)) (list (form -> Prop)) _533276))))).
Proof.
  by funext => ? [? l] ; if_list ; case l.
Qed.

Fixpoint given_sem M n p :=
  match n with
  | O => p
  | S n => step_sem M (given_sem M n p) end.

Definition giveN_sem M n := given_sem M (N.to_nat n).

Lemma given_sem_def : giveN_sem = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) -> (prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop))) -> N -> (prod (list (form -> Prop)) (list (form -> Prop))) -> prod (list (form -> Prop)) (list (form -> Prop))) (fun given_sem' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) -> (prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop))) -> N -> (prod (list (form -> Prop)) (list (form -> Prop))) -> prod (list (form -> Prop)) (list (form -> Prop)) => forall _533299 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))), (forall M : prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop)), forall p : prod (list (form -> Prop)) (list (form -> Prop)), (given_sem' _533299 M (NUMERAL N0) p) = p) /\ (forall M : prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop)), forall n : N, forall p : prod (list (form -> Prop)) (list (form -> Prop)), (given_sem' _533299 M (N.succ n) p) = (step_sem M (given_sem' _533299 M n p)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0))))))))))))))))).
Proof.
  by N_rec_align ; rewrite/giveN_sem Nnat.N2Nat.inj_succ.
Qed.

Definition Used_SEM M init n := let (l,_) := giveN_sem M n init in [set` l].
Definition Unused_SEM M init n := let (_,l) := giveN_sem M n init in [set` l].

Lemma Used_SEM_def : Used_SEM = (fun _533300 : prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop)) => fun _533301 : prod (list (form -> Prop)) (list (form -> Prop)) => fun _533302 : N => @set_of_list (form -> Prop) (@fst (list (form -> Prop)) (list (form -> Prop)) (giveN_sem _533300 _533302 _533301))).
Proof.
  by funext => M init n ; rewrite/Used_SEM ;case (giveN_sem M n init).
Qed.

Lemma Unused_SEM_def : Unused_SEM = (fun _533321 : prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop)) => fun _533322 : prod (list (form -> Prop)) (list (form -> Prop)) => fun _533323 : N => @set_of_list (form -> Prop) (@snd (list (form -> Prop)) (list (form -> Prop)) (giveN_sem _533321 _533323 _533322))).
Proof.
  by funext => M init n ; rewrite/Unused_SEM ;case (giveN_sem M n init).
Qed.

Fixpoint Subnat_SEM M init n := 
  match n with
  | O => set0
  | S n => match given_sem M n init with
    | (_,nil) => Subnat_SEM M init n
    | (_,a::_) => INSERT a (Subnat_SEM M init n) end end.

Definition Sub_SEM M init n : (form -> Prop) -> Prop := Subnat_SEM M init (N.to_nat n).

Lemma Sub_SEM_def : Sub_SEM = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop))) -> (prod (list (form -> Prop)) (list (form -> Prop))) -> N -> (form -> Prop) -> Prop) (fun Sub_SEM' : (prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop))) -> (prod (list (form -> Prop)) (list (form -> Prop))) -> N -> (form -> Prop) -> Prop => forall _533349 : prod N (prod N (prod N (prod N (prod N (prod N N))))), (forall M : prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop)), forall init : prod (list (form -> Prop)) (list (form -> Prop)), (Sub_SEM' _533349 M init (NUMERAL N0)) = (@set0 (form -> Prop))) /\ (forall M : prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop)), forall init : prod (list (form -> Prop)) (list (form -> Prop)), forall n : N, (Sub_SEM' _533349 M init (N.succ n)) = (@COND ((form -> Prop) -> Prop) ((@snd (list (form -> Prop)) (list (form -> Prop)) (giveN_sem M n init)) = (@nil (form -> Prop))) (Sub_SEM' _533349 M init n) (@INSERT (form -> Prop) (@HOLLight.Real_With_N.mappings.hd (form -> Prop) (@snd (list (form -> Prop)) (list (form -> Prop)) (giveN_sem M n init))) (Sub_SEM' _533349 M init n))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0))))))))))))))).
Proof.
  N_rec_align. if_list. rewrite/Sub_SEM Nnat.N2Nat.inj_succ /giveN_sem /=.
  by case (given_sem M (N.to_nat n)) => /= _ [].
Qed.

Fixpoint breaknat_sem M init n :=
  match n with
  | O => lengthN (snd init)
  | S n => let k := breaknat_sem M init n in
           k + lengthN (snd (giveN_sem M k init)) end.

Definition break_sem M init n := breaknat_sem M init (N.to_nat n).

Lemma break_sem_def : break_sem = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) -> (prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop))) -> (prod (list (form -> Prop)) (list (form -> Prop))) -> N -> N) (fun break_sem' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) -> (prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop))) -> (prod (list (form -> Prop)) (list (form -> Prop))) -> N -> N => forall _544384 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))), (forall M : prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop)), forall init : prod (list (form -> Prop)) (list (form -> Prop)), (break_sem' _544384 M init (NUMERAL N0)) = (@lengthN (form -> Prop) (@snd (list (form -> Prop)) (list (form -> Prop)) (giveN_sem M (NUMERAL N0) init)))) /\ (forall M : prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop)), forall n : N, forall init : prod (list (form -> Prop)) (list (form -> Prop)), (break_sem' _544384 M init (N.succ n)) = (N.add (break_sem' _544384 M init n) (@lengthN (form -> Prop) (@snd (list (form -> Prop)) (list (form -> Prop)) (giveN_sem M (break_sem' _544384 M init n) init)))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0))))))))))))))))).
Proof.
  by N_rec_align ; rewrite/break_sem Nnat.N2Nat.inj_succ.
Qed.

Definition level_sem M init n := Sub_SEM M init (break_sem M init n).

Lemma level_sem_def : level_sem = (fun _544385 : prod (N -> Prop) (prod (N -> (list N) -> N) (N -> (list N) -> Prop)) => fun _544386 : prod (list (form -> Prop)) (list (form -> Prop)) => fun _544387 : N => Sub_SEM _544385 _544386 (break_sem _544385 _544386 _544387)).
Proof erefl.

(*****************************************************************************)
(* Logic/prolog.ml *)
(*****************************************************************************)

Definition definite cl := clause cl /\ #|` fset_set (cl `&` positive) | = 1%nat.

Lemma definite_def : definite = (fun _545149 : form -> Prop => (clause _545149) /\ ((@card form (@GSPEC form (fun GEN_PVAR_652 : form => exists p : form, @SETSPEC form GEN_PVAR_652 ((@IN form p _545149) /\ (positive p)) p))) = (NUMERAL (BIT1 N0)))).
Proof.
  rewrite/definite/clause/card INTER_def.
  ext => cl [[fincl +] +] ; rewrite if_triv_True ; ssimpl ; first by move=> + ->.
  1,3 : by apply finite_setIl.
  by repeat split ; auto ; apply Nnat.Nat2N.inj.
Qed.

Definition horn cl := clause cl /\ (#|` fset_set (cl `&` positive) | <= 1)%nat.

Lemma horn_def : horn = (fun _545154 : form -> Prop => (clause _545154) /\ (N.le (@card form (@GSPEC form (fun GEN_PVAR_653 : form => exists p : form, @SETSPEC form GEN_PVAR_653 ((@IN form p _545154) /\ (positive p)) p))) (NUMERAL (BIT1 N0)))).
Proof.
  rewrite/horn/clause/card INTER_def.
  ext => cl [[fincl +] +] ; rewrite if_triv_True ; ssimpl.
  2,4 : by apply finite_setIl.
  1,2 : repeat split ; auto.
  - by rewrite -to_nat_inj_le Nnat.Nat2N.id ; apply/leP.
  - rewrite -[X in (X <= _)%nat]Nnat.Nat2N.id -[1%nat]/(N.to_nat 1).
    by apply/leP ; rewrite to_nat_inj_le.
Qed.

Definition falsify f cl := if definite cl then cl else f |` cl.

Lemma falsify_def : falsify = (fun _545159 : form => fun _545160 : form -> Prop => @COND (form -> Prop) (definite _545160) _545160 (@INSERT form _545159 _545160)).
Proof erefl.

Definition minmodel E := (herbase (functions E),
  (Fn,
  fun n l => forall M, Dom M = herbase (functions E) /\ 
    Fun M = Fn /\ satisfies M E -> Pred M n l)).

Lemma minmodel_def : minmodel = (fun _546187 : form -> Prop => @pair (term -> Prop) (prod (N -> (list term) -> term) (N -> (list term) -> Prop)) (herbase (functions _546187)) (@pair (N -> (list term) -> term) (N -> (list term) -> Prop) Fn (fun p : N => fun zs : list term => forall H : prod (term -> Prop) (prod (N -> (list term) -> term) (N -> (list term) -> Prop)), (((@Dom term H) = (herbase (functions _546187))) /\ (((@Fun term H) = Fn) /\ (@satisfies term H _546187))) -> @Pred term H p zs))).
Proof erefl.

Definition breakhorn cl := if definite cl
  then let p := ε (fun p : form => cl p /\ positive p) in
    (map FNot [list of cl `\  p], p)
  else (map FNot (list_of_set cl), FFalse).

Lemma breakhorn_def : breakhorn = (fun _546245 : form -> Prop => @COND (prod (list form) form) (definite _546245) (@LET form (prod (list form) form) (fun p : form => @LET_END (prod (list form) form) (@pair (list form) form (@List.map form form FNot (@list_of_set form (@DELETE form _546245 p))) p)) (@ε form (fun p : form => (@IN form p _546245) /\ (positive p)))) (@pair (list form) form (@List.map form form FNot (@list_of_set form _546245)) FFalse)).
Proof. by ssimpl. Qed.

Definition hypotheses cl := fst (breakhorn cl).
Definition conclusion cl := snd (breakhorn cl).

Lemma hypotheses_def : hypotheses = (fun _546250 : form -> Prop => @fst (list form) form (breakhorn _546250)).
Proof erefl.
Lemma conclusion_def : conclusion = (fun _546250 : form -> Prop => @snd (list form) form (breakhorn _546250)).
Proof erefl.

Unset Elimination Schemes.
Inductive gbackchain s : N -> form -> Prop :=
| gbackchain0 : forall cl v l, s cl ->
  (forall n, herbase (functions (interp @` s)) (v n)) ->
  Forall2 (gbackchain s) l (map (formsubst v) (hypotheses cl)) ->
  gbackchain s (fold_right N.add 1 l) (formsubst v (conclusion cl)).

Fixpoint gbackchain_ind (s : set (set form))
  (P : N -> form -> Prop)
  (H : forall cl v l, s cl ->
    (forall n : N, herbase (functions (interp @` s)) (v n)) ->
    Forall2 P l (map (formsubst v) (hypotheses cl)) ->
    P (fold_right N.add 1 l) (formsubst v (conclusion cl)))
  (n : N) (f : form) (H0 : gbackchain s n f) : P n f :=
  match H0 in gbackchain _ n1 f1 return P n1 f1
  with gbackchain0 cl v l H1 H2 H3 => H cl v l H1 H2
    (Forall2_ind (Forall2 P)
      (Forall2_nil _) (fun n0 f0 l0 l0' H4 H5 H6 =>
        Forall2_cons _ _ (gbackchain_ind s P H n0 f0 H4) H6) H3) end.

Register Scheme gbackchain_ind as ind_nodep for gbackchain.

Lemma gbackchain_def : gbackchain = (fun s : (form -> Prop) -> Prop => fun a0 : N => fun a1 : form => forall gbackchain' : N -> form -> Prop, (forall a0' : N, forall a1' : form, (exists cl : form -> Prop, exists i : N -> term, exists ns : list N, (a0' = (@fold_right_with_perm_args N N N.add ns (NUMERAL (BIT1 N0)))) /\ ((a1' = (formsubst i (conclusion cl))) /\ ((@IN (form -> Prop) cl s) /\ ((forall x : N, @IN term (i x) (herbase (functions (@IMAGE (form -> Prop) form interp s)))) /\ (@List.Forall2 N form gbackchain' ns (@List.map form form (formsubst i) (hypotheses cl))))))) -> gbackchain' a0' a1') -> gbackchain' a0 a1).
Proof. ssimpl ; ind_align. Qed.

Definition iminmodel E :=
  (terms (functions E),
   (Fn,
     fun n l => forall M, Dom M = terms (functions E) /\ Fun M = Fn /\ 
     (forall v f, IN f E /\ valuation M v -> holds M v f) ->
     Pred M n l)).

Lemma iminmodel_def : iminmodel = (fun _549309 : form -> Prop => @pair (term -> Prop) (prod (N -> (list term) -> term) (N -> (list term) -> Prop)) (terms (functions _549309)) (@pair (N -> (list term) -> term) (N -> (list term) -> Prop) Fn (fun p : N => fun zs : list term => forall C : prod (term -> Prop) (prod (N -> (list term) -> term) (N -> (list term) -> Prop)), (((@Dom term C) = (terms (functions _549309))) /\ (((@Fun term C) = Fn) /\ (forall v : N -> term, forall p' : form, ((@IN form p' _549309) /\ (@valuation term C v)) -> @holds term C v p')) -> @Pred term C p zs)))).
Proof erefl.

Inductive ibackchain s : N -> form -> Prop :=
| ibackchain0 : forall cl v l, s cl ->
  (forall n, terms (functions (interp @` s)) (v n)) ->
  Forall2 (ibackchain s) l (map (formsubst v) (hypotheses cl)) ->
  ibackchain s (fold_right N.add 1 l) (formsubst v (conclusion cl)).

Fixpoint ibackchain_ind (s : set (set form))
  (P : N -> form -> Prop)
  (H : forall cl v l, s cl ->
    (forall n : N, terms (functions (interp @` s)) (v n)) ->
    Forall2 P l (map (formsubst v) (hypotheses cl)) ->
    P (fold_right N.add 1 l) (formsubst v (conclusion cl)))
  (n : N) (f : form) (H0 : ibackchain s n f) : P n f :=
  match H0 in ibackchain _ n1 f1 return P n1 f1
  with ibackchain0 cl v l H1 H2 H3 => H cl v l H1 H2
    (Forall2_ind (Forall2 P)
      (Forall2_nil _) (fun n0 f0 l0 l0' H4 H5 H6 =>
        Forall2_cons _ _ (ibackchain_ind s P H n0 f0 H4) H6) H3) end.

Register Scheme ibackchain_ind as ind_nodep for ibackchain.

Lemma ibackchain_def : ibackchain = (fun s : (form -> Prop) -> Prop => fun a0 : N => fun a1 : form => forall ibackchain' : N -> form -> Prop, (forall a0' : N, forall a1' : form, (exists cl : form -> Prop, exists i : N -> term, exists ns : list N, (a0' = (@fold_right_with_perm_args N N N.add ns (NUMERAL (BIT1 N0)))) /\ ((a1' = (formsubst i (conclusion cl))) /\ ((@IN (form -> Prop) cl s) /\ ((forall x : N, @IN term (i x) (terms (functions (@IMAGE (form -> Prop) form interp s)))) /\ (@List.Forall2 N form ibackchain' ns (@List.map form form (formsubst i) (hypotheses cl))))))) -> ibackchain' a0' a1') -> ibackchain' a0 a1).
Proof. ssimpl ; ind_align. Qed.

(*****************************************************************************)
(* Logic/Birkhoff.ml *)
(*****************************************************************************)


Inductive provable (s : set form) : form -> Prop :=
| pr_assume : forall t t', s (FEq t t') -> provable s (FEq t t')
| pr_FEq_refl : forall t, provable s (FEq t t)
| pr_FEq_sym : forall t t', provable s (FEq t t') -> provable s (FEq t' t)
| pr_FEq_trans : forall t t' t'', provable s (FEq t t') -> provable s (FEq t' t'') ->
                 provable s (FEq t t'')
| pr_FEq_fun_compat : forall n l l', Forall2 (fun t t' => provable s (FEq t t')) l l' ->
               provable s (FEq (Fn n l) (Fn n l'))
| pr_formsubst : forall t t' v, provable s (FEq t t') -> provable s (formsubst v (FEq t t')).

Scheme provable_ind0 := Minimality for provable Sort Prop.

Fixpoint provable_ind (s : set form) (P : form -> Prop)
  H0 H1 H2 H3
  (H4 : forall n l l', Forall2 (fun t t' => P (FEq t t')) l l' ->
               P (FEq (Fn n l) (Fn n l')))
  H5 (f : form) (H6 : provable s f) : P f :=
  provable_ind0 s P H0 H1 H2 H3 
    (fun n l l' H' => H4 n l l' (Forall2_ind (Forall2 (fun t t' => P (FEq t t')))
      (Forall2_nil _) (fun f0 f'0 l0 l'0 H00 H10 H20 => Forall2_cons _ _
        (provable_ind s P H0 H1 H2 H3 H4 H5 _ H00) H20) H')) H5 f H6.

Register Scheme provable_ind as ind_nodep for provable.

Lemma vdash_def : provable = (fun E : form -> Prop => fun a : form => forall vdash' : form -> Prop, (forall a' : form, ((exists s : term, exists t : term, (a' = (FEq s t)) /\ (@IN form (FEq s t) E)) \/ ((exists t : term, a' = (FEq t t)) \/ ((exists s : term, exists t : term, (a' = (FEq t s)) /\ (vdash' (FEq s t))) \/ ((exists s : term, exists t : term, exists u : term, (a' = (FEq s u)) /\ ((vdash' (FEq s t)) /\ (vdash' (FEq t u)))) \/ ((exists f : N, exists a'' : list term, exists b : list term, (a' = (FEq (Fn f a'') (Fn f b))) /\ (@List.Forall2 term term (fun l : term => fun r : term => vdash' (FEq l r)) a'' b)) \/ (exists s : term, exists t : term, exists i : N -> term, (a' = (formsubst i (FEq s t))) /\ (vdash' (FEq s t)))))))) -> vdash' a') -> vdash' a).
Proof. ssimpl ; ind_align. Qed.

Inductive wcprovable (s : set form) : form -> Prop :=
| wcpr_assume : forall t t' v, s (FEq t t') -> wcprovable s (formsubst v (FEq t t'))
| wcpr_FEq_refl : forall t, wcprovable s (FEq t t)
| wcpr_FEq_sym : forall t t' v, s (FEq t t') -> wcprovable s (formsubst v (FEq t' t))
| wcpr_FEq_trans : forall t t' t'', wcprovable s (FEq t t') -> wcprovable s (FEq t' t'') ->
                 wcprovable s (FEq t t'')
| wcpr_FEq_fun_compat : forall n l l', Forall2 (fun t t' => wcprovable s (FEq t t')) l l' ->
               wcprovable s (FEq (Fn n l) (Fn n l')).

Scheme wcprovable_ind0 := Minimality for wcprovable Sort Prop.

Fixpoint wcprovable_ind (s : set form) (P : form -> Prop)
  H0 H1 H2 H3
  (H4 : forall n l l', Forall2 (fun t t' => P (FEq t t')) l l' ->
               P (FEq (Fn n l) (Fn n l')))
  (f : form) (H5 : wcprovable s f) : P f :=
  wcprovable_ind0 s P H0 H1 H2 H3
    (fun n l l' H' => H4 n l l' (Forall2_ind (Forall2 (fun t t' => P (FEq t t')))
      (Forall2_nil _) (fun f0 f'0 l0 l'0 H00 H10 H20 => Forall2_cons _ _
        (wcprovable_ind s P H0 H1 H2 H3 H4 _ H00) H20) H')) f H5.

Register Scheme wcprovable_ind as ind_nodep for wcprovable.

Lemma vdash2_def : wcprovable = (fun E : form -> Prop => fun a : form => forall vdash2' : form -> Prop, (forall a' : form, ((exists s : term, exists t : term, exists i : N -> term, (a' = (formsubst i (FEq s t))) /\ (@IN form (FEq s t) E)) \/ ((exists s : term, exists t : term, exists i : N -> term, (a' = (formsubst i (FEq t s))) /\ (@IN form (FEq s t) E)) \/ ((exists t : term, a' = (FEq t t)) \/ ((exists s : term, exists t : term, exists u : term, (a' = (FEq s u)) /\ ((vdash2' (FEq s t)) /\ (vdash2' (FEq t u)))) \/ (exists f : N, exists a'' : list term, exists b : list term, (a' = (FEq (Fn f a'') (Fn f b))) /\ (@List.Forall2 term term (fun l : term => fun r : term => vdash2' (FEq l r)) a'' b)))))) -> vdash2' a') -> vdash2' a).
Proof. ssimpl ; ind_align. Qed.

Set Elimination Schemes.
Inductive aprovable (s : set form) : form -> Prop :=
| apr_assume : forall t t' v, s (FEq t t') -> aprovable s (formsubst v (FEq t t'))
| apr_FEq_sym : forall t t' v, s (FEq t t')  -> aprovable s (formsubst v (FEq t' t)).

Lemma vdash2_axiom_def : aprovable = (fun E : form -> Prop => fun a : form => forall vdash2_axiom' : form -> Prop, (forall a' : form, ((exists s : term, exists t : term, exists i : N -> term, (a' = (formsubst i (FEq s t))) /\ (@IN form (FEq s t) E)) \/ (exists s : term, exists t : term, exists i : N -> term, (a' = (formsubst i (FEq t s))) /\ (@IN form (FEq s t) E))) -> vdash2_axiom' a') -> vdash2_axiom' a).
Proof. ssimpl ; ind_align. Qed.

Unset Elimination Schemes.
Inductive cprovable s : form -> Prop :=
| cpr_FEq_refl : forall t, cprovable s (FEq t t)
| cpr_prac : forall t t', provable_achain s (FEq t t') -> cprovable s (FEq t t')
| cpr_prcc : forall t t', provable_cchain s (FEq t t') -> cprovable s (FEq t t')
with provable_achain s : form -> Prop :=
| prac_apr : forall t t', aprovable s (FEq t t') -> provable_achain s (FEq t t')
| prac_trans : forall t t' t'', aprovable s (FEq t t') -> cprovable s (FEq t' t'') ->
               provable_achain s (FEq t t'')
with provable_cchain s : form -> Prop :=
| prcc_prc : forall t t', provable_cong s (FEq t t') -> provable_cchain s (FEq t t')
| prcc_trans : forall t t' t'', provable_cong s (FEq t t') -> provable_achain s (FEq t' t'') ->
               provable_cchain s (FEq t t'')
with provable_cong s : form -> Prop :=
| prc_fun_compat : forall n l l', Forall2 (fun t t' => cprovable s (FEq t t')) l l' ->
                   provable_cong s (FEq (Fn n l) (Fn n l')).
Set Elimination Schemes.

Section cprovable_ind.

Variables 
  (s : set form)
  (P P0 P1 P2 : form -> Prop)
  (H0 : forall t, P (FEq t t))
  (H1 : forall t t', provable_achain s (FEq t t') -> P0 (FEq t t') -> P (FEq t t'))
  (H2 : forall t t', provable_cchain s (FEq t t') -> P1 (FEq t t') -> P (FEq t t'))
  (H3 : forall t t', aprovable s (FEq t t') -> P0 (FEq t t'))
  (H4 : forall t t' t'', aprovable s (FEq t t') -> cprovable s (FEq t' t'') ->
    P (FEq t' t'') -> P0 (FEq t t''))
  (H5 : forall t t', provable_cong s (FEq t t') -> P2 (FEq t t') -> P1 (FEq t t'))
  (H6 : forall t t' t'', provable_cong s (FEq t t') -> P2 (FEq t t') ->
    provable_achain s (FEq t' t'') -> P0 (FEq t' t'') -> P1 (FEq t t''))
  (H7 : forall n l l', Forall2 (fun t t' : term => P (FEq t t')) l l' -> P2 (FEq (Fn n l) (Fn n l'))).

Fixpoint cprovable_ind f (H' : cprovable s f) : P f :=
  match H' in cprovable _ f return P f with
  | cpr_FEq_refl t => H0 t
  | cpr_prac t t' Hac => H1 t t' Hac (provable_achain_ind (FEq t t') Hac)
  | cpr_prcc t t' Hcc => H2 t t' Hcc (provable_cchain_ind (FEq t t') Hcc) end
with provable_achain_ind f (Hac : provable_achain s f ): P0 f :=
  match Hac in provable_achain _ f return P0 f with
  | prac_apr t t' Ha => H3 t t' Ha
  | prac_trans t t' t'' Ha H' => H4 t t' t'' Ha H' (cprovable_ind (FEq t' t'') H') end
with provable_cchain_ind f (Hcc : provable_cchain s f) : P1 f :=
  match Hcc in provable_cchain _ f return P1 f with
  | prcc_prc t t' Hc => H5 t t' Hc (provable_cong_ind (FEq t t') Hc)
  | prcc_trans t t' t'' Hc Hac => H6 t t' t'' Hc (provable_cong_ind (FEq t t') Hc)
    Hac (provable_achain_ind (FEq t' t'') Hac) end
with provable_cong_ind f (Hc : provable_cong _ f) : P2 f :=
  match Hc in provable_cong _ f return P2 f with
  | prc_fun_compat n l l' HF2' => H7 n l l'
    (Forall2_ind (Forall2 (fun t t' => P (FEq t t')))
      (Forall2_nil _) (fun f0 f'0 l0 l'0 H00 H10 H20 => Forall2_cons _ _
        (cprovable_ind _ H00) H20) HF2') end.

End cprovable_ind.

Register Scheme cprovable_ind as ind_nodep for cprovable.
Register Scheme provable_achain_ind as ind_nodep for provable_achain.
Register Scheme provable_cchain_ind as ind_nodep for provable_cchain.
Register Scheme provable_cong_ind as ind_nodep for provable_cong.

Ltac provable_align induction_principle :=
  let s := fresh in
  let H := fresh in
  let Pac := fresh in
  let Pcc := fresh in
  let Pc := fresh in
  let P := fresh in
  let H' := fresh in
  funext => s ? ; apply prop_ext ; intro H ;
  [ intros Pac Pcc Pc P H' ; apply (induction_principle s P Pac Pcc Pc) ; auto ;
    clear H ; intros ; apply H' ; breakgoal
  | apply (H (provable_achain s) (provable_cchain s) (provable_cong s) (cprovable s)) ;
    clearall ; repeat split ; intros f H ; full_destruct ;
    blindrewrite ; (try now constructor) ;
    match goal with t:term , t':term |- _ => (try now apply (prac_trans s t t')) ;
    now apply (prcc_trans s t t') end
  ].

Lemma vdash3_def : cprovable = (fun E : form -> Prop => fun a3 : form => forall vdash2_achain' : form -> Prop, forall vdash2_cchain' : form -> Prop, forall vdash2_cong' : form -> Prop, forall vdash3' : form -> Prop, ((forall a0 : form, ((exists s : term, exists t : term, (a0 = (FEq s t)) /\ (aprovable E (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a0 = (FEq s u)) /\ ((aprovable E (FEq s t)) /\ (vdash3' (FEq t u))))) -> vdash2_achain' a0) /\ ((forall a1 : form, ((exists s : term, exists t : term, (a1 = (FEq s t)) /\ (vdash2_cong' (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a1 = (FEq s u)) /\ ((vdash2_cong' (FEq s t)) /\ (vdash2_achain' (FEq t u))))) -> vdash2_cchain' a1) /\ ((forall a2 : form, (exists f : N, exists a : list term, exists b : list term, (a2 = (FEq (Fn f a) (Fn f b))) /\ (@List.Forall2 term term (fun l : term => fun r : term => vdash3' (FEq l r)) a b)) -> vdash2_cong' a2) /\ (forall a3' : form, (exists s : term, exists t : term, (a3' = (FEq s t)) /\ ((s = t) \/ ((vdash2_achain' (FEq s t)) \/ (vdash2_cchain' (FEq s t))))) -> vdash3' a3')))) -> vdash3' a3).
Proof. provable_align cprovable_ind. Qed.

Lemma vdash2_achain_def : provable_achain = (fun E : form -> Prop => fun a0 : form => forall vdash2_achain' : form -> Prop, forall vdash2_cchain' : form -> Prop, forall vdash2_cong' : form -> Prop, forall vdash3' : form -> Prop, ((forall a0' : form, ((exists s : term, exists t : term, (a0' = (FEq s t)) /\ (aprovable E (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a0' = (FEq s u)) /\ ((aprovable E (FEq s t)) /\ (vdash3' (FEq t u))))) -> vdash2_achain' a0') /\ ((forall a1 : form, ((exists s : term, exists t : term, (a1 = (FEq s t)) /\ (vdash2_cong' (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a1 = (FEq s u)) /\ ((vdash2_cong' (FEq s t)) /\ (vdash2_achain' (FEq t u))))) -> vdash2_cchain' a1) /\ ((forall a2 : form, (exists f : N, exists a : list term, exists b : list term, (a2 = (FEq (Fn f a) (Fn f b))) /\ (@List.Forall2 term term (fun l : term => fun r : term => vdash3' (FEq l r)) a b)) -> vdash2_cong' a2) /\ (forall a3 : form, (exists s : term, exists t : term, (a3 = (FEq s t)) /\ ((s = t) \/ ((vdash2_achain' (FEq s t)) \/ (vdash2_cchain' (FEq s t))))) -> vdash3' a3)))) -> vdash2_achain' a0).
Proof. provable_align provable_achain_ind. Qed.

Lemma vdash2_cchain_def : provable_cchain = (fun E : form -> Prop => fun a1 : form => forall vdash2_achain' : form -> Prop, forall vdash2_cchain' : form -> Prop, forall vdash2_cong' : form -> Prop, forall vdash3' : form -> Prop, ((forall a0 : form, ((exists s : term, exists t : term, (a0 = (FEq s t)) /\ (aprovable E (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a0 = (FEq s u)) /\ ((aprovable E (FEq s t)) /\ (vdash3' (FEq t u))))) -> vdash2_achain' a0) /\ ((forall a1' : form, ((exists s : term, exists t : term, (a1' = (FEq s t)) /\ (vdash2_cong' (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a1' = (FEq s u)) /\ ((vdash2_cong' (FEq s t)) /\ (vdash2_achain' (FEq t u))))) -> vdash2_cchain' a1') /\ ((forall a2 : form, (exists f : N, exists a : list term, exists b : list term, (a2 = (FEq (Fn f a) (Fn f b))) /\ (@List.Forall2 term term (fun l : term => fun r : term => vdash3' (FEq l r)) a b)) -> vdash2_cong' a2) /\ (forall a3 : form, (exists s : term, exists t : term, (a3 = (FEq s t)) /\ ((s = t) \/ ((vdash2_achain' (FEq s t)) \/ (vdash2_cchain' (FEq s t))))) -> vdash3' a3)))) -> vdash2_cchain' a1).
Proof. provable_align provable_cchain_ind. Qed.

Lemma vdash2_cong_def : provable_cong = (fun E : form -> Prop => fun a2 : form => forall vdash2_achain' : form -> Prop, forall vdash2_cchain' : form -> Prop, forall vdash2_cong' : form -> Prop, forall vdash3' : form -> Prop, ((forall a0 : form, ((exists s : term, exists t : term, (a0 = (FEq s t)) /\ (aprovable E (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a0 = (FEq s u)) /\ ((aprovable E (FEq s t)) /\ (vdash3' (FEq t u))))) -> vdash2_achain' a0) /\ ((forall a1 : form, ((exists s : term, exists t : term, (a1 = (FEq s t)) /\ (vdash2_cong' (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a1 = (FEq s u)) /\ ((vdash2_cong' (FEq s t)) /\ (vdash2_achain' (FEq t u))))) -> vdash2_cchain' a1) /\ ((forall a2' : form, (exists f : N, exists a : list term, exists b : list term, (a2' = (FEq (Fn f a) (Fn f b))) /\ (@List.Forall2 term term (fun l : term => fun r : term => vdash3' (FEq l r)) a b)) -> vdash2_cong' a2') /\ (forall a3 : form, (exists s : term, exists t : term, (a3 = (FEq s t)) /\ ((s = t) \/ ((vdash2_achain' (FEq s t)) \/ (vdash2_cchain' (FEq s t))))) -> vdash3' a3)))) -> vdash2_cong' a2).
Proof. provable_align provable_cong_ind. Qed.

Fixpoint subterms t : term -> Prop :=
  match t with
  | V _ => [set t]
  | Fn _ l => t |` (list_Union (map subterms l)) end.

Lemma subterms_def : subterms = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> term -> term -> Prop) (fun subterms' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> term -> term -> Prop => forall _553739 : prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))), (forall x : N, (subterms' _553739 (V x)) = (@INSERT term (V x) (@set0 term))) /\ (forall f : N, forall args : list term, (subterms' _553739 (Fn f args)) = (@INSERT term (Fn f args) (@list_Union term (@List.map term (term -> Prop) (subterms' _553739) args))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))))))))))).
Proof.
  by term_align ; ssimpl.
Qed.

Inductive notatom : form -> Prop :=
| notatom_FFalse : notatom FFalse
| notatom_FImp : forall f f', notatom (FImp f f')
| notatom_FAll : forall n f, notatom (FAll n f).

Definition SUBTERMSA : form -> term -> Prop := @ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) -> form -> term -> Prop) (fun subtermsa' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) -> form -> term -> Prop => forall _553741 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))), forall P : N, forall args : list term, (subtermsa' _553741 (Atom P args)) = (@list_Union term (@List.map term (term -> Prop) subterms args))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))))))))))).

Definition subtermsa f : term -> Prop :=
  match f with Atom _ l => list_Union (map subterms l) | _ => SUBTERMSA f end.

Lemma subtermsa_def : subtermsa = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) -> form -> term -> Prop) (fun subtermsa' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) -> form -> term -> Prop => forall _553741 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))), forall P : N, forall args : list term, (subtermsa' _553741 (Atom P args)) = (@list_Union term (@List.map term (term -> Prop) subterms args))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0))))))))))))))))).
Proof. partial_align notatom. Qed.

Definition subtermss s := UNIONS (subtermsa @` s).

Lemma subtermss_def : subtermss = (fun _553742 : form -> Prop => @UNIONS term (@GSPEC (term -> Prop) (fun GEN_PVAR_664 : term -> Prop => exists p : form, @SETSPEC (term -> Prop) GEN_PVAR_664 (@IN form p _553742) (subtermsa p)))).
Proof. by extall ; ssimpl. Qed.

Definition esubterms s t t' := subtermss (FEq t t' |` [set f | exists v, (formsubst v @` s) f]).

Lemma esubterms_def : esubterms = (fun _553747 : form -> Prop => fun _553748 : term => fun _553749 : term => subtermss (@INSERT form (FEq _553748 _553749) (@GSPEC form (fun GEN_PVAR_665 : form => exists i : N -> term, exists p : form, @SETSPEC form GEN_PVAR_665 (@IN form p _553747) (formsubst i p))))).
Proof.
  extall ; ssimpl ; rewrite/esubterms.
  by repeat f_equal ; ext => [? /= [? []] | ? /= [? [? []]]] ; eauto.
Qed.

Unset Elimination Schemes.
Inductive scprovable E : form -> Prop :=
| scpr_FEq_refl : forall t, scprovable E (FEq t t)
| scpr_prsac : forall t t', provable_sachain E (FEq t t') -> scprovable E (FEq t t')
| scpr_prscc : forall t t', provable_scchain E (FEq t t') -> scprovable E (FEq t t')
with provable_sachain E : form -> Prop :=
| prsac_apr : forall t t', aprovable E (FEq t t') -> provable_sachain E (FEq t t')
| prsac_trans : forall t t' t'', aprovable E (FEq t t') -> scprovable E (FEq t' t'') ->
                esubterms E t t'' t' -> provable_sachain E (FEq t t'')
with provable_scchain E : form -> Prop :=
| prscc_prsc : forall t t', provable_scong E (FEq t t') -> provable_scchain E (FEq t t')
| prscc_trans : forall t t' t'', provable_scong E (FEq t t') -> provable_sachain E (FEq t' t'') ->
                esubterms E t t'' t' -> provable_scchain E (FEq t t'')
with provable_scong E : form -> Prop :=
| prsc_fun_compat : forall n l l', Forall2 (fun t t' => scprovable E (FEq t t')) l l' ->
                   provable_scong E (FEq (Fn n l) (Fn n l')).
Set Elimination Schemes.

Section scprovable_ind.

Variables 
  (E : set form)
  (P P0 P1 P2 : form -> Prop)
  (H0 : forall t, P (FEq t t))
  (H1 : forall t t', provable_sachain E (FEq t t') -> P0 (FEq t t') -> P (FEq t t'))
  (H2 : forall t t', provable_scchain E (FEq t t') -> P1 (FEq t t') -> P (FEq t t'))
  (H3 : forall t t', aprovable E (FEq t t') -> P0 (FEq t t'))
  (H4 : forall t t' t'', aprovable E (FEq t t') -> scprovable E (FEq t' t'') ->
    P (FEq t' t'') -> esubterms E t t'' t' -> P0 (FEq t t''))
  (H5 : forall t t', provable_scong E (FEq t t') -> P2 (FEq t t') -> P1 (FEq t t'))
  (H6 : forall t t' t'', provable_scong E (FEq t t') -> P2 (FEq t t') ->
    provable_sachain E (FEq t' t'') -> P0 (FEq t' t'') -> esubterms E t t'' t' ->
    P1 (FEq t t''))
  (H7 : forall n l l', Forall2 (fun t t' : term => P (FEq t t')) l l' -> P2 (FEq (Fn n l) (Fn n l'))).

Fixpoint scprovable_ind f (H' : scprovable E f) : P f :=
  match H' in scprovable _ f return P f with
  | scpr_FEq_refl t => H0 t
  | scpr_prsac t t' Hac => H1 t t' Hac (provable_sachain_ind (FEq t t') Hac)
  | scpr_prscc t t' Hcc => H2 t t' Hcc (provable_scchain_ind (FEq t t') Hcc) end
with provable_sachain_ind f (Hac : provable_sachain E f ): P0 f :=
  match Hac in provable_sachain _ f return P0 f with
  | prsac_apr t t' Ha => H3 t t' Ha
  | prsac_trans t t' t'' Ha H' Hsubs => H4 t t' t'' Ha H' (scprovable_ind (FEq t' t'') H') Hsubs end
with provable_scchain_ind f (Hcc : provable_scchain E f) : P1 f :=
  match Hcc in provable_scchain _ f return P1 f with
  | prscc_prsc t t' Hc => H5 t t' Hc (provable_scong_ind (FEq t t') Hc)
  | prscc_trans t t' t'' Hc Hac Hsubs => H6 t t' t'' Hc (provable_scong_ind (FEq t t') Hc)
    Hac (provable_sachain_ind (FEq t' t'') Hac) Hsubs end
with provable_scong_ind f (Hc : provable_scong _ f) : P2 f :=
  match Hc in provable_scong _ f return P2 f with
  | prsc_fun_compat n l l' HF2' => H7 n l l'
    (Forall2_ind (Forall2 (fun t t' => P (FEq t t')))
      (Forall2_nil _) (fun f0 f'0 l0 l'0 H00 H10 H20 => Forall2_cons _ _
        (scprovable_ind _ H00) H20) HF2') end.

End scprovable_ind.

Register Scheme scprovable_ind as ind_nodep for scprovable.
Register Scheme provable_sachain_ind as ind_nodep for provable_sachain.
Register Scheme provable_scchain_ind as ind_nodep for provable_scchain.
Register Scheme provable_scong_ind as ind_nodep for provable_scong.

Ltac sprovable_align induction_principle :=
  let s := fresh in
  let H := fresh in
  let Pac := fresh in
  let Pcc := fresh in
  let Pc := fresh in
  let P := fresh in
  let H' := fresh in
  ssimpl ; funext => s ? ; apply prop_ext ; intro H ;
  [ intros Pac Pcc Pc P H' ; apply (induction_principle s P Pac Pcc Pc) ; auto ;
    clear H ; intros ; apply H' ; breakgoal
  | apply (H (provable_sachain s) (provable_scchain s) (provable_scong s) (scprovable s)) ;
    clearall ; repeat split ; intros f H ; full_destruct ;
    blindrewrite ; (try now constructor) ;
    match goal with t:term , t':term |- _ => (try now apply (prsac_trans s t t')) ;
    now apply (prscc_trans s t t') end
  ].

Lemma vdash4_def : scprovable = (fun E : form -> Prop => fun a3 : form => forall vdash2_sachain' : form -> Prop, forall vdash2_scchain' : form -> Prop, forall vdash2_scong' : form -> Prop, forall vdash4' : form -> Prop, ((forall a0 : form, ((exists s : term, exists t : term, (a0 = (FEq s t)) /\ (aprovable E (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a0 = (FEq s u)) /\ ((aprovable E (FEq s t)) /\ ((vdash4' (FEq t u)) /\ (@IN term t (esubterms E s u)))))) -> vdash2_sachain' a0) /\ ((forall a1 : form, ((exists s : term, exists t : term, (a1 = (FEq s t)) /\ (vdash2_scong' (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a1 = (FEq s u)) /\ ((vdash2_scong' (FEq s t)) /\ ((vdash2_sachain' (FEq t u)) /\ (@IN term t (esubterms E s u)))))) -> vdash2_scchain' a1) /\ ((forall a2 : form, (exists f : N, exists a : list term, exists b : list term, (a2 = (FEq (Fn f a) (Fn f b))) /\ (@List.Forall2 term term (fun l : term => fun r : term => vdash4' (FEq l r)) a b)) -> vdash2_scong' a2) /\ (forall a3' : form, (exists s : term, exists t : term, (a3' = (FEq s t)) /\ ((s = t) \/ ((vdash2_sachain' (FEq s t)) \/ (vdash2_scchain' (FEq s t))))) -> vdash4' a3')))) -> vdash4' a3).
Proof. sprovable_align scprovable_ind. Qed.

Lemma vdash2_sachain_def : provable_sachain = (fun E : form -> Prop => fun a0 : form => forall vdash2_sachain' : form -> Prop, forall vdash2_scchain' : form -> Prop, forall vdash2_scong' : form -> Prop, forall vdash4' : form -> Prop, ((forall a0' : form, ((exists s : term, exists t : term, (a0' = (FEq s t)) /\ (aprovable E (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a0' = (FEq s u)) /\ ((aprovable E (FEq s t)) /\ ((vdash4' (FEq t u)) /\ (@IN term t (esubterms E s u)))))) -> vdash2_sachain' a0') /\ ((forall a1 : form, ((exists s : term, exists t : term, (a1 = (FEq s t)) /\ (vdash2_scong' (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a1 = (FEq s u)) /\ ((vdash2_scong' (FEq s t)) /\ ((vdash2_sachain' (FEq t u)) /\ (@IN term t (esubterms E s u)))))) -> vdash2_scchain' a1) /\ ((forall a2 : form, (exists f : N, exists a : list term, exists b : list term, (a2 = (FEq (Fn f a) (Fn f b))) /\ (@List.Forall2 term term (fun l : term => fun r : term => vdash4' (FEq l r)) a b)) -> vdash2_scong' a2) /\ (forall a3 : form, (exists s : term, exists t : term, (a3 = (FEq s t)) /\ ((s = t) \/ ((vdash2_sachain' (FEq s t)) \/ (vdash2_scchain' (FEq s t))))) -> vdash4' a3)))) -> vdash2_sachain' a0).
Proof. sprovable_align provable_sachain_ind. Qed.

Lemma vdash2_scchain_def : provable_scchain = (fun E : form -> Prop => fun a1 : form => forall vdash2_sachain' : form -> Prop, forall vdash2_scchain' : form -> Prop, forall vdash2_scong' : form -> Prop, forall vdash4' : form -> Prop, ((forall a0 : form, ((exists s : term, exists t : term, (a0 = (FEq s t)) /\ (aprovable E (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a0 = (FEq s u)) /\ ((aprovable E (FEq s t)) /\ ((vdash4' (FEq t u)) /\ (@IN term t (esubterms E s u)))))) -> vdash2_sachain' a0) /\ ((forall a1' : form, ((exists s : term, exists t : term, (a1' = (FEq s t)) /\ (vdash2_scong' (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a1' = (FEq s u)) /\ ((vdash2_scong' (FEq s t)) /\ ((vdash2_sachain' (FEq t u)) /\ (@IN term t (esubterms E s u)))))) -> vdash2_scchain' a1') /\ ((forall a2 : form, (exists f : N, exists a : list term, exists b : list term, (a2 = (FEq (Fn f a) (Fn f b))) /\ (@List.Forall2 term term (fun l : term => fun r : term => vdash4' (FEq l r)) a b)) -> vdash2_scong' a2) /\ (forall a3 : form, (exists s : term, exists t : term, (a3 = (FEq s t)) /\ ((s = t) \/ ((vdash2_sachain' (FEq s t)) \/ (vdash2_scchain' (FEq s t))))) -> vdash4' a3)))) -> vdash2_scchain' a1).
Proof. sprovable_align provable_scchain_ind. Qed.

Lemma vdash2_scong_def : provable_scong = (fun E : form -> Prop => fun a2 : form => forall vdash2_sachain' : form -> Prop, forall vdash2_scchain' : form -> Prop, forall vdash2_scong' : form -> Prop, forall vdash4' : form -> Prop, ((forall a0 : form, ((exists s : term, exists t : term, (a0 = (FEq s t)) /\ (aprovable E (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a0 = (FEq s u)) /\ ((aprovable E (FEq s t)) /\ ((vdash4' (FEq t u)) /\ (@IN term t (esubterms E s u)))))) -> vdash2_sachain' a0) /\ ((forall a1 : form, ((exists s : term, exists t : term, (a1 = (FEq s t)) /\ (vdash2_scong' (FEq s t))) \/ (exists s : term, exists t : term, exists u : term, (a1 = (FEq s u)) /\ ((vdash2_scong' (FEq s t)) /\ ((vdash2_sachain' (FEq t u)) /\ (@IN term t (esubterms E s u)))))) -> vdash2_scchain' a1) /\ ((forall a2' : form, (exists f : N, exists a : list term, exists b : list term, (a2' = (FEq (Fn f a) (Fn f b))) /\ (@List.Forall2 term term (fun l : term => fun r : term => vdash4' (FEq l r)) a b)) -> vdash2_scong' a2') /\ (forall a3 : form, (exists s : term, exists t : term, (a3 = (FEq s t)) /\ ((s = t) \/ ((vdash2_sachain' (FEq s t)) \/ (vdash2_scchain' (FEq s t))))) -> vdash4' a3)))) -> vdash2_scong' a2).
Proof. sprovable_align provable_scong_ind. Qed.

Definition Eqclause_Func (c : N*N) := let (n,m) := c in
  let l := Varpairs m in
  [set` (FEq (Fn n (map fst l)) (Fn n (map snd l)) ::
   map (fun c' => Not (FEq (fst c') (snd c'))) l)].

Lemma Eqclause_Func_def : Eqclause_Func = (fun _554544 : prod N N => @set_of_list form (@cons form (FEq (Fn (@fst N N _554544) (@List.map (prod term term) term (@fst term term) (Varpairs (@snd N N _554544)))) (Fn (@fst N N _554544) (@List.map (prod term term) term (@snd term term) (Varpairs (@snd N N _554544))))) (@List.map (prod term term) form (@ε ((prod term term) -> form) (fun f : (prod term term) -> form => forall s : term, forall t : term, @eq form (f (@pair term term s t)) (Not (FEq s t)))) (Varpairs (@snd N N _554544))))).
Proof.
  apply funext ; case=> n m ; rewrite/Eqclause_Func/set_of_list /=.
  match goal with | |- [set` (?a::map _ ?l)] = _ =>
    apply (f_equal (fun f => [set` (a :: map f l)])) end.
  by align_ε => // ? H H' ; ext ; case => t t' ; rewrite H H'.
Qed.

Definition Eqclause_Pred (c : N*N) := let (n,m) := c in
  let l := Varpairs m in
  [set` Atom n (map snd l) :: Not (Atom n (map fst l)) ::
     map (fun c' => Not (FEq (fst c') (snd c'))) l].

Lemma Eqclause_Pred_def : Eqclause_Pred = (fun _554553 : prod N N => @set_of_list form (@cons form (Atom (@fst N N _554553) (@List.map (prod term term) term (@snd term term) (Varpairs (@snd N N _554553)))) (@cons form (Not (Atom (@fst N N _554553) (@List.map (prod term term) term (@fst term term) (Varpairs (@snd N N _554553))))) (@List.map (prod term term) form (@ε ((prod term term) -> form) (fun f : (prod term term) -> form => forall s : term, forall t : term, @eq form (f (@pair term term s t)) (Not (FEq s t)))) (Varpairs (@snd N N _554553)))))).
Proof.
  apply funext ; case=> n m ; rewrite/Eqclause_Func/set_of_list /=.
  match goal with | |- [set` (?a::?b::map _ ?l)] = _ =>
    apply (f_equal (fun f => [set` (a :: b :: map f l)])) end.
  by align_ε => // ? H H' ; ext ; case => t t' ; rewrite H H'.
Qed.

Definition Eqclauses (L : set (N*N) * set (N*N)) := let (s,s') := L in
  [set FEq (V 0) (V 0)] |` (
    [set Not (FEq (V 0) (V 1)) ; Not (FEq (V 2) (V 1)) ; FEq (V 0) (V 2)] |` (
      Eqclause_Func @` s `|` Eqclause_Pred @` s' )).

Lemma Eqclauses_def : Eqclauses = (fun _554562 : prod ((prod N N) -> Prop) ((prod N N) -> Prop) => @INSERT (form -> Prop) (@INSERT form (FEq (V (NUMERAL N0)) (V (NUMERAL N0))) (@set0 form)) (@INSERT (form -> Prop) (@INSERT form (Not (FEq (V (NUMERAL N0)) (V (NUMERAL (BIT1 N0))))) (@INSERT form (Not (FEq (V (NUMERAL (BIT0 (BIT1 N0)))) (V (NUMERAL (BIT1 N0))))) (@INSERT form (FEq (V (NUMERAL N0)) (V (NUMERAL (BIT0 (BIT1 N0))))) (@set0 form)))) (@setU (form -> Prop) (@GSPEC (form -> Prop) (fun GEN_PVAR_666 : form -> Prop => exists fa : prod N N, @SETSPEC (form -> Prop) GEN_PVAR_666 (@IN (prod N N) fa (@fst ((prod N N) -> Prop) ((prod N N) -> Prop) _554562)) (Eqclause_Func fa))) (@GSPEC (form -> Prop) (fun GEN_PVAR_667 : form -> Prop => exists pa : prod N N, @SETSPEC (form -> Prop) GEN_PVAR_667 (@IN (prod N N) pa (@snd ((prod N N) -> Prop) ((prod N N) -> Prop) _554562)) (Eqclause_Pred pa)))))).
Proof.
  by apply funext ; case => n m ; ssimpl ; rewrite/Eqclauses ?setUA.
Qed.

Definition Eqaxiom_Pred_imp c := uclose
  (FImp (fold_right FAnd FTrue (map (fun c => FEq (fst c) (snd c)) (Varpairs (snd c))))
     (FImp (Atom (fst c) (map fst (Varpairs (snd c)))) (Atom (fst c) (map snd (Varpairs (snd c)))))).

Lemma Eqaxiom_Pred_imp_def : Eqaxiom_Pred_imp = (fun _554616 : prod N N => uclose (FImp (@fold_right_with_perm_args form form FAnd (@List.map (prod term term) form (@ε ((prod term term) -> form) (fun f : (prod term term) -> form => forall s : term, forall t : term, @eq form (f (@pair term term s t)) (FEq s t))) (Varpairs (@snd N N _554616))) FTrue) (FImp (Atom (@fst N N _554616) (@List.map (prod term term) term (@fst term term) (Varpairs (@snd N N _554616)))) (Atom (@fst N N _554616) (@List.map (prod term term) term (@snd term term) (Varpairs (@snd N N _554616))))))).
Proof.
  have <- : (fun c => FEq (fst c) (snd c)) =
    ε (fun f => forall s t, f (s,t) = FEq s t) ; last by [].
  by align_ε => // func' H H' ; ext ; case => * ; rewrite H H'.
Qed.

(*****************************************************************************)
(* Logic/trs.ml *)
(*****************************************************************************)

(* term rewritings *)
Inductive TRS (rw_rules : term * term -> Prop) : term -> term -> Prop :=
| TRS_subst : forall v t t', rw_rules (t,t') ->
  TRS rw_rules (termsubst v t) (termsubst v t')
| TRS_rec : forall t t' n l l', TRS rw_rules t t' ->
  TRS rw_rules (Fn n (l++t::l')) (Fn n (l++t'::l')).

Lemma TRS_def : TRS = (fun rws : (prod term term) -> Prop => fun a0 : term => fun a1 : term => forall TRS' : term -> term -> Prop, (forall a0' : term, forall a1' : term, ((exists i : N -> term, exists l : term, exists r : term, (a0' = (termsubst i l)) /\ ((a1' = (termsubst i r)) /\ (@IN (prod term term) (@pair term term l r) rws))) \/ (exists s : term, exists t : term, exists f : N, exists largs : list term, exists rargs : list term, (a0' = (Fn f (@app term largs (@cons term s rargs)))) /\ ((a1' = (Fn f (@app term largs (@cons term t rargs)))) /\ (TRS' s t)))) -> TRS' a0' a1') -> TRS' a0 a1).
Proof. ssimpl ; ind_align. Qed.

(*****************************************************************************)
(* Logic/lpo.ml *)
(*****************************************************************************)

Definition NONWF {A : Type} (R : A -> A -> Prop) (x : A) :=
  exists s, s 0 = x /\ forall n, R (s (N.succ n)) (s n).

Lemma NONWF_def {A : Type'} :  (@NONWF A) = (fun _563585 : A -> A -> Prop => fun _563586 : A => ex (fun s : N -> A => (eq (s (NUMERAL N0)) _563586) /\ (forall n : N, _563585 (s (N.succ n)) (s n)))).
Proof erefl.

Fixpoint termsize t :=
  match t with
  | V _ => 1
  | Fn _ l => fold_right N.add 1 (map termsize l) end.

Lemma termsize_def : termsize = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> term -> N) (fun termsize' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> term -> N => forall _564457 : prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))), (forall x : N, (termsize' _564457 (V x)) = (NUMERAL (BIT1 N0))) /\ (forall f : N, forall args : list term, (termsize' _564457 (Fn f args)) = (@fold_right_with_perm_args N N N.add (@List.map term N (termsize' _564457) args) (NUMERAL (BIT1 N0))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))))))))))).
Proof. term_align. Qed.

Inductive LEX {A : Type} (R : A -> A -> Prop) : list A -> list A -> Prop :=
| LEX_R : forall x l x' l', R x x' -> length l = length l' -> LEX R (x::l) (x'::l')
| LEX_eq : forall x l l', LEX R l l' -> LEX R (x::l) (x::l').

Lemma LEX_length {A : Type} (R : A -> A -> Prop) l l' :
  LEX R l l' -> length l = length l'.
Proof.
  by induction 1 => /= ; f_equal.
Qed.

Lemma LEX_def {_250280 : Type'} : (@LEX _250280) = (@ε ((prod N (prod N N)) -> (_250280 -> _250280 -> Prop) -> (list _250280) -> (list _250280) -> Prop) (fun LEX' : (prod N (prod N N)) -> (_250280 -> _250280 -> Prop) -> (list _250280) -> (list _250280) -> Prop => forall _564465 : prod N (prod N N), (forall lt2' : _250280 -> _250280 -> Prop, forall l : list _250280, (LEX' _564465 lt2' (@nil _250280) l) = False) /\ (forall h : _250280, forall lt2' : _250280 -> _250280 -> Prop, forall t : list _250280, forall l : list _250280, (LEX' _564465 lt2' (@cons _250280 h t) l) = (@COND Prop (l = (@nil _250280)) False (@COND Prop (lt2' h (@HOLLight.Real_With_N.mappings.hd _250280 l)) ((@lengthN _250280 t) = (@lengthN _250280 (@HOLLight.Real_With_N.mappings.tl _250280 l))) ((h = (@HOLLight.Real_With_N.mappings.hd _250280 l)) /\ (LEX' _564465 lt2' t (@HOLLight.Real_With_N.mappings.tl _250280 l))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 N0))))))))))).
Proof.
  total_align ; first by ext ; inversion 1.
  if_list ; destruct l ; first by ext ; inversion 1.
  if_intro => H ; last by ext ; first inversion 1 ; last (move=>[->] ; right).
  by rewrite -lengthN_eqE ; ext ; first move/LEX_length=> [=] ; last left.
Qed.

Inductive subterm : term -> term -> Prop :=
| subterm_refl : forall t, subterm t t
| subterm_rec : forall t t' n l, subterm t t' -> In t' l -> subterm t (Fn n l).

Lemma subterm_def : subterm = (fun a0 : term => fun a1 : term => forall subterm' : term -> term -> Prop, (forall a0' : term, forall a1' : term, ((a1' = a0') \/ (exists a : term, exists f : N, exists args : list term, (a1' = (Fn f args)) /\ ((subterm' a0' a) /\ (@List.In term a args)))) -> subterm' a0' a1') -> subterm' a0 a1).
Proof. ind_align. Qed.

Definition psubterm t t' := (subterm t t' /\ t <> t').

Lemma psubterm_def : psubterm = (fun _567009 : term => fun _567010 : term => (subterm _567009 _567010) /\ (~ (eq _567009 _567010))).
Proof erefl.

Unset Elimination Schemes.
Inductive lpo : term -> term -> Prop :=
| lpo_free : forall n t, free_variables_term t n -> t <> V n -> lpo (V n) t
| lpo_psubterm1 : forall n l n' l' t, In t l' -> lpo (Fn n l) t ->
                lpo (Fn n l) (Fn n' l')
| lpo_psubterm2 : forall n l n' l' t, In t l' -> t = Fn n l ->
                lpo (Fn n l) (Fn n' l')
| lpo_Fn_smaller : forall n l n' l', n' > n \/ (n' = n /\ (length l' > length l)%nat) ->
         Forall (fun t => lpo t (Fn n' l')) l -> lpo (Fn n l) (Fn n' l')
| lpo_LEX : forall n l l', Forall (fun t => lpo t (Fn n l')) l -> LEX lpo l l' ->
            lpo (Fn n l) (Fn n l').
Set Elimination Schemes.

Scheme lpo_ind0 := Minimality for lpo Sort Prop.

Fixpoint lpo_ind P H0 H1 H2 
  (H3 : forall n l n' l', n' > n \/ (n' = n /\ (length l' > length l)%nat) ->
    Forall (fun t : term => P t (Fn n' l')) l -> P (Fn n l) (Fn n' l'))
  (H4 : forall n l l', Forall (fun t : term => P t (Fn n l')) l -> LEX lpo l l' ->
    LEX P l l' -> P (Fn n l) (Fn n l'))
  t t' (H5 : lpo t t') : P t t' :=
  lpo_ind0 P H0 H1 H2
    (fun n l n' l' H0' H1' => H3 n l n' l' H0' (Forall_ind (Forall (fun t => P t (Fn n' l')))
      (Forall_nil _) 
      (fun t0 l0 H00 _ H10 => Forall_cons _ (lpo_ind P H0 H1 H2 H3 H4 _ _ H00) H10) H1'))
    (fun n l l' H0' H1' => H4 n l l' (Forall_ind (Forall (fun t => P t (Fn n l')))
      (Forall_nil _) 
      (fun t0 l0 H00 _ H10 => Forall_cons _ (lpo_ind P H0 H1 H2 H3 H4 _ _ H00) H10) H0')
      H1'
      (LEX_ind _ _ (LEX P)
        (fun t0 l0 t0' l0' H00 H10 => LEX_R P t0 l0 t0' l0' 
          (lpo_ind P H0 H1 H2 H3 H4 _ _ H00) H10)
        (fun t0 l0 l0' _ H00 => LEX_eq P t0 l0 l0' H00) l l' H1')) t t' H5.

Register Scheme lpo_ind as ind_nodep for lpo.

Lemma lpo_def : lpo = (fun a0 : term => fun a1 : term => forall lt2' : term -> term -> Prop, (forall a0' : term, forall a1' : term, ((exists x : N, (a0' = (V x)) /\ ((@IN N x (free_variables_term a1')) /\ (~ (a1' = (V x))))) \/ ((exists fs : N, exists sargs : list term, exists ft : N, exists targs : list term, exists si : term, (a0' = (Fn ft targs)) /\ ((a1' = (Fn fs sargs)) /\ ((@List.In term si sargs) /\ ((lt2' (Fn ft targs) si) \/ (si = (Fn ft targs)))))) \/ ((exists fs : N, exists ft : N, exists sargs : list term, exists targs : list term, (a0' = (Fn ft targs)) /\ ((a1' = (Fn fs sargs)) /\ (((N.gt fs ft) \/ ((fs = ft) /\ (N.gt (@lengthN term sargs) (@lengthN term targs)))) /\ (@List.Forall term (fun ti : term => lt2' ti (Fn fs sargs)) targs)))) \/ (exists f : N, exists sargs : list term, exists targs : list term, (a0' = (Fn f targs)) /\ ((a1' = (Fn f sargs)) /\ ((@List.Forall term (fun ti : term => lt2' ti (Fn f sargs)) targs) /\ (@LEX term lt2' targs sargs))))))) -> lt2' a0' a1') -> lt2' a0 a1).
Proof.
  ssimpl ; ind_align.
  - breakgoal by rewrite -lengthN_gtE.
  - by subst ; apply lpo_Fn_smaller => // ; rewrite lengthN_gtE ; auto.
Qed.