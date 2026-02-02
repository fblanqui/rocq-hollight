From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype choice seq.
From mathcomp Require Import boolp functions.
From mathcomp Require Export classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(****************************************************************************)
(* Type of non-empty types, used to interpret HOL-Light types types. *)
(****************************************************************************)

(* Exact same as isPointed, but we will derive choice and decidable
   equality for it, which could be bad for types that have
   their own choice/eq defined in ssreflect (like nat) if it were derived
   from isPointed directly, because it has an instance of isPointed,
   which would make it so it has two defined equalities.

   This should only be used for types without a predefined decidable equality *)

HB.factory Record HOL_isPointed T := {point : T}.

Notation is_Type' := (HOL_isPointed.Build _).

(* in classical context, is a factory for pointedType *)
HB.builders Context T of HOL_isPointed T.

HB.instance Definition _ := isPointed.Build _ point.

HB.instance Definition _ := gen_eqMixin T.

HB.instance Definition _ := gen_choiceMixin T.

HB.end.

Notation Type' := pointedType.

(* Type' is the type of Types of HOL-Light (HOL-Light considers pointed types) *)
(* To define an instance of Type' for a non-empty type [T], use :
   [HB.instance Definition _ := is_Type' a] for some [a : T] *)

(* The most important types and type constructors already have an instance as Type' *)

(****************************************************************************)
(* Extensionalities *)
(****************************************************************************)

(* tactic ext should cover almost all cases of need with functional and propositional
   extensionality and their combinations. *)

(* Axiom propext : forall P Q, P <-> Q -> P = Q *)
Lemma prop_ext : forall P Q : Prop, (P -> Q) -> (Q -> P) -> P = Q.
Proof.
  by move=> *; eqProp.
Qed.

(* Axiom functional_extensionality_dep :
   forall f g, (forall x, f x = g x) -> f = g *)
Notation funext := functional_extensionality_dep.

(* applies them to all arguments and propositions at once *)
Tactic Notation "ext" :=
  let rec ext' := (let H := fresh in
    first [apply funext | eqProp]=> H ; try ext' ; move:H)
  in ext'.

(* with a counter added to the context to apply it for exactly n arguments/propositions *)
Variant internal_witness : forall A, A -> Type :=
  w0 A : forall a : A, internal_witness a.

Definition addone : forall n, internal_witness n -> internal_witness n.+1 :=
  fun n _ => w0 n.+1.

Ltac typecheck A a := assert_succeeds let s:=fresh in set (s := a : A).

Tactic Notation "ext" integer(n) :=
  let ext0 x w := (first [apply funext | eqProp]=>x ; set (w := w0 x))
   (* choosing the fresh variables inside ext0 fails to create new variable names. *)
  in do n (let x := fresh in let w := fresh in ext0 x w) ;
  repeat match goal with | x : _ |- _  =>
  lazymatch goal with w : internal_witness x |- _ => clear w ; revert x end end.

(* Example of use :
Lemma test : (fun f g : nat -> nat => (f=g)) = (fun f g : nat -> nat => (f=g)).
Proof.
(*  ext=> f g H n. *) (* or *)
(*  ext 3 => f g H. *)
  auto.
Qed. *)

(* Small issue : the witnesses are present in the proof term. How bad is it?
   Example :
   Lemma test (f : nat -> nat -> nat -> nat -> nat -> nat -> nat -> nat) : f = f.
   Proof. by ext 7. Qed.
   Print test.

   This means that ext should be prefered to ext n if possible. *)

(****************************************************************************)
(* Repeating exists. *)
(****************************************************************************)

Tactic Notation "exist" uconstr(x1) uconstr(x2) :=
  exists x1 ; exists x2.

Tactic Notation "exist" uconstr(x1) uconstr(x2) uconstr(x3) :=
  exists x1 ; exists x2 ; exists x3.

Tactic Notation "exist" uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) :=
  exists x1 ; exists x2 ; exists x3 ; exists x4.

Tactic Notation "exist" uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) uconstr(x5) :=
  exists x1 ; exists x2 ; exists x3 ; exists x4 ; exists x5.

(****************************************************************************)
(* Coercion from Prop to bool? *)
(****************************************************************************)

Coercion asbool : Sortclass >-> bool.

Ltac booleqsimp := rewrite ?eqb_id ?eqbF_neg.

Lemma bool_eq_decompP : forall a b : bool, is_true (a==b) = (is_true a = is_true b).
Proof.
  by move=> [] [] ; ext ; booleqsimp ; rewrite //= ; first (move <-) ; last (move ->).
Qed.

Ltac AllProp := rewrite -?eq_opE ?bool_eq_decompP ?asboolE.

(* Check and : bool -> bool -> bool. *)

(****************************************************************************)
(* Coercion from nat to N ? *)
(****************************************************************************)
(* TODO : For another time, if the double coercion between bool and Prop works out.
          it would require to either remove nat_of_bin as a coercion and implement
          N.of_nat and N.to_nat from Stdlib.NArith.Nnat as coercions instead,
          or prove isomorphism (conversions for the most important functions
          and relations) as ssrnat has basically none, especially for bin_of_nat.
          could allow to use for example nth or length on lists.

Require Import Stdlib.NArith.BinNat.
Coercion bin_of_nat : nat >-> N.

(* nat_of_bin is already defined as a coercion in ssrnat. *)

(* Check S : N -> N. *) *)

(****************************************************************************)
(* Curryfied versions of some Rocq connectives. *)
(****************************************************************************)

Definition arr (A B : Type') : Type' := A -> B.

Definition imp (P Q : Prop) : Prop := P -> Q.

Definition ex1 : forall (A : Type'), (A -> Prop) -> Prop := fun A P => exists! x, P x.

(****************************************************************************)
(* Proof of some HOL-Light rules. *)
(****************************************************************************)

Lemma MK_COMB (a b : Type') (s t : a -> b) (u v : a) (h1 : s = t) (h2 : u = v)
  : (s u) = (t v).
Proof. by rewrite h1 h2. Qed.

Lemma EQ_MP (p q : Prop) (e : p = q) (h : p) : q.
Proof. by rewrite -e. Qed.

(* erefl with non-implicit second parameter. *)
Definition REFL A x := @erefl A x.

(****************************************************************************)
(* Proof of some natural deduction rules. *)
(****************************************************************************)

Lemma or_intro1 (p:Prop) (h : p) (q:Prop) : p \/ q.
Proof. exact (@or_introl p q h). Qed.

Lemma or_elim (p q : Prop) (h : p \/ q) (r : Prop) (h1: p -> r) (h2: q -> r) : r.
Proof. exact (@or_ind p q r h1 h2 h). Qed.

Lemma ex_elim a (p : a -> Prop)
  (h1 : exists x, p x) (r : Prop) (h2 : forall x : a, (p x) -> r) : r.
Proof. exact (@ex_ind a p r h2 h1). Qed.

(****************************************************************************)
(* Hilbert's ε operator. *)
(****************************************************************************)

Definition ε (A : Type') (P : A -> Prop) := get P.

Definition ε_spec {A : Type'} {P : A -> Prop} : (exists x, P x) -> P (ε P) := @getPex _ P.

Lemma align_ε (A : Type') (P : A -> Prop) a : P a -> (forall x, P a -> P x -> a = x) -> a = ε P.
Proof. 
  by move => ha ; apply ; last (apply ε_spec ; exists a).
Qed.

Lemma is_True P : (P = True) = P.
Proof.
  by ext=> // ->.
Qed.

(* From a proof of P (either a hypothesis or a lemma), rewrite P into True. *)
Ltac is_True H :=
  let H' := fresh in set (H' := H) ;
  match type of H' with ?P => rewrite <- (is_True P) in H' ;
    rewrite -> H' in * ; clear H' ; try clear H end.

Lemma is_False P : (P = False) = ~ P.
Proof.
  by ext=> // ->.
Qed.

(* From hypothesis H : ~P, rewrite P into False *)
Ltac is_False H :=
  let H' := fresh in set (H' := H) ;
  match type of H' with ~?P => rewrite <- (is_False P) in H' ;
    rewrite -> H' in * ; clear H' ; try clear H end.

Lemma prop_degen : forall P, P = True \/ P = False.
Proof.
  move=>P ; rewrite is_False is_True ; exact (EM _).
Qed.

Lemma sym {A} (x y : A) : (x = y) = (y = x).
Proof. by ext. Qed.

(****************************************************************************)
(* if then else over Prop *)
(****************************************************************************)

Definition COND (A : Type) (P : Prop) (x y : A) := if P then x else y.

Lemma if_True (A : Type) (x y : A) : (if True then x else y) = x.
Proof.
  by rewrite/asbool ; case pselect.
Qed.

Lemma if_False (A : Type) (x y : A) : (if False then x else y) = y.
Proof.
by rewrite/asbool ; case pselect.
Qed.

Lemma COND_def {A : Type'} : (@COND A) = (fun t : Prop => fun t1 : A => fun t2 : A => @ε A (fun x : A => ((t = True) -> x = t1) /\ ((t = False) -> x = t2))).
Proof.
  ext=> P x y ; apply align_ε ; first by split=> -> ; rewrite/COND ?if_True ?if_False.
  move=> f' [CT CF] [f'T f'F] ; case : (prop_degen P) => H ; first by rewrite (CT H) f'T.
  by rewrite (CF H) f'F.
Qed.

Definition COND_dep (Q: Prop) (C: Type) (f1: Q -> C) (f2: ~Q -> C) : C :=
  match pselect Q with
  | left x => f1 x
  | right x => f2 x
  end.

(****************************************************************************)
(* Derive proof irrelevance. *)
(****************************************************************************)

Lemma proof_irrelevance (P : Prop) :
  forall (p p' : P), p = p'.
Proof.
  case (EM P).
  - by rewrite -{1}(is_True P)=>->.
  - by rewrite -(is_False P).
Qed.

Arguments proof_irrelevance: clear implicits.

(****************************************************************************)
(* Proof of HOL-Light axioms. *)
(****************************************************************************)

Lemma axiom_0 : forall {A B : Type'}, forall t : A -> B, (fun x : A => t x) = t.
Proof. by []. Qed.

Lemma axiom_1 : forall {A : Type'}, forall P : A -> Prop, forall x : A, (P x) -> P (@ε A P).
Proof.
  by move=> A P x H ; apply ε_spec ; exists x.
Qed.

(****************************************************************************)
(* Alignment of connectives. *)
(****************************************************************************)

Lemma ex1_def : forall {A : Type'}, (@ex1 A) = (fun P : A -> Prop => (ex P) /\ (forall x : A, forall y : A, ((P x) /\ (P y)) -> x = y)).
Proof.
  rewrite/ex1=> A ; ext=> [P [x [Hx Hunique]] | P [[x Hx] Hunique]].
  - by split ; first exists x ; last move=> y z [/Hunique<- /Hunique<-].
  - by exists x ; split ; last (move=> * ; apply Hunique).
Qed.

Lemma F_def : False = (forall p : Prop, p).
Proof.
  by eqProp=>H ; first destruct H ; apply H.
Qed.

Lemma not_def : not = (fun p : Prop => p -> False).
Proof. reflexivity. Qed.

Lemma or_def : or = (fun p : Prop => fun q : Prop => forall r : Prop, (p -> r) -> (q -> r) -> r).
Proof.
  ext=> [P Q []|P Q] ; last apply ; tauto.
Qed.

Lemma ex_def : forall {A : Type'}, (@ex A) = (fun P : A -> Prop => forall q : Prop, (forall x : A, (P x) -> q) -> q).
Proof.
  by move=> A ; ext=> P ; last apply ; firstorder.
Qed.

Lemma all_def : forall {A : Type'}, (@Logic.all A) = (fun P : A -> Prop => P = (fun x : A => True)).
Proof.
  by move=>A ; ext=> [|| P ->].
Qed.

Lemma imp_def : imp = (fun p : Prop => fun q : Prop => (p /\ q) = p).
Proof.
  by ext=>[||P Q <-] ; firstorder.
Qed.

Lemma and_def : and = (fun p : Prop => fun q : Prop => (fun f : Prop -> Prop -> Prop => f p q) = (fun f : Prop -> Prop -> Prop => f True True)).
Proof.
  ext=>[||P Q e] ; last by pattern and ; rewrite e.
  1,2 : by move=> P Q [HP HQ] ; is_True HP ; is_True HQ.
Qed.

Lemma T_def : True = ((fun p : Prop => p) = (fun p : Prop => p)).
Proof. by ext 1. Qed.

(*****************************************************************************)
(* Alignment of subtypes. *)
(*****************************************************************************)

Section Subtype.

  Variables (A : Type) (P : A -> Prop) (a : A) (h : P a).

  Definition subtype (h : P a) := {x | P x}.

  HB.instance Definition _ := HOL_isPointed.Build (subtype h) (exist P a h).

  Definition dest : subtype h -> A := fun x => proj1_sig x.

  Definition mk : A -> subtype h :=
    fun x => COND_dep (exist P x) (fun _ => exist P a h).

  Lemma dest_mk_aux x : P x -> (dest (mk x) = x).
  Proof.
    by move=> Px ; rewrite/mk/COND_dep ; case:(pselect (P x)).
  Qed.

  Lemma dest_mk x : P x = (dest (mk x) = x).
  Proof.
    by ext=> [|<-] ; first exact (@dest_mk_aux x) ; last case:(mk x).
  Qed.

  Lemma mk_dest x : mk (dest x) = x.
  Proof.
    rewrite/mk/COND_dep; case: (pselect (P (dest x))); case x ; last by [].
    by move=>a' p pa' ; rewrite (proof_irrelevance _ p pa').
  Qed.

  Lemma dest_inj x y : dest x = dest y -> x = y.
  Proof.
    intro e. destruct x as [x i]. destruct y as [y j]. simpl in e.
    subst y. rewrite (proof_irrelevance _ i j). reflexivity.
  Qed.

  Lemma mk_inj x y : P x -> P y -> mk x = mk y -> x = y.
  Proof.
    rewrite/mk/COND_dep=>hx hy.
    by case:(pselect (P x)); case (pselect (P y))=> Hx Hy ; try move=>[=].
  Qed.

End Subtype.

Arguments dest [_] [_] [_] _.
Arguments mk_dest [_] [_] [_] _.

(****************************************************************************)
(* Alignment of the unit type. *)
(****************************************************************************)

Definition one_ABS : Prop -> unit := fun _ => tt.

Definition one_REP : unit -> Prop := fun _ => True.

Lemma axiom_2 : forall (a : unit), (one_ABS (one_REP a)) = a.
Proof. intro a. destruct a. reflexivity. Qed.

Lemma axiom_3 : forall (r : Prop), ((fun b : Prop => b) r) = ((one_REP (one_ABS r)) = r).
Proof. intro r. compute. rewrite (sym True r) is_True. reflexivity. Qed.

Lemma one_def : tt = ε one_REP.
Proof. by case:(ε one_REP). Qed.

(****************************************************************************)
(* Alignment of the product type constructor. *)
(****************************************************************************)

Definition mk_pair {A B : Type'} :=
  fun x : A => fun y : B => fun a : A => fun b : B => (a = x) /\ (b = y).

Lemma mk_pair_def {A B : Type'} : (@mk_pair A B) = (fun x : A => fun y : B => fun a : A => fun b : B => (a = x) /\ (b = y)).
Proof. exact erefl. Qed.

Lemma mk_pair_inj {A B : Type'} {x x' : A} {y y' : B} :
  mk_pair x y = mk_pair x' y' -> x = x' /\ y = y'.
Proof.
 by fold (mk_pair x' y' x y) ; move=><-.
Qed.

Definition ABS_prod : forall {A B : Type'}, (A -> B -> Prop) -> prod A B :=
  fun A B f => ε (fun p => f = mk_pair (fst p) (snd p)).

Lemma ABS_prod_mk_pair {A B : Type'} {x : A} {y : B} :
  (x,y) = ABS_prod (mk_pair x y).
Proof.
  unfold ABS_prod.
  apply align_ε.
  - reflexivity.
  - move=> [x' y'] _ h.
    apply pair_equal_spec.
    exact (mk_pair_inj h).
Qed.

Definition REP_prod : forall {A B : Type'}, (prod A B) -> A -> B -> Prop :=
  fun A B p a b => mk_pair (fst p) (snd p) a b.

Lemma pair_def {A B : Type'} : (@pair A B) = (fun x : A => fun y : B => @ABS_prod A B (@mk_pair A B x y)).
Proof.
  ext=> x y.
  exact ABS_prod_mk_pair.
Qed.

Lemma FST_def {A B : Type'} : (@fst A B) = (fun p : prod A B => @ε A (fun x : A => exists y : B, p = (@pair A B x y))).
Proof.
  ext=> [[x y]].
  apply align_ε.
  - exists y.
    reflexivity.
  - by move => x' _ [y' ->].
Qed.

Lemma SND_def {A B : Type'} : (@snd A B) = (fun p : prod A B => @ε B (fun y : B => exists x : A, p = (@pair A B x y))).
Proof.
  ext=> [[x y]].
  apply align_ε.
  - exists x.
    reflexivity.
  - by move=> y' _ [x' ->].
Qed.

Lemma axiom_4 : forall {A B : Type'} (a : prod A B), (@ABS_prod A B (@REP_prod A B a)) = a.
Proof. intros A B [a b]. symmetry. exact ABS_prod_mk_pair. Qed.

Lemma axiom_5 : forall {A B : Type'} (r : A -> B -> Prop), ((fun x : A -> B -> Prop => exists a : A, exists b : B, x = (@mk_pair A B a b)) r) = ((@REP_prod A B (@ABS_prod A B r)) = r).
Proof.
  intros A B f.
  apply prop_ext.
  - intros [a [b ->]].
    rewrite -ABS_prod_mk_pair.
    reflexivity.
  - generalize (ABS_prod f).
    intros [a b] e.
    exists a.
    exists b.
    rewrite <- e.
    reflexivity.
Qed.

(****************************************************************************)
(* Alignment of the infinite type ind. *)
(****************************************************************************)

Definition ind : Type' := nat.

Definition ONE_ONE A B := @injective B A.

Lemma ONE_ONE_def {A B : Type'} : (@ONE_ONE A B) = (fun _2064 : A -> B => forall x1 : A, forall x2 : A, ((_2064 x1) = (_2064 x2)) -> x1 = x2).
Proof. exact erefl. Qed.

Definition ONTO {A B : Type'} (f : A -> B) := set_surj setT setT f.

Lemma ONTO_def {A B : Type'} : (@ONTO A B) = (fun _2069 : A -> B => forall y : B, exists x : A, y = (_2069 x)).
Proof.
  ext=>f H x ; last by case:(H x)=>x0 eq_fx0_x _ ; exists x0.
  by case: (H x Logic.I)=>x0 _ eq_fx0_x ; exists x0.
Qed.

Lemma axiom_6 : exists f : ind -> ind, (@ONE_ONE ind ind f) /\ (~ (@ONTO ind ind f)).
Proof.
  rewrite ONTO_def.
  exists S.
  split.
  - exact eq_add_S.
  - intro h.
    generalize (h 0).
    intros [x hx].
    discriminate.
Qed.

(****************************************************************************)
(* Notation to easily rewrite a view. *)
(****************************************************************************)

Notation "H **" := (reflect_eq H).

(* example :
Goal forall P Q, ~~ P /\ Q -> ~P /\ Q.
by move=>* ; rewrite negP**.
Abort. *)

(****************************************************************************)
(* To be able to use ext within =>. *)
(****************************************************************************)

(* use /` during ssr intropattern to ext all,
   /f` to only use funext,
   and /n` for n between 1 and 5 ext exactly n arguments / hypotheses. *)

Ltac funext :=
  let rec funext' := (let x := fresh "x" in
    apply funext => x ; try funext' ; move:x)
  in funext'.

Notation "`" := (ltac:(try ext)) (at level 0, only parsing).
Notation "f`" := (ltac:(try funext)) (at level 0, only parsing).

Notation "1`" := (ltac:(first [apply funext | eqProp])) (at level 0, only parsing).

Notation "2`" := (ltac:( let H := fresh in first [apply funext | eqProp]=>H ;
                         first [apply funext | eqProp] ; move: H ))
                           (at level 0, only parsing).

Notation "3`" := (ltac:( let H1 := fresh in first [apply funext | eqProp]=>H1 ;
                         let H2 := fresh in first [apply funext | eqProp]=>H2 ;
                         first [apply funext | eqProp] ; move: H1 H2 ))
                           (at level 0, only parsing).

Notation "4`" := (ltac:( let H1 := fresh in first [apply funext | eqProp]=>H1 ;
                         let H2 := fresh in first [apply funext | eqProp]=>H2 ;
                         let H3 := fresh in first [apply funext | eqProp]=>H3 ;
                         first [apply funext | eqProp] ; move: H1 H2 H3))
                           (at level 0, only parsing).

Notation "5`" := (ltac:( let H1 := fresh in first [apply funext | eqProp]=>H1 ;
                         let H2 := fresh in first [apply funext | eqProp]=>H2 ;
                         let H3 := fresh in first [apply funext | eqProp]=>H3 ;
                         let H4 := fresh in first [apply funext | eqProp]=>H4 ;
                         first [apply funext | eqProp] ; move: H1 H2 H3 H4))
                           (at level 0, only parsing).

(* Definition test (n m k : nat) (f : nat -> nat -> nat) := f = f.
Goal True -> test = test. move => * /f`* /3` H n0 m0. *)

(****************************************************************************)
(* The opposite, transform hypothesis f = g with forall x, f x = g x. *)
(****************************************************************************)

Lemma gen_fun1 A B (f g : forall a : A, B a) : f = g <-> forall a, f a = g a.
Proof.
  by split=>[->|? /f`].
Qed.

Lemma gen_fun2 A B C (f g : forall (a:A) (b:B a), C a b) : f = g <->
  forall a b, f a b = g a b.
Proof.
  by split=>[->|? /f`].
Qed.

Lemma gen_fun3 A B C D (f g: forall (a:A) (b:B a) (c:C a b),D a b c): f = g <->
  forall a b c, f a b c = g a b c.
Proof.
  by split=>[->|? /f`].
Qed.

Lemma gen_fun4 A B C D E (f g: forall (a:A) (b:B a)
  (c:C a b) (d:D a b c), E a b c d) : f = g <->
    forall a b c d, f a b c d = g a b c d.
Proof.
  by split=>[->|? /f`].
Qed.

Lemma gen_fun5 A B C D E F (f g: forall (a:A) (b:B a) (c:C a b)
  (d:D a b c) (e:E a b c d), F a b c d e):  f = g <->
  forall a b c d e, f a b c d e = g a b c d e.
Proof.
  by split=>[->|? /f`].
Qed.

(* /[gen] in an intro pattern to replace partial functional equality in
   the top assumption with fully quantified equality unless the functions
   have more than 5 arguments. /[funext] replaces quantified equality with
   function equality instead. *)
Ltac move_gen_fun := move/gen_fun5 || move/gen_fun4 || move/gen_fun3
  || move/gen_fun2 || move/gen_fun1 ||
  fail "top assumption is not a (possibly quantified) function equality".

Notation "[ 'funext' ]" := ltac:(lazymatch goal with
  | |- _ = _ -> _ =>
    fail "top assumption is an equality, no extensionality can apply"
  | |- _ => move_gen_fun end).

Notation "[ 'gen' ]" := ltac:(try move/[funext] ; move_gen_fun).

(****************************************************************************)
(* specialize the top assumption *)
(****************************************************************************)

Notation "[ 'spec' x ]" :=
  ltac:(let H := fresh "top" in move=>H ; move:{H}(H x)).

Notation "[ 'spec' x | y ]" :=
  ltac:(let H := fresh "top" in move=>H ; move:{H}(H x y)).

Notation "[ 'spec' x | y | z ]" :=
  ltac:(let H := fresh "top" in move=>H ; move:{H}(H x y z)).

Notation "[ 'spec' ]" :=
  ltac:(lazymatch goal with
  | |- (forall _: ?A, _) -> _ => have: A ; last move/[swap]/[apply]
  | |- _ => fail "not a product type in top assumption" end).

Notation "[ 'spec' 'by' [ ] ]" :=
  ltac:(lazymatch goal with
  | |- (forall _: ?A, _) -> _ => (have: A by []) => /[swap]/[apply]
  | |- _ => fail "not a product type in top assumption" end).

(****************************************************************************)
(* Repeating exists. *)
(****************************************************************************)

Tactic Notation "exist" uconstr(x1) uconstr(x2) :=
  exists x1 ; exists x2.

Tactic Notation "exist" uconstr(x1) uconstr(x2) uconstr(x3) :=
  exists x1 ; exists x2 ; exists x3.

Tactic Notation "exist" uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) :=
  exists x1 ; exists x2 ; exists x3 ; exists x4.

Tactic Notation "exist" uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) uconstr(x5) :=
  exists x1 ; exists x2 ; exists x3 ; exists x4 ; exists x5.

(****************************************************************************)
(* Alignment automation tactics. *)
(****************************************************************************)

(****************************************************************************)
(* For the ε operator *)
(****************************************************************************)

(* The definition of an HOL-Light function that is recursively defined
on some inductive type usually looks like:

  [ε (fun g => forall uv, P (g uv)) uv0]

  where P does not depend on uv (unused variable). *)

(* [gobble f uv] replaces the occurrences of [f uv] by a new symbol
named [f] too and removes [uv] from the context, assuming that [f uv]
does not actually depends on [uv]. *)
Ltac gobble f uv :=
  let g := fresh in
  set (g := f uv) in * ;
  clearbody g ; simpl in g ;
  clear f uv ; rename g into f.

(* From a goal of the form [a = ε (fun a' => forall uv, P (a' uv)) uv0],
align_ε generates two subgoals [P a] and [forall x, P a -> P x -> a = x]. *)
Ltac align_ε :=
  let rec aux :=
    lazymatch goal with
    | |- _ ?x = ε _ ?x => apply (f_equal (fun f => f x)) ; aux
    | |- ?a = ε _ ?r =>
        (* Replace the goal by (fun _ => a = ε ?P) *)
        apply (f_equal (fun g => g r) (x := fun _ => a)) ;
        aux ;
        [ intros _
        | let a' := fresh in
          let uv := fresh in
          let H' := fresh in
          let H := fresh in
          intros a' H H' ; ext 1=> uv ;
          specialize (H uv) ; (* As [P] starts with [forall uv] *)
          specialize (H' uv) ;
          simpl ((fun _ => a) uv) in * ; (* Simplifies to [a] so that [uv] only appears in [a' uv] *)
          gobble a' uv ;
          revert a' H H' (* Revert [a'], [P a] and [P a'] to reuse them in other tactics *)
        ]
    | |- ?a = ε ?P => apply align_ε (* Replaces the goal [a = ε P] with two goals [P a] and
                                       [forall x, P a => P x => x = a]. *)
    end
  in aux.

(****************************************************************************)
(* For if ... then ... else ... *)
(****************************************************************************)

(* The following are useful tools to work with COND :
   - Tactic if_triv replaces [if P then x else y] in the goal with either x or y
     assuming P or ~P is derivable with easy.
   - Tactic if_intro transforms a goal [P (if Q then x else y)]
     into two goals [Q -> P x] and [~Q -> P y] and
     simplifies all other [if Q then x' else y'] even if x<>x' or y<>y'
   - Lemma if_elim destructs hypothesis [if P then Q else R]
     as if it were (P /\ Q) \/ (~P /\ R) *)

Lemma if_triv_True (A : Type') (P : Prop) (x y : A) : P -> (if P then x else y) = x.
Proof.
  by rewrite -{1}(is_True P) => -> ; exact (if_True _ _).
Qed.

Lemma if_triv_False (A : Type') (P : Prop) (x y : A) : ~P -> (if P then x else y) = y.
Proof.
  by rewrite -{1}(is_False P) => -> ; exact (if_False _ _).
Qed.

Tactic Notation "if_triv" "by" tactic(tac) :=
  rewrite/COND ;
  (rewrite if_triv_True ; last by tac) ||
  (rewrite if_triv_False ; last by tac) ||
  fail "no conditional term to simplify".

Tactic Notation "if_triv" := if_triv by idtac.

(* /1= in intro/rewrite pattern *)
Ltac ssrsimpl1 := repeat if_triv.

(* If needed, specify which P is trivial *)
Tactic Notation "if_triv" constr(P) :=
  rewrite/COND ;
  (rewrite (if_triv_True _ P) ; [auto | easy]) +
  (rewrite (if_triv_False _ P) ; [auto | easy]).

Tactic Notation "if_triv" "using" constr(H) :=
  rewrite/COND ; let H' := fresh in set (H' := H) ;
  (rewrite if_triv_True ; last by auto using H') ||
  (rewrite if_triv_False ; last by auto using H') ; clear H'.

Tactic Notation "if_triv" constr(P) "using" constr(H) :=
  rewrite/COND ; let H' := fresh in set (H' := H) ;
  (rewrite (if_triv_True _ P) ; last by auto using H') ||
  (rewrite (if_triv_False _ P) ; last by auto using H') ; clear H'.

Lemma if_intro (A : Type') (Q : Prop) (P : A -> Prop) (x y : A) :
  (Q -> P x) -> (~Q -> P y) -> P (if Q then x else y).
Proof. case (pselect Q)=> [? /1= + _ | ? /1= _]; exact. Qed.

(* applies if_intro then also clears all if with
   the same hypothesis *)

Ltac if_intro :=
  rewrite/COND ;
  let H := fresh in
  apply if_intro => H ;
  [ repeat rewrite (if_triv_True _ _ H)
  | repeat rewrite (if_triv_False _ _ H)] ;
  move : H.

(* /c` in intropattern, c for case. *)
Notation "c`" := (ltac:(if_intro)) (at level 0, only parsing).

Lemma if_elim (P Q R G : Prop) : (if P then Q else R) -> (P -> Q -> G) -> (~ P -> R -> G) -> G.
Proof.
  by case (pselect P) => H /1= ; auto.
Qed.

(****************************************************************************)
(* For partial functions *)
(****************************************************************************)

(* Whenever functions defined in HOL-Light are only defined in some specific cases
   with ε, it can be defined in Rocq with an if then else, to have a meaningful value
   for these specific cases and default to the default ε-chosen function's
   value elsewhere. For example, functions defined on finite sets.

   align_ε_if works similarly to align_ε' in this case, with restraining
   uniqueness to the relevant cases for the function *)

Lemma align_ε_if1 {A B : Type'}
  (Q : A -> Prop) (f : A -> B) (P : (A -> B) -> Prop) :
  P f ->
  (forall f', P f -> P f' -> forall x, Q x -> f x = f' x) ->
  forall x, (if Q x then f x else ε P x) = ε P x.
Proof.
  by move=> Hf + x /c` ? // ; apply => // ; apply ε_spec ; exists f.
Qed.

Lemma align_ε_if2 {A B C : Type'}
  (Q : (A -> B -> Prop)) (f : A -> B -> C) (P : (A -> B -> C) -> Prop) :
  P f ->
  (forall f', P f -> P f' -> forall x y, Q x y -> f x y = f' x y) ->
  forall x y, (if Q x y then f x y else ε P x y) = ε P x y.
Proof.
  by move=> Hf Hunique x y /c` ; [apply Hunique ; [|apply ε_spec ; exists f]|].
Qed.

Lemma align_ε_if3 {A B C D : Type'}
  (Q : (A -> B -> C -> Prop)) (f : A -> B -> C -> D) (P : (A -> B -> C -> D) -> Prop) :
  P f ->
  (forall f', P f -> P f' -> forall x y z, Q x y z -> f x y z = f' x y z) ->
  forall x y z, (if Q x y z then f x y z else ε P x y z) = ε P x y z.
Proof.
  move=> Hf Hunique x y z /c` // ; apply Hunique => //.
  by apply ε_spec ; exists f.
Qed.

Arguments align_ε_if1 {_ _} _ _.
Arguments align_ε_if2 {_ _ _} _ _.
Arguments align_ε_if3 {_ _ _ _} _ _.

Ltac align_ε_if :=
  let rec aux :=
    lazymatch goal with
    | |- ?f = ε _ ?uv => generalize uv ; aux ;
          [ intros _
          | let f' := fresh in
            let uv := fresh in
            let Hf := fresh in
            let Hf' := fresh in
            let x := fresh "x" in
            let y := fresh "y" in
            let HP := fresh in
            try intros f' Hf Hf' uv x y HP ; try intros f' Hf Hf' uv x HP ;
            specialize (Hf uv) ;
            specialize (Hf' uv) ;
            simpl (_ uv) in * ;
            gobble f' uv ;
            revert HP ; try revert y ; revert f' Hf Hf' x ]
    | |- _ = ε _ => funext ; (* helping with pattern matching by
                                universally quantifying on the arguments *)
      lazymatch goal with
      | |- forall x, (if `[<?P>] then ?f else _) = _ =>
             apply (align_ε_if1 (fun x => P) (fun x => f))
      | |- forall x y, (if `[<?P>] then ?f else _) = _ =>
             apply (align_ε_if2 (fun x y => P) (fun x y => f))
      | |- forall x y z, (if `[<?P>] then ?f else _) = _ =>
             apply (align_ε_if3 (fun x y z => P) (fun x y z => f)) end
    | |- forall uv, _ = ε _ uv => intro uv ; try funext ; revert uv ;
      lazymatch goal with
      | |- forall x, (if `[<?P>] then ?f else _) = _ =>
             apply (align_ε_if1 (fun x => P) (fun x => f))
      | |- forall x y, (if `[<?P>] then ?f else _) = _ =>
             apply (align_ε_if2 (fun x y => P) (fun x y => f))
      | |- forall x y z, (if `[<?P>] then ?f else _) = _ =>
             apply (align_ε_if3 (fun x y z => P) (fun x y z => f)) end end
  in aux.

(****************************************************************************)
(* For inductive propositions. *)
(****************************************************************************)

Tactic Notation (at level 0) "breakgoal" "by" tactic(solvetac) :=
  let rec body := match goal with
  | |- _ \/ _ => left + right ; body (* Try both *)
  | |- _ /\ _ => split ; body
  | |- exists _,_ => eexists ; body (* The witness should be obvious *)
  | |- _ = _ => reflexivity
  | |- _ => first [by eauto | by solvetac] end
  in body. (* if solvetac cannot do the job, it fails to branch back. *)

Ltac breakgoal := breakgoal by idtac.

(* simply decomposing each hypothesis that we might encounter,
   a lot faster than going brutally with firstorder *)
Ltac full_destruct := repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  | H : exists x, _ |- _ => destruct H
  | H : _ \/ _ |- _ => destruct H end.

Ltac blindrewrite := repeat match goal with H : _ |- _ => rewrite H end.

(* Tactic to clear variables not appearing anywhere, including hypotheses. *)

Ltac clearall := repeat match goal with useless : _ |- _ => clear useless end.

(* In HOL_Light, an inductive defintion is top-down :
   if [Case_i x1 ... xn : Hyps_i x1 ... xn -> P (f_i x1 ... xn)] for 1 <= i <= k
   are the constructors / rules of P, then :
   [P x = forall P', (forall x', Case_1' x' \/ ... \/ Case_k' x' -> P' x') -> P' x]
   where [Case_i' x' := exists x1 ... xn, f_i x1 ... xn = x' /\ Hyps_i x1 ... xn]

   Let P_h x := forall P', H' -> P' x' denote the HOL_Light definition of P
   and P_r the Rocq Inductive definition.
   *)

Ltac intros_namelast name :=
  let tac_with_currentname x := intro x ; tryif intros_namelast name
                                then idtac else rename x into name
  in
  let check_is_not_complicatename y :=
    assert_succeeds (intro y ; assert (complicatename : True))
  in
  match goal with
  | |- forall complicatename, _ => check_is_not_complicatename complicatename ;
                                   tac_with_currentname complicatename
  | |- _ -> _ => let H := fresh in tac_with_currentname H
  | |- _ => let x := fresh "x" in tac_with_currentname x end.

Ltac extall := repeat (let x := fresh "x" in apply funext=>x).

Ltac ind_align :=
  let H := fresh in extall ; ext => H ;
  (* Prove equality by double implication *)
  [ let P' := fresh "P'" in
    let H' := fresh "H'" in (* Proving [P_r x -> P_h x] *)
    intros P' H' ; induction H ; apply H' ;
    (* Induction on hypothesis [P_r x] replaces [x] according to Case_i for each i.
       to prove [P' x] we apply [H']. *)
    try breakgoal (* Trying to automatically find and solve Case_i'.
                     The Hyps_i are in the context. *)
  | (* Proving [P_h x -> P_r x] *)
    apply H ; (* Replaces goal [P_r x] with [H'] *)
    clearall ; (* H' talks about fresh variables *)
    intros_namelast H ;
    full_destruct ; (* Destructing H results in one goal per case, and separates the hypotheses *)
    blindrewrite ;  (* not much to do, each clause should be proved with a rule,
                       we just try to rewrite [a = f x1 ... xn] if it exists *)
    try (econstructor ; breakgoal) ; auto ].

(*****************************************************************************)
(* For function inverses *)
(*****************************************************************************)

Definition finv [A B : Type'] (f : A -> B) : B -> A := fun y => ε (fun x => f x = y).

(* finv can define the inverse of a type embedding, the following will be useful to
   prove isomorphisms *)

Lemma finv_inv_l [A B : Type'] (f : A -> B) (x : A) :
  (forall x0 x1 : A, f x0 = f x1 -> x0 = x1) -> finv f (f x) = x.
Proof.
  intro H. apply H. apply (ε_spec (P := fun x' => f x' = f x)). now exists x. 
Qed.

Ltac finv_inv_l := intros ; apply finv_inv_l ; clearall.

Lemma finv_inv_r [A B : Type'] (f : A -> B) : forall (P : B -> Prop) (y : B),
  (P y -> exists x, f x = y) -> ((exists x, f x = y) -> P y) -> P y = (f (finv f y) = y).
Proof.
  intros P y i1 i2. transitivity (exists x, f x = y).
  - exact (prop_ext i1 i2).
  - apply prop_ext;intro H.
    + exact (ε_spec H).
    + now exists (finv f y).
Qed.

(*****************************************************************************)
(* For inductive types *)
(*****************************************************************************)

Definition FCONS {A : Type} (a : A) (f: nat -> A) (n : nat) : A := match n with
  | 0 => a
  | n.+1 => f n end.

Lemma FCONS_inj [A : Type'] (a a' : A) f f' : (FCONS a f = FCONS a' f') = (a = a' /\ f = f').
Proof.
  ext => [FCONS_eq | [? eqS] [|n]] //= ; last by rewrite eqS.
  have {}FCONS_eq: forall n, FCONS a f n = FCONS a' f' n by rewrite FCONS_eq.
  split ; [exact: (FCONS_eq 0) | ext=> n ; exact: (FCONS_eq n.+1)].
Qed.

(* In this section, we suppose that we wish to align a HOL_Light inductive definition to a
   Rocq one. In simple cases (Same ammount of constructors with same arguments,
   Rocq generates the correct inductive principle, currently no mutually defined types
   (check coq-hol-light-Logic for an example of alignment of 2 mutually defined types)), the following 
   tactics allow to fully automate the proofs. *)

(* Let this also serve as a tutorial on how to map a HOL Light type T in general.

   - Once file.ml has been translated with hol2dk,
     search for "Axiom" in file_terms.v. You should find axioms,
     usually named _mk_T and _dest_T, with type recspace A -> T and
     T -> recspace A respectively for some A.

   - In the mappings file, first define the correct Rocq inductive type if it does not exist,
     then define _dest_T yourself recursively.
     > To know how you should define it, look at the definitions after axioms _mk_T and _dest_t
       in T_terms.v. They should look like :
       "Definition _123456 := fun (...) => _mk_T [...]" where _123456 (for example) is simply a temporary name
       for a constructor C, replaced soon after with "Definition C := _123456".
       [_dest_T (C (...))] should then have value [...].

    - You can then define _mk_t := finv _dest_t.

    - Then, in file_types.v, you should find two axioms named axiom_... stating
      that _dest_T and _mk_t are the inverse of each other. Prove them in the mappings file using the following
      tactics :
      *)

(* _dest_inj proves that _dest is injective by double induction.
   Can fail when the induction principle isn't suited.
   Only works for non mutually defined types. *)

Ltac _dest_inj_inductive :=
  match goal with |- forall x x', _ => let e := fresh in
    induction x ; induction x' ; simpl ; intro e ;
    (* e is of the form "CONSTR n a f = CONSTR n' a' f'", so inversion
       gives hypotheses n=n' , a=a' and f=f'. *)
    inversion e ; auto ;
    repeat rewrite -> FCONS_inj in * ; (* f and f' should represent lists of recursive calls
                                       so we transform their equality into equality of
                                       each recursive call (so of the form
                                       "et : _dest_T t = _dest_T t'") *)
    f_equal ;
    match goal with IH : _ |- _ => now apply IH (* trying to apply the
                                                   induction hypothesis blindly to prove 
                                                   t = t' from et *)
    end end.

(* As long as _mk_T is defined as finv _dest_T, _mk_dest_inductive will
   transform a goal of the form [forall x, (_mk_T (_dest_T x)) = x] into
   a goal stating injectivity of _dest_T thanks to finv_inv_l, then try to apply _dest_inj. *)

Ltac _mk_dest_inductive := finv_inv_l ; try _dest_inj_inductive.

(* Try to solve a goal of the form [forall r, P r = (_dest_T (_mk_T r)) = r)]
   for P defining the subset of recspace A with which the defined type(s) are
   isomorphism.
   Thanks to finv_inv_r, the goal can be replaced by [P r <-> exists x, _dest_T x = r]
   as long as _mk_T is defined as finv _dest_T.

   P is an inductive definition so the following is very similar to ind_align,
   except that [exists x, _dest_T x = r] is not inductive so we are rather inducting on x.
   Compared to ind_align, we do not have access to the constructor tactic to automatically
   find the correct constructor so it currently needs to be done by hand. *)

Ltac blindrewrite_rev := repeat match goal with H : _ |- _ => rewrite -H end.

Ltac _dest_mk_inductive :=
  let H := fresh in 
  let x := fresh "x" in
  let P := fresh "P" in
  intros ; apply finv_inv_r ;
  [ intro H ; apply H ;
    clear H ; intros x H ;
    full_destruct ; rewrite H ;
    clear H ; simpl in * ;
    try (unshelve eexists ; [econstructor | blindrewrite_rev ; reflexivity])
  | (* simply inducting over [x] such that [_dest_ x = r]. *)
    intros (x,<-) P ;
    induction x ;
    intros H ; apply H ; try breakgoal ].

(* - Finally, prove the definition of all constructors ( the lemmas _123456_def and C_def
     right under their definition in T_terms.v, replacing them with the new definition ).
     constr_align automatically proves _123456_def (afterwards, C_def is just reflexivity) : *)

Ltac constr_align H := (* Takes as argument the lemma [forall x, _mk_T (_dest_T x) = x].
                          Requires explicit type arguments. *)
  extall ; match goal with |- ?x = _ => exact (esym (H x)) end.


(*****************************************************************************)
(* For Record-like types *)
(*****************************************************************************)

(* Record-like types in HOL Light are simply subtypes of the form
   {x : T1 * T2 * ... * Tn | (P1 /\ P2 /\ ... /\ Pn') x}
   where the Pi and Ti are the Prop and non-Prop fields respectively. *)

(* The goal of this section is to automate the alignment of this type
   with the corresponding record in Rocq. *)

(* Note that the Ti cannot depend on each other, since HOL Light cannot define
   dependant pairs. *)

(* let r be an element of the record Type, _dest_T r should simply be the tuple
   of all non-Prop fields of r. We made the choice that _mk_T should be finv _dest_T
   but here other options were available compared to inductive types. *)

(* Revert everything that H does not depend on.
   ( actually also keeps everything that has the same type as H,
     H is supposed to be a proposition ) *)
Ltac revert_keep H :=
  match type of H with ?T =>
    repeat match goal with
    | x : _ |- _ => assert_fails typecheck T x ; revert x end end.

(* Apply proof_irrelevance to all propositionnal fields,
   to prove injectivity of _dest_T. *)

(* To do that we first need to rewrite equalities to remove the difference in
   dependant typing of the fields. *)

Ltac instance_uniqueness := let instance1 := fresh in
  let instance2 := fresh in
  let eq := fresh in
  intros instance1 instance2 eq ;
  match type of eq with
  | ?f _ = _ => unfold f in eq
  | ?f _ _ = _ => unfold f in eq
  | ?f _ _ _ = _ => unfold f in eq
  | ?f _ _ _ _ = _ => unfold f in eq end ;
  destruct instance1,instance2 ; simpl in eq ;
  revert_keep eq ; inversion_clear eq ;
  intros ; f_equal ; apply proof_irrelevance.

(* Combine it with finv_inv_l. *)

Ltac _mk_dest_record := finv_inv_l ; instance_uniqueness.

(* tries proving [H1 /\ ... /\ Hn -> P] with hypothesis [H1 -> ... -> Hn -> P]
   or the converse. *)

Ltac and_arrow := try (move=>* ; full_destruct ; match goal with
  | Hyp : _ |- _ => exact: Hyp end).

(* finv_inv_r gives us two goals, we can only fully automate one :
   [exists r' : T, _dest r' = r -> (P1 /\ P2 /\ ... /\ Pn') r]
   which is simply done by rewriting the hypothesis, and destructing r'
   to get its fields which should contain the required proof.
   The tactic tac can provide a way to simplify hol light definitions
   assuming they are already simplified in the record to align it with *)

Tactic Notation "_dest_mk_record" "by" tactic(tac) "with" uconstr(dest) :=
  intros ; apply finv_inv_r with (f := dest) ;
  [ try match goal with
    | |- ?P _ -> _ => unfold P
    | |- ?P _ _ -> _ => unfold P
    | |- ?P _ _ _ -> _ => unfold P
    | |- ?P _ _ _ _ -> _ => unfold P end ;
    tac ; intros ; full_destruct
  | try match goal with
    | |- (exists _, ?f _ = _) -> _ => unfold f
    | |- (exists _, ?f _ _ = _) -> _ => unfold f
    | |- (exists _, ?f _ _ _ = _) -> _ => unfold f
    | |- (exists _, ?f _ _ _ _  = _) -> _ => unfold f end ; 
    let r := fresh in
    intros [r <-] ; clearall ; destruct r ;
    try match goal with
    | |- ?P _ => unfold P
    | |- ?P _ _ => unfold P
    | |- ?P _ _ _ => unfold P
    | |- ?P _ _ _ _ => unfold P end ;
    tac ; repeat (and_arrow ; split) ; and_arrow ; simpl ].

Tactic Notation "_dest_mk_record" "by" tactic(tac) := _dest_mk_record by tac with _.
Tactic Notation "_dest_mk_record" "with" uconstr(dest) := _dest_mk_record by idtac with dest.
Tactic Notation "_dest_mk_record" := _dest_mk_record with _.

(* The other goal is the opposite direction,
   for which it is required to provide an instance of the Rocq record,
   which is sadly not automatable with Rocq alone.
   The following tactic automates everything but require as input
   a uconstr of the form {| F1 := fst r ; ... ; Fn := snd (... (snd r)) |},
   explicitly giving all non-Prop fields.  *)

Ltac destruct_tuple r := let b := fresh in
  destruct r as (?a,b) ; try destruct_tuple b.

Tactic Notation "record_exists" uconstr(uwitness) :=
  unshelve eexists uwitness ;
  and_arrow ;
  try match goal with |- _ = ?r => now try destruct_tuple r end.

(* In case the Prop fields are not the same as the HOL_Light ones,
   we will be left with proving their double implication. *)

(****************************************************************************)
(* For total recursive functions *)
(****************************************************************************)

(* make sure to not split too far *)
Ltac split_all := repeat match goal with |- _ /\ _ => split end.

(* total_alignk for k between 1 and 3 replaces a goal of the form 
     f = ε P uv with two goals PO f and PS f whenever P = PO /\ PS
   totally defines the function by peano recursion on the kth argument. *)
(* These tactics only work for functions with 3 or less arguments. *)

(* Tries to prove a goal [f = ε P uv] where f is recursively defined. *)
Ltac total_align1_general inductiontac solvetac :=
  align_ε ; (* At this state, we have two goals : [P f] and [P f -> P f' -> f = f'].
                We now assume that [P f] is of the form
                [Q1 f C1 = ... /\ Q2 f C2 = ... /\ ... /\ Qn f Cn = ...]
                where the Ci are the constructors of the type and
                the Qi are universal quantifications over other arguments and subterms of the Ci. *)
  [ split_all
  | let f' := fresh "f'" in
    let r := fresh in
    let H := fresh in
    let H' := fresh in
    intros f' H H' ; ext 1 => r ; inductiontac r ; extall ;
    solvetac (* Depending on the need, can be a basic tactic ending with auto or
                one that must succeed, or a more complex one for specific types *)
    ].

(* The following only change which argument inductiontac is applied on. *)

Ltac total_align2_general inductiontac solvetac :=
  align_ε ; [ split_all
  | let f' := fresh "f'" in
    let r := fresh in
    let a := fresh "x" in
    let H := fresh in
    let H' := fresh in
    intros f' H H' ; ext 2=> + r ; inductiontac r => a ; extall ; solvetac ].

Ltac total_align3_general inductiontac solvetac :=
  align_ε ; [ split_all
  | let f' := fresh "f'" in
    let r := fresh in
    let a := fresh "x" in
    let b := fresh "x" in
    let H := fresh in
    let H' := fresh in
    intros f' H H' ; ext 3 => + + r ; inductiontac r => a b ; extall ; solvetac ].

Ltac total_align4_general inductiontac solvetac :=
  align_ε ; [ split_all
  | let f' := fresh "f'" in
    let r := fresh in
    let a := fresh "x" in
    let b := fresh "x" in
    let c := fresh "x" in
    let H := fresh in
    let H' := fresh in
    intros f' H H' ; ext 4 => + + + r ;
    inductiontac r => a b c ; extall ; solvetac ].

Ltac total_align5_general inductiontac solvetac :=
  align_ε ; [ split_all
  | let f' := fresh "f'" in
    let r := fresh in
    let a := fresh "x" in
    let b := fresh "x" in
    let c := fresh "x" in
    let d := fresh "x" in
    let H := fresh in
    let H' := fresh in
    intros f' H H' ; ext 5 => + + + + r ;
    inductiontac r ; extall ; solvetac ].

Ltac total_align_general inductiontac solvetac :=
  let force_solvetac := solve [solvetac] in
  first
  [ total_align1_general inductiontac force_solvetac
  | total_align2_general inductiontac force_solvetac
  | total_align3_general inductiontac force_solvetac
  | total_align4_general inductiontac force_solvetac
  | total_align5_general inductiontac force_solvetac ].

Ltac solve_total_align := try full_destruct ;
  blindrewrite ; try reflexivity.

(* With the correct induction principle, we have one case per clause,
   we can replace [f] and [f']'s values with the corresponding
   clause in [P] (that we have split). By also rewriting all induction hypotheses,
   the goal should become a reflexive equality.

   For more complex types, it is possible to try and adapt this tactic
   to specify how the induction hypothesis should be used.
   See term_align in coq-hol-light-Logic1 for an example with lists as recursive arguments,
   using the following solving tactic *)

Definition ALL T (P : T -> Prop) s : Prop := all P s.

Lemma map_ALLE (A B : Type) (f g : A -> B) (s : seq A) :
  ALL (fun x => f x = g x) s -> map f s = map g s.
Proof.
  by elim:s=> //= ? ? IHs; rewrite/ALL -andP** asboolE=> -[? /IHs ?]; f_equal.
Qed.

Ltac solve_total_align_with_lists :=
  try full_destruct ; blindrewrite ; auto ;
  repeat (f_equal ; try now apply map_ALLE).

Ltac use_induction r := induction r.
Ltac total_align1 := total_align1_general use_induction solve_total_align.
Ltac total_align2 := total_align2_general use_induction solve_total_align.
Ltac total_align3 := total_align3_general use_induction solve_total_align.
Ltac total_align4 := total_align4_general use_induction solve_total_align.
Ltac total_align5 := total_align5_general use_induction solve_total_align.
Ltac total_align := total_align_general use_induction solve_total_align.

(* In the rare case where solve_total_align would not be sufficient in proving one of the goals,
   one should use total_aligni where i is the variable to induct on. Otherwise, simply use total_align. *)

(****************************************************************************)
(* For partial recursive functions. *)
(****************************************************************************)

(* It is possible in HOL_Light to define a function
   recursively while not defining it for some constructors.
   The function will then have its value on these constructors chosen
   by the ε operator. In that case it is necessary to define the rocq function
   to be trivially equal to the HOL-Light one on each of these constructors.

   The following tactics allow to align such a partially defined function
   when provided with a predicate Q representing the cases where equality has to
   be trivial.

   Q should be defined inductively so as to be able to automatically discharge
   the goal [Q x -> _=_] via inversion. *)

(* First, the following lemmas mimick align_ε in the case where equality has to
   be trivial on Q. They can be used for any partial function, not just recursive
   (for example, a function defined through "new_specification") *)

Unset Implicit Arguments. 
Lemma partial_align_case1 {U A B : Type'} {uv0 : U} {x : A}
  (Q : A -> Prop) (f : U -> A -> B) (P : (U -> A -> B) -> Prop) :
  P f -> (forall x', Q x' -> f uv0 x' = ε P uv0 x') ->
  (forall f' uv x', P f ->  P f' -> (forall x'', Q x'' -> f uv x'' = f' uv x'') ->
  f uv x' = f' uv x') -> f uv0 x = ε P uv0 x.
Proof.
  intros Hf Htriv Hunique.
  apply Hunique;auto. apply ε_spec. now exists f.
Qed.

Lemma partial_align_case2 {U A B C : Type'} {uv0 : U} {x : B} {y : A}
  (Q : A -> Prop) (f : U -> B -> A -> C) (P : (U -> B -> A -> C) -> Prop) :
  P f -> (forall x' y', Q y' -> f uv0 x' y' = ε P uv0 x' y') ->
  (forall f' uv x' y', P f ->  P f' ->
  (forall x'' y'', Q y'' -> f uv x'' y'' = f' uv x'' y'') ->
  f uv x' y' = f' uv x' y') -> f uv0 x y = ε P uv0 x y.
Proof.
  intros Hf Htriv Hunique.
  apply Hunique;auto. apply ε_spec. now exists f.
Qed.

Lemma partial_align_case3 {U A B C D : Type'} {uv0 : U} {x : B} {y : C} {z : A}
  (Q : A -> Prop) (f : U -> B -> C -> A -> D) (P : (U -> B -> C -> A -> D) -> Prop) :
  P f -> (forall x' y' z', Q z' -> f uv0 x' y' z' = ε P uv0 x' y' z') ->
  (forall f' uv x' y' z', P f ->  P f' ->
  (forall x'' y'' z'', Q z'' -> f uv x'' y'' z'' = f' uv x'' y'' z'') ->
  f uv x' y' z' = f' uv x' y' z') -> f uv0 x y z = ε P uv0 x y z.
Proof.
  intros Hf Htriv Hunique.
  apply Hunique;auto. apply ε_spec. now exists f.
Qed.
Set Implicit Arguments.

(* The following ressembles total_align but also tries to automatically get rid of every cases that
   are in Q. It is designed for recursive functions only. *)
Ltac partial_align1_general Q inductiontac solvetac :=
  let f' := fresh "f'" in 
  let uv := fresh "uv" in
  let H := fresh in
  let H' := fresh "H'" in
  let Htriv := fresh "Htriv" in
  match goal with
  |- ?f ?x = ε _ _ ?x => apply (partial_align_case1 Q (fun _ => f)) ; (* replace f with (fun _ => f) uv *)
    clear x ; [ move=> _; split_all
    | intro x ; now inversion 1 (* Additional goal
                                   [forall x, Q x -> f uv x = ε uv x] compared to
                                   total_align, if Q is inductive and the equality
                                   is trivial, inversion should do the job. *)
    | intros f' uv x H H' Htriv ; extall ;
      specialize (H uv) ;
      specialize (H' uv) ;
      simpl (_ uv) in * ;
      gobble f' uv ;
      inductiontac x ; (try now rewrite Htriv ; constructor) ; (* automatically takes care of cases
                                                                        in Q. *)
      clear Htriv ; (* We do not want to be able to rewrite Htriv outside of cases in Q. *)
      solvetac ] end.

Ltac partial_align2_general Q inductiontac solvetac :=
  let f' := fresh "f'" in 
  let uv := fresh "uv" in
  let H := fresh in
  let H' := fresh "H'" in
  let Htriv := fresh "Htriv" in
  match goal with
  |- ?f ?y ?x = ε _ _ ?y ?x => apply (partial_align_case2 Q (fun _ => f)) ;
    clear y x ; [ move=> _; split_all
    | intros y x ; now inversion 1
    | intros f' uv y x H H' Htriv ; extall ;
      specialize (H uv) ;
      specialize (H' uv) ;
      simpl (_ uv) in * ;
      gobble f' uv ;
      inductiontac x ; (try now rewrite Htriv ; constructor) ;
      clear Htriv ; solvetac ] end.

Ltac partial_align3_general Q inductiontac solvetac :=
  let f' := fresh "f'" in 
  let uv := fresh "uv" in
  let H := fresh in
  let H' := fresh "H'" in
  let Htriv := fresh "Htriv" in
  match goal with
  |- ?f ?y ?z ?x = ε _ _ ?y ?z ?x => apply (partial_align_case3 Q (fun _ => f)) ;
    clear y z x ; [ move=> _; split_all
    | intros y z x ; now inversion 1
    | intros f' uv y z x H H' Htriv ; extall ;
      specialize (H uv) ;
      specialize (H' uv) ;
      simpl (_ uv) in * ;
      gobble f' uv ;
      induction x ; (try now rewrite Htriv ; constructor) ;
      clear Htriv ; solvetac] end.

Ltac partial_align_general Q inductiontac solvetac :=
  let x := fresh "x" in
  let y := fresh "y" in
  let z := fresh "z" in
  ext 1 => x ; partial_align1_general Q inductiontac solvetac +
  (ext 1 => y ; partial_align2_general Q inductiontac solvetac +
  (ext 1 => z ; partial_align3_general Q inductiontac solvetac)).

Ltac partial_align1 Q := partial_align1_general Q use_induction solve_total_align.
Ltac partial_align2 Q := partial_align2_general Q use_induction solve_total_align.
Ltac partial_align3 Q := partial_align3_general Q use_induction solve_total_align.
Ltac partial_align Q := partial_align_general Q use_induction solve_total_align.

(****************************************************************************)
(* Miscellaneous. *)
(****************************************************************************)

Lemma GABS_def {A : Type'} : (@ε A) = (fun P : A -> Prop => @ε A P).
Proof. exact erefl. Qed.

Lemma GEQ_def {A : Type'} : (@eq A) = (fun a : A => fun b : A => a = b).
Proof. exact erefl. Qed.

Lemma _UNGUARDED_PATTERN_def : and = (fun p : Prop => fun r : Prop => p /\ r).
Proof. exact erefl. Qed.

Lemma _FALSITY__def : False = False.
Proof. exact erefl. Qed.

Lemma hashek_def : True = True.
Proof. exact erefl. Qed.

Definition cancel2 (A B : Type) (f : A -> B) (g : B -> A) := cancel g f /\ cancel f g.

Lemma ISO_def {A B : Type'} : (@cancel2 A B) = (fun _17569 : A -> B => fun _17570 : B -> A => (forall x : B, (_17569 (_17570 x)) = x) /\ (forall y : A, (_17570 (_17569 y)) = y)).
Proof. by funext. Qed.

(*****************************************************************************)
(* Alignment of quotients. *)
(*****************************************************************************)

Section Quotient.

  Variables (A : Type') (R : A -> A -> Prop).

  Definition is_eq_class X := exists a, X = R a.

  Definition class_of x := R x.

  Lemma is_eq_class_of x : is_eq_class (class_of x).
  Proof. exists x. reflexivity. Qed.

  Lemma non_empty : is_eq_class (class_of point).
  Proof. exists point. reflexivity. Qed.

  Definition quotient := subtype non_empty.

  Definition mk_quotient : (A -> Prop) -> quotient := mk non_empty.
  Definition dest_quotient : quotient -> (A -> Prop) := dest non_empty.

  Lemma mk_dest_quotient : forall x, mk_quotient (dest_quotient x) = x.
  Proof. exact (mk_dest non_empty). Qed.

  Lemma dest_mk_aux_quotient : forall x, is_eq_class x -> (dest_quotient (mk_quotient x) = x).
  Proof. exact (dest_mk_aux non_empty). Qed.

  Lemma dest_mk_quotient : forall x, is_eq_class x = (dest_quotient (mk_quotient x) = x).
  Proof. exact (dest_mk non_empty). Qed.

  Definition elt_of : quotient -> A := fun x => ε (dest_quotient x).

  Variable R_refl : forall a, R a a.

  Lemma eq_elt_of a : R a (ε (R a)).
  Proof. apply ε_spec. exists a. apply R_refl. Qed.

  Lemma dest_quotient_elt_of x : dest_quotient x (elt_of x).
  Proof.
    unfold elt_of, dest_quotient, dest. destruct x as [c [a h]]; simpl. subst c.
    apply ε_spec. exists a. apply R_refl.
  Qed.

  Variable R_sym : forall x y, R x y -> R y x.
  Variable R_trans : forall x y z, R x y -> R y z -> R x z.

  Lemma dest_quotient_elim x y : dest_quotient x y -> R (elt_of x) y.
  Proof.
    unfold elt_of, dest_quotient, dest. destruct x as [c [a h]]; simpl. subst c.
    intro h. apply R_trans with a. apply R_sym. apply eq_elt_of. exact h.
  Qed.

  Lemma eq_class_intro_elt (x y: quotient) : R (elt_of x) (elt_of y) -> x = y.
  Proof.
    destruct x as [c [x h]]. destruct y as [d [y i]]. unfold elt_of. simpl.
    intro r. generalize (ex_intro (fun a : A => c = R a) x h)
      (ex_intro (fun a : A => d = R a) y i).
    have -> : c = d ; last by move=>* ; f_equal ; exact: proof_irrelevance.
    rewrite h i. ext=> z ?.
    - apply: (R_trans (eq_elt_of y)).
      rewrite i in r. apply (R_trans (R_sym r)).
      rewrite h. by apply: (R_trans (R_sym (eq_elt_of x))).
    - apply: (R_trans (eq_elt_of x)).
      rewrite h in r. apply (R_trans r).
      rewrite i. by apply: (R_trans (R_sym (eq_elt_of y))).
  Qed.

  Lemma eq_class_intro (x y: A) : R x y -> R x = R y.
  Proof.
    move=> xy /` a h.
    apply R_trans with x. apply R_sym. exact xy. exact h.
    apply R_trans with y. exact xy. exact h.
  Qed.

  Lemma eq_class_elim (x y: A) : R x = R y -> R x y.
  Proof. by move=>->. Qed.

  Lemma mk_quotient_elt_of x : mk_quotient (R (elt_of x)) = x.
  Proof.
    apply eq_class_intro_elt. set (a := elt_of x). unfold elt_of.
    rewrite dest_mk_aux_quotient. apply R_sym. apply eq_elt_of.
    exists a. reflexivity.
  Qed.

End Quotient.
Arguments dest_quotient [_] _.
Arguments mk_dest_quotient [_] _.
Arguments dest_mk_aux_quotient [_] _ _ _.
