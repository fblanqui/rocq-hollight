Require Import Stdlib.NArith.BinNat Stdlib.Reals.Reals mathcomp.classical.classical_sets mathcomp.classical.cardinality mathcomp.boot.choice mathcomp.boot.ssrbool HOLLight.Real_With_N.mappings HOLLight.Unif.mappings HOLLight.Logic.mappings.
Definition o {A B C : Type'} : (B -> C) -> (A -> B) -> A -> C := fun f : B -> C => fun g : A -> B => fun x : A => f (g x).
Lemma o_def {A B C : Type'} : (@o A B C) = (fun f : B -> C => fun g : A -> B => fun x : A => f (g x)).
Proof. exact (REFL (@o A B C)). Qed.
Definition I {A : Type'} : A -> A := fun x : A => x.
Lemma I_def {A : Type'} : (@I A) = (fun x : A => x).
Proof. exact (REFL (@I A)). Qed.
Definition _SEQPATTERN {A B : Type'} : (A -> B -> Prop) -> (A -> B -> Prop) -> A -> B -> Prop := fun r : A -> B -> Prop => fun s : A -> B -> Prop => fun x : A => @COND (B -> Prop) (exists y : B, r x y) (r x) (s x).
Lemma _SEQPATTERN_def {A B : Type'} : (@_SEQPATTERN A B) = (fun r : A -> B -> Prop => fun s : A -> B -> Prop => fun x : A => @COND (B -> Prop) (exists y : B, r x y) (r x) (s x)).
Proof. exact (REFL (@_SEQPATTERN A B)). Qed.
Definition _GUARDED_PATTERN : Prop -> Prop -> Prop -> Prop := fun p : Prop => fun g : Prop => fun r : Prop => p /\ (g /\ r).
Lemma _GUARDED_PATTERN_def : _GUARDED_PATTERN = (fun p : Prop => fun g : Prop => fun r : Prop => p /\ (g /\ r)).
Proof. exact (REFL _GUARDED_PATTERN). Qed.
Definition _MATCH {A B : Type'} : A -> (A -> B -> Prop) -> B := fun e : A => fun r : A -> B -> Prop => @COND B (@ex1 B (r e)) (@ε B (r e)) (@ε B (fun z : B => False)).
Lemma _MATCH_def {A B : Type'} : (@_MATCH A B) = (fun e : A => fun r : A -> B -> Prop => @COND B (@ex1 B (r e)) (@ε B (r e)) (@ε B (fun z : B => False))).
Proof. exact (REFL (@_MATCH A B)). Qed.
Definition _FUNCTION {A B : Type'} : (A -> B -> Prop) -> A -> B := fun r : A -> B -> Prop => fun x : A => @COND B (@ex1 B (r x)) (@ε B (r x)) (@ε B (fun z : B => False)).
Lemma _FUNCTION_def {A B : Type'} : (@_FUNCTION A B) = (fun r : A -> B -> Prop => fun x : A => @COND B (@ex1 B (r x)) (@ε B (r x)) (@ε B (fun z : B => False))).
Proof. exact (REFL (@_FUNCTION A B)). Qed.
Definition CURRY {A B C : Type'} : ((prod A B) -> C) -> A -> B -> C := fun _1283 : (prod A B) -> C => fun _1284 : A => fun _1285 : B => _1283 (@pair A B _1284 _1285).
Lemma CURRY_def {A B C : Type'} : (@CURRY A B C) = (fun _1283 : (prod A B) -> C => fun _1284 : A => fun _1285 : B => _1283 (@pair A B _1284 _1285)).
Proof. exact (REFL (@CURRY A B C)). Qed.
Definition UNCURRY {A B C : Type'} : (A -> B -> C) -> (prod A B) -> C := fun _1304 : A -> B -> C => fun _1305 : prod A B => _1304 (@fst A B _1305) (@snd A B _1305).
Lemma UNCURRY_def {A B C : Type'} : (@UNCURRY A B C) = (fun _1304 : A -> B -> C => fun _1305 : prod A B => _1304 (@fst A B _1305) (@snd A B _1305)).
Proof. exact (REFL (@UNCURRY A B C)). Qed.
Definition PASSOC {A B C D : Type'} : ((prod (prod A B) C) -> D) -> (prod A (prod B C)) -> D := fun _1321 : (prod (prod A B) C) -> D => fun _1322 : prod A (prod B C) => _1321 (@pair (prod A B) C (@pair A B (@fst A (prod B C) _1322) (@fst B C (@snd A (prod B C) _1322))) (@snd B C (@snd A (prod B C) _1322))).
Lemma PASSOC_def {A B C D : Type'} : (@PASSOC A B C D) = (fun _1321 : (prod (prod A B) C) -> D => fun _1322 : prod A (prod B C) => _1321 (@pair (prod A B) C (@pair A B (@fst A (prod B C) _1322) (@fst B C (@snd A (prod B C) _1322))) (@snd B C (@snd A (prod B C) _1322)))).
Proof. exact (REFL (@PASSOC A B C D)). Qed.
Definition minimal : (N -> Prop) -> N := fun _6536 : N -> Prop => @ε N (fun n : N => (_6536 n) /\ (forall m : N, (N.lt m n) -> ~ (_6536 m))).
Lemma minimal_def : minimal = (fun _6536 : N -> Prop => @ε N (fun n : N => (_6536 n) /\ (forall m : N, (N.lt m n) -> ~ (_6536 m)))).
Proof. exact (REFL minimal). Qed.
Definition FNIL {A : Type'} : N -> A := fun _17624 : N => @ε A (fun x : A => True).
Lemma FNIL_def {A : Type'} : (@FNIL A) = (fun _17624 : N => @ε A (fun x : A => True)).
Proof. exact (REFL (@FNIL A)). Qed.
Definition OUTL {A B : Type'} : (Datatypes.sum A B) -> A := @ε ((prod N (prod N (prod N N))) -> (Datatypes.sum A B) -> A) (fun OUTL' : (prod N (prod N (prod N N))) -> (Datatypes.sum A B) -> A => forall _17649 : prod N (prod N (prod N N)), forall x : A, (OUTL' _17649 (@inl A B x)) = x) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0))))))))))).
Lemma OUTL_def {A B : Type'} : (@OUTL A B) = (@ε ((prod N (prod N (prod N N))) -> (Datatypes.sum A B) -> A) (fun OUTL' : (prod N (prod N (prod N N))) -> (Datatypes.sum A B) -> A => forall _17649 : prod N (prod N (prod N N)), forall x : A, (OUTL' _17649 (@inl A B x)) = x) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))))))).
Proof. exact (REFL (@OUTL A B)). Qed.
Definition OUTR {A B : Type'} : (Datatypes.sum A B) -> B := @ε ((prod N (prod N (prod N N))) -> (Datatypes.sum A B) -> B) (fun OUTR' : (prod N (prod N (prod N N))) -> (Datatypes.sum A B) -> B => forall _17651 : prod N (prod N (prod N N)), forall y : B, (OUTR' _17651 (@inr A B y)) = y) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0))))))))))).
Lemma OUTR_def {A B : Type'} : (@OUTR A B) = (@ε ((prod N (prod N (prod N N))) -> (Datatypes.sum A B) -> B) (fun OUTR' : (prod N (prod N (prod N N))) -> (Datatypes.sum A B) -> B => forall _17651 : prod N (prod N (prod N N)), forall y : B, (OUTR' _17651 (@inr A B y)) = y) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))))))).
Proof. exact (REFL (@OUTR A B)). Qed.
Definition _22943 : Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Ascii.ascii := fun a0 : Prop => fun a1 : Prop => fun a2 : Prop => fun a3 : Prop => fun a4 : Prop => fun a5 : Prop => fun a6 : Prop => fun a7 : Prop => _mk_char ((fun a0' : Prop => fun a1' : Prop => fun a2' : Prop => fun a3' : Prop => fun a4' : Prop => fun a5' : Prop => fun a6' : Prop => fun a7' : Prop => @CONSTR (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))) (NUMERAL N0) (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))) a0' (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))) a1' (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))) a2' (@pair Prop (prod Prop (prod Prop (prod Prop Prop))) a3' (@pair Prop (prod Prop (prod Prop Prop)) a4' (@pair Prop (prod Prop Prop) a5' (@pair Prop Prop a6' a7'))))))) (fun n : N => @BOTTOM (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))))) a0 a1 a2 a3 a4 a5 a6 a7).
Lemma _22943_def : _22943 = (fun a0 : Prop => fun a1 : Prop => fun a2 : Prop => fun a3 : Prop => fun a4 : Prop => fun a5 : Prop => fun a6 : Prop => fun a7 : Prop => _mk_char ((fun a0' : Prop => fun a1' : Prop => fun a2' : Prop => fun a3' : Prop => fun a4' : Prop => fun a5' : Prop => fun a6' : Prop => fun a7' : Prop => @CONSTR (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))) (NUMERAL N0) (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))) a0' (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))) a1' (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))) a2' (@pair Prop (prod Prop (prod Prop (prod Prop Prop))) a3' (@pair Prop (prod Prop (prod Prop Prop)) a4' (@pair Prop (prod Prop Prop) a5' (@pair Prop Prop a6' a7'))))))) (fun n : N => @BOTTOM (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))))) a0 a1 a2 a3 a4 a5 a6 a7)).
Proof. exact (REFL _22943). Qed.
Definition ASCII : Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Ascii.ascii := _22943.
Lemma ASCII_def : ASCII = _22943.
Proof. exact (REFL ASCII). Qed.
Definition sqrt : R -> R := fun _27235 : R => @ε R (fun y : R => ((Rsgn y) = (Rsgn _27235)) /\ ((Rpow y (NUMERAL (BIT0 (BIT1 N0)))) = (Rabs _27235))).
Lemma sqrt_def : sqrt = (fun _27235 : R => @ε R (fun y : R => ((Rsgn y) = (Rsgn _27235)) /\ ((Rpow y (NUMERAL (BIT0 (BIT1 N0)))) = (Rabs _27235)))).
Proof. exact (REFL sqrt). Qed.
Definition DECIMAL : N -> N -> R := fun _27914 : N => fun _27915 : N => Rdiv (R_of_N _27914) (R_of_N _27915).
Lemma DECIMAL_def : DECIMAL = (fun _27914 : N => fun _27915 : N => Rdiv (R_of_N _27914) (R_of_N _27915)).
Proof. exact (REFL DECIMAL). Qed.
Definition eq2 {A : Type'} : A -> A -> (A -> A -> Prop) -> Prop := fun _29688 : A => fun _29689 : A => fun _29690 : A -> A -> Prop => _29690 _29688 _29689.
Lemma eq2_def {A : Type'} : (@eq2 A) = (fun _29688 : A => fun _29689 : A => fun _29690 : A -> A -> Prop => _29690 _29688 _29689).
Proof. exact (REFL (@eq2 A)). Qed.
Definition int_mod : Z -> Z -> Z -> Prop := fun _29750 : Z => fun _29751 : Z => fun _29752 : Z => Z.divide _29750 (Z.sub _29751 _29752).
Lemma int_mod_def : int_mod = (fun _29750 : Z => fun _29751 : Z => fun _29752 : Z => Z.divide _29750 (Z.sub _29751 _29752)).
Proof. exact (REFL int_mod). Qed.
Definition num_of_int : Z -> N := fun _31320 : Z => @ε N (fun n : N => (Z_of_N n) = _31320).
Lemma num_of_int_def : num_of_int = (fun _31320 : Z => @ε N (fun n : N => (Z_of_N n) = _31320)).
Proof. exact (REFL num_of_int). Qed.
Definition num_divides : N -> N -> Prop := fun _31352 : N => fun _31353 : N => Z.divide (Z_of_N _31352) (Z_of_N _31353).
Lemma num_divides_def : num_divides = (fun _31352 : N => fun _31353 : N => Z.divide (Z_of_N _31352) (Z_of_N _31353)).
Proof. exact (REFL num_divides). Qed.
Definition num_mod : N -> N -> N -> Prop := fun _31364 : N => fun _31365 : N => fun _31366 : N => int_mod (Z_of_N _31364) (Z_of_N _31365) (Z_of_N _31366).
Lemma num_mod_def : num_mod = (fun _31364 : N => fun _31365 : N => fun _31366 : N => int_mod (Z_of_N _31364) (Z_of_N _31365) (Z_of_N _31366)).
Proof. exact (REFL num_mod). Qed.
Definition num_coprime : (prod N N) -> Prop := fun _31385 : prod N N => int_coprime (@pair Z Z (Z_of_N (@fst N N _31385)) (Z_of_N (@snd N N _31385))).
Lemma num_coprime_def : num_coprime = (fun _31385 : prod N N => int_coprime (@pair Z Z (Z_of_N (@fst N N _31385)) (Z_of_N (@snd N N _31385)))).
Proof. exact (REFL num_coprime). Qed.
Definition num_gcd : (prod N N) -> N := fun _31394 : prod N N => num_of_int (int_gcd (@pair Z Z (Z_of_N (@fst N N _31394)) (Z_of_N (@snd N N _31394)))).
Lemma num_gcd_def : num_gcd = (fun _31394 : prod N N => num_of_int (int_gcd (@pair Z Z (Z_of_N (@fst N N _31394)) (Z_of_N (@snd N N _31394))))).
Proof. exact (REFL num_gcd). Qed.
Definition num_lcm : (prod N N) -> N := fun _31403 : prod N N => num_of_int (int_lcm (@pair Z Z (Z_of_N (@fst N N _31403)) (Z_of_N (@snd N N _31403)))).
Lemma num_lcm_def : num_lcm = (fun _31403 : prod N N => num_of_int (int_lcm (@pair Z Z (Z_of_N (@fst N N _31403)) (Z_of_N (@snd N N _31403))))).
Proof. exact (REFL num_lcm). Qed.
Definition prime : N -> Prop := fun _32188 : N => (~ (_32188 = (NUMERAL (BIT1 N0)))) /\ (forall x : N, (num_divides x _32188) -> (x = (NUMERAL (BIT1 N0))) \/ (x = _32188)).
Lemma prime_def : prime = (fun _32188 : N => (~ (_32188 = (NUMERAL (BIT1 N0)))) /\ (forall x : N, (num_divides x _32188) -> (x = (NUMERAL (BIT1 N0))) \/ (x = _32188))).
Proof. exact (REFL prime). Qed.
Definition real_zpow : R -> Z -> R := fun _32346 : R => fun _32347 : Z => @COND R (Z.le (Z_of_N (NUMERAL N0)) _32347) (Rpow _32346 (num_of_int _32347)) (Rinv (Rpow _32346 (num_of_int (Z.opp _32347)))).
Lemma real_zpow_def : real_zpow = (fun _32346 : R => fun _32347 : Z => @COND R (Z.le (Z_of_N (NUMERAL N0)) _32347) (Rpow _32346 (num_of_int _32347)) (Rinv (Rpow _32346 (num_of_int (Z.opp _32347))))).
Proof. exact (REFL real_zpow). Qed.
Definition INFINITE {A : Type'} : (A -> Prop) -> Prop := fun _32574 : A -> Prop => ~ (@finite_set A _32574).
Lemma INFINITE_def {A : Type'} : (@INFINITE A) = (fun _32574 : A -> Prop => ~ (@finite_set A _32574)).
Proof. exact (REFL (@INFINITE A)). Qed.
Definition INJ {A B : Type'} : (A -> B) -> (A -> Prop) -> (B -> Prop) -> Prop := fun _32591 : A -> B => fun _32592 : A -> Prop => fun _32593 : B -> Prop => (forall x : A, (@IN A x _32592) -> @IN B (_32591 x) _32593) /\ (forall x : A, forall y : A, ((@IN A x _32592) /\ ((@IN A y _32592) /\ ((_32591 x) = (_32591 y)))) -> x = y).
Lemma INJ_def {A B : Type'} : (@INJ A B) = (fun _32591 : A -> B => fun _32592 : A -> Prop => fun _32593 : B -> Prop => (forall x : A, (@IN A x _32592) -> @IN B (_32591 x) _32593) /\ (forall x : A, forall y : A, ((@IN A x _32592) /\ ((@IN A y _32592) /\ ((_32591 x) = (_32591 y)))) -> x = y)).
Proof. exact (REFL (@INJ A B)). Qed.
Definition SURJ {A B : Type'} : (A -> B) -> (A -> Prop) -> (B -> Prop) -> Prop := fun _32612 : A -> B => fun _32613 : A -> Prop => fun _32614 : B -> Prop => (forall x : A, (@IN A x _32613) -> @IN B (_32612 x) _32614) /\ (forall x : B, (@IN B x _32614) -> exists y : A, (@IN A y _32613) /\ ((_32612 y) = x)).
Lemma SURJ_def {A B : Type'} : (@SURJ A B) = (fun _32612 : A -> B => fun _32613 : A -> Prop => fun _32614 : B -> Prop => (forall x : A, (@IN A x _32613) -> @IN B (_32612 x) _32614) /\ (forall x : B, (@IN B x _32614) -> exists y : A, (@IN A y _32613) /\ ((_32612 y) = x))).
Proof. exact (REFL (@SURJ A B)). Qed.
Definition BIJ {A B : Type'} : (A -> B) -> (A -> Prop) -> (B -> Prop) -> Prop := fun _32633 : A -> B => fun _32634 : A -> Prop => fun _32635 : B -> Prop => (@INJ A B _32633 _32634 _32635) /\ (@SURJ A B _32633 _32634 _32635).
Lemma BIJ_def {A B : Type'} : (@BIJ A B) = (fun _32633 : A -> B => fun _32634 : A -> Prop => fun _32635 : B -> Prop => (@INJ A B _32633 _32634 _32635) /\ (@SURJ A B _32633 _32634 _32635)).
Proof. exact (REFL (@BIJ A B)). Qed.
Definition CHOICE {A : Type'} : (A -> Prop) -> A := fun _32654 : A -> Prop => @ε A (fun x : A => @IN A x _32654).
Lemma CHOICE_def {A : Type'} : (@CHOICE A) = (fun _32654 : A -> Prop => @ε A (fun x : A => @IN A x _32654)).
Proof. exact (REFL (@CHOICE A)). Qed.
Definition REST {A : Type'} : (A -> Prop) -> A -> Prop := fun _32659 : A -> Prop => @DELETE A _32659 (@CHOICE A _32659).
Lemma REST_def {A : Type'} : (@REST A) = (fun _32659 : A -> Prop => @DELETE A _32659 (@CHOICE A _32659)).
Proof. exact (REFL (@REST A)). Qed.
Definition FINREC {A B : Type'} : (A -> B -> B) -> B -> (A -> Prop) -> B -> N -> Prop := @ε ((prod N (prod N (prod N (prod N (prod N N))))) -> (A -> B -> B) -> B -> (A -> Prop) -> B -> N -> Prop) (fun FINREC' : (prod N (prod N (prod N (prod N (prod N N))))) -> (A -> B -> B) -> B -> (A -> Prop) -> B -> N -> Prop => forall _42261 : prod N (prod N (prod N (prod N (prod N N)))), (forall f : A -> B -> B, forall s : A -> Prop, forall a : B, forall b : B, (FINREC' _42261 f b s a (NUMERAL N0)) = ((s = (@set0 A)) /\ (a = b))) /\ (forall b : B, forall s : A -> Prop, forall n : N, forall a : B, forall f : A -> B -> B, (FINREC' _42261 f b s a (N.succ n)) = (exists x : A, exists c : B, (@IN A x s) /\ ((FINREC' _42261 f b (@DELETE A s x) c n) /\ (a = (f x c)))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0))))))))))))).
Lemma FINREC_def {A B : Type'} : (@FINREC A B) = (@ε ((prod N (prod N (prod N (prod N (prod N N))))) -> (A -> B -> B) -> B -> (A -> Prop) -> B -> N -> Prop) (fun FINREC' : (prod N (prod N (prod N (prod N (prod N N))))) -> (A -> B -> B) -> B -> (A -> Prop) -> B -> N -> Prop => forall _42261 : prod N (prod N (prod N (prod N (prod N N)))), (forall f : A -> B -> B, forall s : A -> Prop, forall a : B, forall b : B, (FINREC' _42261 f b s a (NUMERAL N0)) = ((s = (@set0 A)) /\ (a = b))) /\ (forall b : B, forall s : A -> Prop, forall n : N, forall a : B, forall f : A -> B -> B, (FINREC' _42261 f b s a (N.succ n)) = (exists x : A, exists c : B, (@IN A x s) /\ ((FINREC' _42261 f b (@DELETE A s x) c n) /\ (a = (f x c)))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))))))))).
Proof. exact (REFL (@FINREC A B)). Qed.
Definition HAS_SIZE {A : Type'} : (A -> Prop) -> N -> Prop := fun _43489 : A -> Prop => fun _43490 : N => (@finite_set A _43489) /\ ((@card A _43489) = _43490).
Lemma HAS_SIZE_def {A : Type'} : (@HAS_SIZE A) = (fun _43489 : A -> Prop => fun _43490 : N => (@finite_set A _43489) /\ ((@card A _43489) = _43490)).
Proof. exact (REFL (@HAS_SIZE A)). Qed.
Definition CROSS {A B : Type'} : (A -> Prop) -> (B -> Prop) -> (prod A B) -> Prop := fun _47408 : A -> Prop => fun _47409 : B -> Prop => @GSPEC (prod A B) (fun GEN_PVAR_132 : prod A B => exists x : A, exists y : B, @SETSPEC (prod A B) GEN_PVAR_132 ((@IN A x _47408) /\ (@IN B y _47409)) (@pair A B x y)).
Lemma CROSS_def {A B : Type'} : (@CROSS A B) = (fun _47408 : A -> Prop => fun _47409 : B -> Prop => @GSPEC (prod A B) (fun GEN_PVAR_132 : prod A B => exists x : A, exists y : B, @SETSPEC (prod A B) GEN_PVAR_132 ((@IN A x _47408) /\ (@IN B y _47409)) (@pair A B x y))).
Proof. exact (REFL (@CROSS A B)). Qed.
Definition ARB {A : Type'} : A := @ε A (fun x : A => False).
Lemma ARB_def {A : Type'} : (@ARB A) = (@ε A (fun x : A => False)).
Proof. exact (REFL (@ARB A)). Qed.
Definition EXTENSIONAL {A B : Type'} : (A -> Prop) -> (A -> B) -> Prop := fun _48182 : A -> Prop => @GSPEC (A -> B) (fun GEN_PVAR_141 : A -> B => exists f : A -> B, @SETSPEC (A -> B) GEN_PVAR_141 (forall x : A, (~ (@IN A x _48182)) -> (f x) = (@ARB B)) f).
Lemma EXTENSIONAL_def {A B : Type'} : (@EXTENSIONAL A B) = (fun _48182 : A -> Prop => @GSPEC (A -> B) (fun GEN_PVAR_141 : A -> B => exists f : A -> B, @SETSPEC (A -> B) GEN_PVAR_141 (forall x : A, (~ (@IN A x _48182)) -> (f x) = (@ARB B)) f)).
Proof. exact (REFL (@EXTENSIONAL A B)). Qed.
Definition RESTRICTION {A B : Type'} : (A -> Prop) -> (A -> B) -> A -> B := fun _48234 : A -> Prop => fun _48235 : A -> B => fun _48236 : A => @COND B (@IN A _48236 _48234) (_48235 _48236) (@ARB B).
Lemma RESTRICTION_def {A B : Type'} : (@RESTRICTION A B) = (fun _48234 : A -> Prop => fun _48235 : A -> B => fun _48236 : A => @COND B (@IN A _48236 _48234) (_48235 _48236) (@ARB B)).
Proof. exact (REFL (@RESTRICTION A B)). Qed.
Definition cartesian_product {A K : Type'} : (K -> Prop) -> (K -> A -> Prop) -> (K -> A) -> Prop := fun _48429 : K -> Prop => fun _48430 : K -> A -> Prop => @GSPEC (K -> A) (fun GEN_PVAR_142 : K -> A => exists f : K -> A, @SETSPEC (K -> A) GEN_PVAR_142 ((@EXTENSIONAL K A _48429 f) /\ (forall i : K, (@IN K i _48429) -> @IN A (f i) (_48430 i))) f).
Lemma cartesian_product_def {A K : Type'} : (@cartesian_product A K) = (fun _48429 : K -> Prop => fun _48430 : K -> A -> Prop => @GSPEC (K -> A) (fun GEN_PVAR_142 : K -> A => exists f : K -> A, @SETSPEC (K -> A) GEN_PVAR_142 ((@EXTENSIONAL K A _48429 f) /\ (forall i : K, (@IN K i _48429) -> @IN A (f i) (_48430 i))) f)).
Proof. exact (REFL (@cartesian_product A K)). Qed.
Definition product_map {A B K : Type'} : (K -> Prop) -> (K -> A -> B) -> (K -> A) -> K -> B := fun _49478 : K -> Prop => fun _49479 : K -> A -> B => fun x : K -> A => @RESTRICTION K B _49478 (fun i : K => _49479 i (x i)).
Lemma product_map_def {A B K : Type'} : (@product_map A B K) = (fun _49478 : K -> Prop => fun _49479 : K -> A -> B => fun x : K -> A => @RESTRICTION K B _49478 (fun i : K => _49479 i (x i))).
Proof. exact (REFL (@product_map A B K)). Qed.
Definition disjoint_union {A K : Type'} : (K -> Prop) -> (K -> A -> Prop) -> (prod K A) -> Prop := fun _49614 : K -> Prop => fun _49615 : K -> A -> Prop => @GSPEC (prod K A) (fun GEN_PVAR_145 : prod K A => exists i : K, exists x : A, @SETSPEC (prod K A) GEN_PVAR_145 ((@IN K i _49614) /\ (@IN A x (_49615 i))) (@pair K A i x)).
Lemma disjoint_union_def {A K : Type'} : (@disjoint_union A K) = (fun _49614 : K -> Prop => fun _49615 : K -> A -> Prop => @GSPEC (prod K A) (fun GEN_PVAR_145 : prod K A => exists i : K, exists x : A, @SETSPEC (prod K A) GEN_PVAR_145 ((@IN K i _49614) /\ (@IN A x (_49615 i))) (@pair K A i x))).
Proof. exact (REFL (@disjoint_union A K)). Qed.
Definition pairwise {A : Type'} : (A -> A -> Prop) -> (A -> Prop) -> Prop := fun _56702 : A -> A -> Prop => fun _56703 : A -> Prop => forall x : A, forall y : A, ((@IN A x _56703) /\ ((@IN A y _56703) /\ (~ (x = y)))) -> _56702 x y.
Lemma pairwise_def {A : Type'} : (@pairwise A) = (fun _56702 : A -> A -> Prop => fun _56703 : A -> Prop => forall x : A, forall y : A, ((@IN A x _56703) /\ ((@IN A y _56703) /\ (~ (x = y)))) -> _56702 x y).
Proof. exact (REFL (@pairwise A)). Qed.
Definition UNION_OF {A : Type'} : (((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop := fun _57415 : ((A -> Prop) -> Prop) -> Prop => fun _57416 : (A -> Prop) -> Prop => fun s : A -> Prop => exists u : (A -> Prop) -> Prop, (_57415 u) /\ ((forall c : A -> Prop, (@IN (A -> Prop) c u) -> _57416 c) /\ ((@UNIONS A u) = s)).
Lemma UNION_OF_def {A : Type'} : (@UNION_OF A) = (fun _57415 : ((A -> Prop) -> Prop) -> Prop => fun _57416 : (A -> Prop) -> Prop => fun s : A -> Prop => exists u : (A -> Prop) -> Prop, (_57415 u) /\ ((forall c : A -> Prop, (@IN (A -> Prop) c u) -> _57416 c) /\ ((@UNIONS A u) = s))).
Proof. exact (REFL (@UNION_OF A)). Qed.
Definition INTERSECTION_OF {A : Type'} : (((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop := fun _57427 : ((A -> Prop) -> Prop) -> Prop => fun _57428 : (A -> Prop) -> Prop => fun s : A -> Prop => exists u : (A -> Prop) -> Prop, (_57427 u) /\ ((forall c : A -> Prop, (@IN (A -> Prop) c u) -> _57428 c) /\ ((@INTERS A u) = s)).
Lemma INTERSECTION_OF_def {A : Type'} : (@INTERSECTION_OF A) = (fun _57427 : ((A -> Prop) -> Prop) -> Prop => fun _57428 : (A -> Prop) -> Prop => fun s : A -> Prop => exists u : (A -> Prop) -> Prop, (_57427 u) /\ ((forall c : A -> Prop, (@IN (A -> Prop) c u) -> _57428 c) /\ ((@INTERS A u) = s))).
Proof. exact (REFL (@INTERSECTION_OF A)). Qed.
Definition ARBITRARY {A : Type'} : ((A -> Prop) -> Prop) -> Prop := fun _57563 : (A -> Prop) -> Prop => True.
Lemma ARBITRARY_def {A : Type'} : (@ARBITRARY A) = (fun _57563 : (A -> Prop) -> Prop => True).
Proof. exact (REFL (@ARBITRARY A)). Qed.
Definition le_c {A B : Type'} : (A -> Prop) -> (B -> Prop) -> Prop := fun _64157 : A -> Prop => fun _64158 : B -> Prop => exists f : A -> B, (forall x : A, (@IN A x _64157) -> @IN B (f x) _64158) /\ (forall x : A, forall y : A, ((@IN A x _64157) /\ ((@IN A y _64157) /\ ((f x) = (f y)))) -> x = y).
Lemma le_c_def {A B : Type'} : (@le_c A B) = (fun _64157 : A -> Prop => fun _64158 : B -> Prop => exists f : A -> B, (forall x : A, (@IN A x _64157) -> @IN B (f x) _64158) /\ (forall x : A, forall y : A, ((@IN A x _64157) /\ ((@IN A y _64157) /\ ((f x) = (f y)))) -> x = y)).
Proof. exact (REFL (@le_c A B)). Qed.
Definition lt_c {A B : Type'} : (A -> Prop) -> (B -> Prop) -> Prop := fun _64169 : A -> Prop => fun _64170 : B -> Prop => (@le_c A B _64169 _64170) /\ (~ (@le_c B A _64170 _64169)).
Lemma lt_c_def {A B : Type'} : (@lt_c A B) = (fun _64169 : A -> Prop => fun _64170 : B -> Prop => (@le_c A B _64169 _64170) /\ (~ (@le_c B A _64170 _64169))).
Proof. exact (REFL (@lt_c A B)). Qed.
Definition eq_c {A B : Type'} : (A -> Prop) -> (B -> Prop) -> Prop := fun _64181 : A -> Prop => fun _64182 : B -> Prop => exists f : A -> B, (forall x : A, (@IN A x _64181) -> @IN B (f x) _64182) /\ (forall y : B, (@IN B y _64182) -> @ex1 A (fun x : A => (@IN A x _64181) /\ ((f x) = y))).
Lemma eq_c_def {A B : Type'} : (@eq_c A B) = (fun _64181 : A -> Prop => fun _64182 : B -> Prop => exists f : A -> B, (forall x : A, (@IN A x _64181) -> @IN B (f x) _64182) /\ (forall y : B, (@IN B y _64182) -> @ex1 A (fun x : A => (@IN A x _64181) /\ ((f x) = y)))).
Proof. exact (REFL (@eq_c A B)). Qed.
Definition ge_c {A B : Type'} : (A -> Prop) -> (B -> Prop) -> Prop := fun _64193 : A -> Prop => fun _64194 : B -> Prop => @le_c B A _64194 _64193.
Lemma ge_c_def {A B : Type'} : (@ge_c A B) = (fun _64193 : A -> Prop => fun _64194 : B -> Prop => @le_c B A _64194 _64193).
Proof. exact (REFL (@ge_c A B)). Qed.
Definition gt_c {A B : Type'} : (A -> Prop) -> (B -> Prop) -> Prop := fun _64205 : A -> Prop => fun _64206 : B -> Prop => @lt_c B A _64206 _64205.
Lemma gt_c_def {A B : Type'} : (@gt_c A B) = (fun _64205 : A -> Prop => fun _64206 : B -> Prop => @lt_c B A _64206 _64205).
Proof. exact (REFL (@gt_c A B)). Qed.
Definition COUNTABLE {A : Type'} : (A -> Prop) -> Prop := fun _64356 : A -> Prop => @ge_c N A (@setT N) _64356.
Lemma COUNTABLE_def {A : Type'} : (@COUNTABLE A) = (fun _64356 : A -> Prop => @ge_c N A (@setT N) _64356).
Proof. exact (REFL (@COUNTABLE A)). Qed.
Definition sup : (R -> Prop) -> R := fun _64361 : R -> Prop => @ε R (fun a : R => (forall x : R, (@IN R x _64361) -> Rle x a) /\ (forall b : R, (forall x : R, (@IN R x _64361) -> Rle x b) -> Rle a b)).
Lemma sup_def : sup = (fun _64361 : R -> Prop => @ε R (fun a : R => (forall x : R, (@IN R x _64361) -> Rle x a) /\ (forall b : R, (forall x : R, (@IN R x _64361) -> Rle x b) -> Rle a b))).
Proof. exact (REFL sup). Qed.
Definition inf : (R -> Prop) -> R := fun _65220 : R -> Prop => @ε R (fun a : R => (forall x : R, (@IN R x _65220) -> Rle a x) /\ (forall b : R, (forall x : R, (@IN R x _65220) -> Rle b x) -> Rle b a)).
Lemma inf_def : inf = (fun _65220 : R -> Prop => @ε R (fun a : R => (forall x : R, (@IN R x _65220) -> Rle a x) /\ (forall b : R, (forall x : R, (@IN R x _65220) -> Rle b x) -> Rle b a))).
Proof. exact (REFL inf). Qed.
Definition has_inf : (R -> Prop) -> R -> Prop := fun _66570 : R -> Prop => fun _66571 : R => forall c : R, (forall x : R, (@IN R x _66570) -> Rle c x) = (Rle c _66571).
Lemma has_inf_def : has_inf = (fun _66570 : R -> Prop => fun _66571 : R => forall c : R, (forall x : R, (@IN R x _66570) -> Rle c x) = (Rle c _66571)).
Proof. exact (REFL has_inf). Qed.
Definition has_sup : (R -> Prop) -> R -> Prop := fun _66582 : R -> Prop => fun _66583 : R => forall c : R, (forall x : R, (@IN R x _66582) -> Rle x c) = (Rle _66583 c).
Lemma has_sup_def : has_sup = (fun _66582 : R -> Prop => fun _66583 : R => forall c : R, (forall x : R, (@IN R x _66582) -> Rle x c) = (Rle _66583 c)).
Proof. exact (REFL has_sup). Qed.
Definition neutral {A : Type'} : (A -> A -> A) -> A := fun _68920 : A -> A -> A => @ε A (fun x : A => forall y : A, ((_68920 x y) = y) /\ ((_68920 y x) = y)).
Lemma neutral_def {A : Type'} : (@neutral A) = (fun _68920 : A -> A -> A => @ε A (fun x : A => forall y : A, ((_68920 x y) = y) /\ ((_68920 y x) = y))).
Proof. exact (REFL (@neutral A)). Qed.
Definition monoidal {A : Type'} : (A -> A -> A) -> Prop := fun _68925 : A -> A -> A => (forall x : A, forall y : A, (_68925 x y) = (_68925 y x)) /\ ((forall x : A, forall y : A, forall z : A, (_68925 x (_68925 y z)) = (_68925 (_68925 x y) z)) /\ (forall x : A, (_68925 (@neutral A _68925) x) = x)).
Lemma monoidal_def {A : Type'} : (@monoidal A) = (fun _68925 : A -> A -> A => (forall x : A, forall y : A, (_68925 x y) = (_68925 y x)) /\ ((forall x : A, forall y : A, forall z : A, (_68925 x (_68925 y z)) = (_68925 (_68925 x y) z)) /\ (forall x : A, (_68925 (@neutral A _68925) x) = x))).
Proof. exact (REFL (@monoidal A)). Qed.
Definition support {A B : Type'} : (B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop := fun _69010 : B -> B -> B => fun _69011 : A -> B => fun _69012 : A -> Prop => @GSPEC A (fun GEN_PVAR_239 : A => exists x : A, @SETSPEC A GEN_PVAR_239 ((@IN A x _69012) /\ (~ ((_69011 x) = (@neutral B _69010)))) x).
Lemma support_def {A B : Type'} : (@support A B) = (fun _69010 : B -> B -> B => fun _69011 : A -> B => fun _69012 : A -> Prop => @GSPEC A (fun GEN_PVAR_239 : A => exists x : A, @SETSPEC A GEN_PVAR_239 ((@IN A x _69012) /\ (~ ((_69011 x) = (@neutral B _69010)))) x)).
Proof. exact (REFL (@support A B)). Qed.
Definition iterate {A B : Type'} : (B -> B -> B) -> (A -> Prop) -> (A -> B) -> B := fun _69031 : B -> B -> B => fun _69032 : A -> Prop => fun _69033 : A -> B => @COND B (@finite_set A (@support A B _69031 _69033 _69032)) (@fold_set A B (fun x : A => fun a : B => _69031 (_69033 x) a) (@support A B _69031 _69033 _69032) (@neutral B _69031)) (@neutral B _69031).
Lemma iterate_def {A B : Type'} : (@iterate A B) = (fun _69031 : B -> B -> B => fun _69032 : A -> Prop => fun _69033 : A -> B => @COND B (@finite_set A (@support A B _69031 _69033 _69032)) (@fold_set A B (fun x : A => fun a : B => _69031 (_69033 x) a) (@support A B _69031 _69033 _69032) (@neutral B _69031)) (@neutral B _69031)).
Proof. exact (REFL (@iterate A B)). Qed.
Definition iterato {A K : Type'} : (A -> Prop) -> A -> (A -> A -> A) -> (K -> K -> Prop) -> (K -> Prop) -> (K -> A) -> A := @ε ((prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (A -> Prop) -> A -> (A -> A -> A) -> (K -> K -> Prop) -> (K -> Prop) -> (K -> A) -> A) (fun itty : (prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (A -> Prop) -> A -> (A -> A -> A) -> (K -> K -> Prop) -> (K -> Prop) -> (K -> A) -> A => forall _76787 : prod N (prod N (prod N (prod N (prod N (prod N N))))), forall dom : A -> Prop, forall neut : A, forall op : A -> A -> A, forall ltle : K -> K -> Prop, forall k : K -> Prop, forall f : K -> A, (itty _76787 dom neut op ltle k f) = (@COND A ((@finite_set K (@GSPEC K (fun GEN_PVAR_265 : K => exists i : K, @SETSPEC K GEN_PVAR_265 ((@IN K i k) /\ (@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A))))) i))) /\ (~ ((@GSPEC K (fun GEN_PVAR_266 : K => exists i : K, @SETSPEC K GEN_PVAR_266 ((@IN K i k) /\ (@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A))))) i)) = (@set0 K)))) (@LET K A (fun i : K => @LET_END A (op (f i) (itty _76787 dom neut op ltle (@GSPEC K (fun GEN_PVAR_267 : K => exists j : K, @SETSPEC K GEN_PVAR_267 ((@IN K j (@DELETE K k i)) /\ (@IN A (f j) (@setD A dom (@INSERT A neut (@set0 A))))) j)) f))) (@COND K (exists i : K, (@IN K i k) /\ ((@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A)))) /\ (forall j : K, ((ltle j i) /\ ((@IN K j k) /\ (@IN A (f j) (@setD A dom (@INSERT A neut (@set0 A)))))) -> j = i))) (@ε K (fun i : K => (@IN K i k) /\ ((@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A)))) /\ (forall j : K, ((ltle j i) /\ ((@IN K j k) /\ (@IN A (f j) (@setD A dom (@INSERT A neut (@set0 A)))))) -> j = i)))) (@ε K (fun i : K => (@IN K i k) /\ (@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A)))))))) neut)) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))))))))).
Lemma iterato_def {A K : Type'} : (@iterato A K) = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (A -> Prop) -> A -> (A -> A -> A) -> (K -> K -> Prop) -> (K -> Prop) -> (K -> A) -> A) (fun itty : (prod N (prod N (prod N (prod N (prod N (prod N N)))))) -> (A -> Prop) -> A -> (A -> A -> A) -> (K -> K -> Prop) -> (K -> Prop) -> (K -> A) -> A => forall _76787 : prod N (prod N (prod N (prod N (prod N (prod N N))))), forall dom : A -> Prop, forall neut : A, forall op : A -> A -> A, forall ltle : K -> K -> Prop, forall k : K -> Prop, forall f : K -> A, (itty _76787 dom neut op ltle k f) = (@COND A ((@finite_set K (@GSPEC K (fun GEN_PVAR_265 : K => exists i : K, @SETSPEC K GEN_PVAR_265 ((@IN K i k) /\ (@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A))))) i))) /\ (~ ((@GSPEC K (fun GEN_PVAR_266 : K => exists i : K, @SETSPEC K GEN_PVAR_266 ((@IN K i k) /\ (@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A))))) i)) = (@set0 K)))) (@LET K A (fun i : K => @LET_END A (op (f i) (itty _76787 dom neut op ltle (@GSPEC K (fun GEN_PVAR_267 : K => exists j : K, @SETSPEC K GEN_PVAR_267 ((@IN K j (@DELETE K k i)) /\ (@IN A (f j) (@setD A dom (@INSERT A neut (@set0 A))))) j)) f))) (@COND K (exists i : K, (@IN K i k) /\ ((@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A)))) /\ (forall j : K, ((ltle j i) /\ ((@IN K j k) /\ (@IN A (f j) (@setD A dom (@INSERT A neut (@set0 A)))))) -> j = i))) (@ε K (fun i : K => (@IN K i k) /\ ((@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A)))) /\ (forall j : K, ((ltle j i) /\ ((@IN K j k) /\ (@IN A (f j) (@setD A dom (@INSERT A neut (@set0 A)))))) -> j = i)))) (@ε K (fun i : K => (@IN K i k) /\ (@IN A (f i) (@setD A dom (@INSERT A neut (@set0 A)))))))) neut)) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0))))))))))))))).
Proof. exact (REFL (@iterato A K)). Qed.
Definition nproduct {A : Type'} : (A -> Prop) -> (A -> N) -> N := @iterate A N N.mul.
Lemma nproduct_def {A : Type'} : (@nproduct A) = (@iterate A N N.mul).
Proof. exact (REFL (@nproduct A)). Qed.
Definition iproduct {A : Type'} : (A -> Prop) -> (A -> Z) -> Z := @iterate A Z Z.mul.
Lemma iproduct_def {A : Type'} : (@iproduct A) = (@iterate A Z Z.mul).
Proof. exact (REFL (@iproduct A)). Qed.
Definition product {A : Type'} : (A -> Prop) -> (A -> R) -> R := @iterate A R Rmult.
Lemma product_def {A : Type'} : (@product A) = (@iterate A R Rmult).
Proof. exact (REFL (@product A)). Qed.
Definition isum {A : Type'} : (A -> Prop) -> (A -> Z) -> Z := @iterate A Z Z.add.
Lemma isum_def {A : Type'} : (@isum A) = (@iterate A Z Z.add).
Proof. exact (REFL (@isum A)). Qed.
Definition nsum {A : Type'} : (A -> Prop) -> (A -> N) -> N := @iterate A N N.add.
Lemma nsum_def {A : Type'} : (@nsum A) = (@iterate A N N.add).
Proof. exact (REFL (@nsum A)). Qed.
Definition sum {A : Type'} : (A -> Prop) -> (A -> R) -> R := @iterate A R Rplus.
Lemma sum_def {A : Type'} : (@sum A) = (@iterate A R Rplus).
Proof. exact (REFL (@sum A)). Qed.
Definition polynomial_function : (R -> R) -> Prop := fun _94200 : R -> R => exists m : N, exists c : N -> R, forall x : R, (_94200 x) = (@sum N (Ninterval (NUMERAL N0) m) (fun i : N => Rmult (c i) (Rpow x i))).
Lemma polynomial_function_def : polynomial_function = (fun _94200 : R -> R => exists m : N, exists c : N -> R, forall x : R, (_94200 x) = (@sum N (Ninterval (NUMERAL N0) m) (fun i : N => Rmult (c i) (Rpow x i)))).
Proof. exact (REFL polynomial_function). Qed.
Definition dollar {A N' : Type'} : (cart A N') -> N -> A := fun _94652 : cart A N' => fun _94653 : N => @dest_cart A N' _94652 (@finite_index N' _94653).
Lemma dollar_def {A N' : Type'} : (@dollar A N') = (fun _94652 : cart A N' => fun _94653 : N => @dest_cart A N' _94652 (@finite_index N' _94653)).
Proof. exact (REFL (@dollar A N')). Qed.
Definition lambda {A B : Type'} : (N -> A) -> cart A B := fun _94688 : N -> A => @ε (cart A B) (fun f : cart A B => forall i : N, ((N.le (NUMERAL (BIT1 N0)) i) /\ (N.le i (@dimindex B (@setT B)))) -> (@dollar A B f i) = (_94688 i)).
Lemma lambda_def {A B : Type'} : (@lambda A B) = (fun _94688 : N -> A => @ε (cart A B) (fun f : cart A B => forall i : N, ((N.le (NUMERAL (BIT1 N0)) i) /\ (N.le i (@dimindex B (@setT B)))) -> (@dollar A B f i) = (_94688 i))).
Proof. exact (REFL (@lambda A B)). Qed.
Definition pastecart {A M N' : Type'} : (cart A M) -> (cart A N') -> cart A (finite_sum M N') := fun _94979 : cart A M => fun _94980 : cart A N' => @lambda A (finite_sum M N') (fun i : N => @COND A (N.le i (@dimindex M (@setT M))) (@dollar A M _94979 i) (@dollar A N' _94980 (N.sub i (@dimindex M (@setT M))))).
Lemma pastecart_def {A M N' : Type'} : (@pastecart A M N') = (fun _94979 : cart A M => fun _94980 : cart A N' => @lambda A (finite_sum M N') (fun i : N => @COND A (N.le i (@dimindex M (@setT M))) (@dollar A M _94979 i) (@dollar A N' _94980 (N.sub i (@dimindex M (@setT M)))))).
Proof. exact (REFL (@pastecart A M N')). Qed.
Definition fstcart {A M N' : Type'} : (cart A (finite_sum M N')) -> cart A M := fun _94991 : cart A (finite_sum M N') => @lambda A M (fun i : N => @dollar A (finite_sum M N') _94991 i).
Lemma fstcart_def {A M N' : Type'} : (@fstcart A M N') = (fun _94991 : cart A (finite_sum M N') => @lambda A M (fun i : N => @dollar A (finite_sum M N') _94991 i)).
Proof. exact (REFL (@fstcart A M N')). Qed.
Definition sndcart {A M N' : Type'} : (cart A (finite_sum M N')) -> cart A N' := fun _94996 : cart A (finite_sum M N') => @lambda A N' (fun i : N => @dollar A (finite_sum M N') _94996 (N.add i (@dimindex M (@setT M)))).
Lemma sndcart_def {A M N' : Type'} : (@sndcart A M N') = (fun _94996 : cart A (finite_sum M N') => @lambda A N' (fun i : N => @dollar A (finite_sum M N') _94996 (N.add i (@dimindex M (@setT M))))).
Proof. exact (REFL (@sndcart A M N')). Qed.
Definition _100406 {A : Type'} : (finite_sum A A) -> tybit0 A := fun a : finite_sum A A => @_mk_tybit0 A ((fun a' : finite_sum A A => @CONSTR (finite_sum A A) (NUMERAL N0) a' (fun n : N => @BOTTOM (finite_sum A A))) a).
Lemma _100406_def {A : Type'} : (@_100406 A) = (fun a : finite_sum A A => @_mk_tybit0 A ((fun a' : finite_sum A A => @CONSTR (finite_sum A A) (NUMERAL N0) a' (fun n : N => @BOTTOM (finite_sum A A))) a)).
Proof. exact (REFL (@_100406 A)). Qed.
Definition mktybit0 {A : Type'} : (finite_sum A A) -> tybit0 A := @_100406 A.
Lemma mktybit0_def {A : Type'} : (@mktybit0 A) = (@_100406 A).
Proof. exact (REFL (@mktybit0 A)). Qed.
Definition _100425 {A : Type'} : (finite_sum (finite_sum A A) unit) -> tybit1 A := fun a : finite_sum (finite_sum A A) unit => @_mk_tybit1 A ((fun a' : finite_sum (finite_sum A A) unit => @CONSTR (finite_sum (finite_sum A A) unit) (NUMERAL N0) a' (fun n : N => @BOTTOM (finite_sum (finite_sum A A) unit))) a).
Lemma _100425_def {A : Type'} : (@_100425 A) = (fun a : finite_sum (finite_sum A A) unit => @_mk_tybit1 A ((fun a' : finite_sum (finite_sum A A) unit => @CONSTR (finite_sum (finite_sum A A) unit) (NUMERAL N0) a' (fun n : N => @BOTTOM (finite_sum (finite_sum A A) unit))) a)).
Proof. exact (REFL (@_100425 A)). Qed.
Definition mktybit1 {A : Type'} : (finite_sum (finite_sum A A) unit) -> tybit1 A := @_100425 A.
Lemma mktybit1_def {A : Type'} : (@mktybit1 A) = (@_100425 A).
Proof. exact (REFL (@mktybit1 A)). Qed.
Definition vector {A N' : Type'} : (list A) -> cart A N' := fun _102119 : list A => @lambda A N' (fun i : N => @Nth A (N.sub i (NUMERAL (BIT1 N0))) _102119).
Lemma vector_def {A N' : Type'} : (@vector A N') = (fun _102119 : list A => @lambda A N' (fun i : N => @Nth A (N.sub i (NUMERAL (BIT1 N0))) _102119)).
Proof. exact (REFL (@vector A N')). Qed.
Definition PCROSS {A M N' : Type'} : ((cart A M) -> Prop) -> ((cart A N') -> Prop) -> (cart A (finite_sum M N')) -> Prop := fun _102146 : (cart A M) -> Prop => fun _102147 : (cart A N') -> Prop => @GSPEC (cart A (finite_sum M N')) (fun GEN_PVAR_363 : cart A (finite_sum M N') => exists x : cart A M, exists y : cart A N', @SETSPEC (cart A (finite_sum M N')) GEN_PVAR_363 ((@IN (cart A M) x _102146) /\ (@IN (cart A N') y _102147)) (@pastecart A M N' x y)).
Lemma PCROSS_def {A M N' : Type'} : (@PCROSS A M N') = (fun _102146 : (cart A M) -> Prop => fun _102147 : (cart A N') -> Prop => @GSPEC (cart A (finite_sum M N')) (fun GEN_PVAR_363 : cart A (finite_sum M N') => exists x : cart A M, exists y : cart A N', @SETSPEC (cart A (finite_sum M N')) GEN_PVAR_363 ((@IN (cart A M) x _102146) /\ (@IN (cart A N') y _102147)) (@pastecart A M N' x y))).
Proof. exact (REFL (@PCROSS A M N')). Qed.
Definition CASEWISE {_138002 _138038 _138042 _138043 : Type'} : (list (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002))) -> _138043 -> _138042 -> _138002 := @ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> (list (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002))) -> _138043 -> _138042 -> _138002) (fun CASEWISE' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> (list (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002))) -> _138043 -> _138042 -> _138002 => forall _102751 : prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))), (forall f : _138043, forall x : _138042, (CASEWISE' _102751 (@nil (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002))) f x) = (@ε _138002 (fun y : _138002 => True))) /\ (forall h : prod (_138038 -> _138042) (_138043 -> _138038 -> _138002), forall t : list (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002)), forall f : _138043, forall x : _138042, (CASEWISE' _102751 (@cons (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002)) h t) f x) = (@COND _138002 (exists y : _138038, (@fst (_138038 -> _138042) (_138043 -> _138038 -> _138002) h y) = x) (@snd (_138038 -> _138042) (_138043 -> _138038 -> _138002) h f (@ε _138038 (fun y : _138038 => (@fst (_138038 -> _138042) (_138043 -> _138038 -> _138002) h y) = x))) (CASEWISE' _102751 t f x)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0))))))))))))))).
Lemma CASEWISE_def {_138002 _138038 _138042 _138043 : Type'} : (@CASEWISE _138002 _138038 _138042 _138043) = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> (list (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002))) -> _138043 -> _138042 -> _138002) (fun CASEWISE' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> (list (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002))) -> _138043 -> _138042 -> _138002 => forall _102751 : prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))), (forall f : _138043, forall x : _138042, (CASEWISE' _102751 (@nil (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002))) f x) = (@ε _138002 (fun y : _138002 => True))) /\ (forall h : prod (_138038 -> _138042) (_138043 -> _138038 -> _138002), forall t : list (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002)), forall f : _138043, forall x : _138042, (CASEWISE' _102751 (@cons (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002)) h t) f x) = (@COND _138002 (exists y : _138038, (@fst (_138038 -> _138042) (_138043 -> _138038 -> _138002) h y) = x) (@snd (_138038 -> _138042) (_138043 -> _138038 -> _138002) h f (@ε _138038 (fun y : _138038 => (@fst (_138038 -> _138042) (_138043 -> _138038 -> _138002) h y) = x))) (CASEWISE' _102751 t f x)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))))))))))).
Proof. exact (REFL (@CASEWISE _138002 _138038 _138042 _138043)). Qed.
Definition admissible {_138333 _138336 _138340 _138341 _138346 : Type'} : (_138340 -> _138333 -> Prop) -> ((_138340 -> _138336) -> _138346 -> Prop) -> (_138346 -> _138333) -> ((_138340 -> _138336) -> _138346 -> _138341) -> Prop := fun _103818 : _138340 -> _138333 -> Prop => fun _103819 : (_138340 -> _138336) -> _138346 -> Prop => fun _103820 : _138346 -> _138333 => fun _103821 : (_138340 -> _138336) -> _138346 -> _138341 => forall f : _138340 -> _138336, forall g : _138340 -> _138336, forall a : _138346, ((_103819 f a) /\ ((_103819 g a) /\ (forall z : _138340, (_103818 z (_103820 a)) -> (f z) = (g z)))) -> (_103821 f a) = (_103821 g a).
Lemma admissible_def {_138333 _138336 _138340 _138341 _138346 : Type'} : (@admissible _138333 _138336 _138340 _138341 _138346) = (fun _103818 : _138340 -> _138333 -> Prop => fun _103819 : (_138340 -> _138336) -> _138346 -> Prop => fun _103820 : _138346 -> _138333 => fun _103821 : (_138340 -> _138336) -> _138346 -> _138341 => forall f : _138340 -> _138336, forall g : _138340 -> _138336, forall a : _138346, ((_103819 f a) /\ ((_103819 g a) /\ (forall z : _138340, (_103818 z (_103820 a)) -> (f z) = (g z)))) -> (_103821 f a) = (_103821 g a)).
Proof. exact (REFL (@admissible _138333 _138336 _138340 _138341 _138346)). Qed.
Definition tailadmissible {A B P : Type'} : (A -> A -> Prop) -> ((A -> B) -> P -> Prop) -> (P -> A) -> ((A -> B) -> P -> B) -> Prop := fun _103850 : A -> A -> Prop => fun _103851 : (A -> B) -> P -> Prop => fun _103852 : P -> A => fun _103853 : (A -> B) -> P -> B => exists P' : (A -> B) -> P -> Prop, exists G : (A -> B) -> P -> A, exists H : (A -> B) -> P -> B, (forall f : A -> B, forall a : P, forall y : A, ((P' f a) /\ (_103850 y (G f a))) -> _103850 y (_103852 a)) /\ ((forall f : A -> B, forall g : A -> B, forall a : P, (forall z : A, (_103850 z (_103852 a)) -> (f z) = (g z)) -> ((P' f a) = (P' g a)) /\ (((G f a) = (G g a)) /\ ((H f a) = (H g a)))) /\ (forall f : A -> B, forall a : P, (_103851 f a) -> (_103853 f a) = (@COND B (P' f a) (f (G f a)) (H f a)))).
Lemma tailadmissible_def {A B P : Type'} : (@tailadmissible A B P) = (fun _103850 : A -> A -> Prop => fun _103851 : (A -> B) -> P -> Prop => fun _103852 : P -> A => fun _103853 : (A -> B) -> P -> B => exists P' : (A -> B) -> P -> Prop, exists G : (A -> B) -> P -> A, exists H : (A -> B) -> P -> B, (forall f : A -> B, forall a : P, forall y : A, ((P' f a) /\ (_103850 y (G f a))) -> _103850 y (_103852 a)) /\ ((forall f : A -> B, forall g : A -> B, forall a : P, (forall z : A, (_103850 z (_103852 a)) -> (f z) = (g z)) -> ((P' f a) = (P' g a)) /\ (((G f a) = (G g a)) /\ ((H f a) = (H g a)))) /\ (forall f : A -> B, forall a : P, (_103851 f a) -> (_103853 f a) = (@COND B (P' f a) (f (G f a)) (H f a))))).
Proof. exact (REFL (@tailadmissible A B P)). Qed.
Definition superadmissible {_138490 _138492 _138498 : Type'} : (_138490 -> _138490 -> Prop) -> ((_138490 -> _138492) -> _138498 -> Prop) -> (_138498 -> _138490) -> ((_138490 -> _138492) -> _138498 -> _138492) -> Prop := fun _103882 : _138490 -> _138490 -> Prop => fun _103883 : (_138490 -> _138492) -> _138498 -> Prop => fun _103884 : _138498 -> _138490 => fun _103885 : (_138490 -> _138492) -> _138498 -> _138492 => (@admissible _138490 _138492 _138490 Prop _138498 _103882 (fun f : _138490 -> _138492 => fun a : _138498 => True) _103884 _103883) -> @tailadmissible _138490 _138492 _138498 _103882 _103883 _103884 _103885.
Lemma superadmissible_def {_138490 _138492 _138498 : Type'} : (@superadmissible _138490 _138492 _138498) = (fun _103882 : _138490 -> _138490 -> Prop => fun _103883 : (_138490 -> _138492) -> _138498 -> Prop => fun _103884 : _138498 -> _138490 => fun _103885 : (_138490 -> _138492) -> _138498 -> _138492 => (@admissible _138490 _138492 _138490 Prop _138498 _103882 (fun f : _138490 -> _138492 => fun a : _138498 => True) _103884 _103883) -> @tailadmissible _138490 _138492 _138498 _103882 _103883 _103884 _103885).
Proof. exact (REFL (@superadmissible _138490 _138492 _138498)). Qed.
Definition psum : (prod N N) -> (N -> R) -> R := @ε ((prod N (prod N (prod N N))) -> (prod N N) -> (N -> R) -> R) (fun sum' : (prod N (prod N (prod N N))) -> (prod N N) -> (N -> R) -> R => forall _114544 : prod N (prod N (prod N N)), (forall f : N -> R, forall n : N, (sum' _114544 (@pair N N n (NUMERAL N0)) f) = (R_of_N (NUMERAL N0))) /\ (forall f : N -> R, forall m : N, forall n : N, (sum' _114544 (@pair N N n (N.succ m)) f) = (Rplus (sum' _114544 (@pair N N n m) f) (f (N.add n m))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0))))))))))).
Lemma psum_def : psum = (@ε ((prod N (prod N (prod N N))) -> (prod N N) -> (N -> R) -> R) (fun sum' : (prod N (prod N (prod N N))) -> (prod N N) -> (N -> R) -> R => forall _114544 : prod N (prod N (prod N N)), (forall f : N -> R, forall n : N, (sum' _114544 (@pair N N n (NUMERAL N0)) f) = (R_of_N (NUMERAL N0))) /\ (forall f : N -> R, forall m : N, forall n : N, (sum' _114544 (@pair N N n (N.succ m)) f) = (Rplus (sum' _114544 (@pair N N n m) f) (f (N.add n m))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))))))).
Proof. exact (REFL psum). Qed.
Definition re_Union {A : Type'} : ((A -> Prop) -> Prop) -> A -> Prop := fun _114591 : (A -> Prop) -> Prop => fun x : A => exists s : A -> Prop, (_114591 s) /\ (s x).
Lemma re_Union_def {A : Type'} : (@re_Union A) = (fun _114591 : (A -> Prop) -> Prop => fun x : A => exists s : A -> Prop, (_114591 s) /\ (s x)).
Proof. exact (REFL (@re_Union A)). Qed.
Definition re_union {A : Type'} : (A -> Prop) -> (A -> Prop) -> A -> Prop := fun _114596 : A -> Prop => fun _114597 : A -> Prop => fun x : A => (_114596 x) \/ (_114597 x).
Lemma re_union_def {A : Type'} : (@re_union A) = (fun _114596 : A -> Prop => fun _114597 : A -> Prop => fun x : A => (_114596 x) \/ (_114597 x)).
Proof. exact (REFL (@re_union A)). Qed.
Definition re_intersect {A : Type'} : (A -> Prop) -> (A -> Prop) -> A -> Prop := fun _114608 : A -> Prop => fun _114609 : A -> Prop => fun x : A => (_114608 x) /\ (_114609 x).
Lemma re_intersect_def {A : Type'} : (@re_intersect A) = (fun _114608 : A -> Prop => fun _114609 : A -> Prop => fun x : A => (_114608 x) /\ (_114609 x)).
Proof. exact (REFL (@re_intersect A)). Qed.
Definition re_null {A : Type'} : A -> Prop := fun x : A => False.
Lemma re_null_def {A : Type'} : (@re_null A) = (fun x : A => False).
Proof. exact (REFL (@re_null A)). Qed.
Definition re_universe {A : Type'} : A -> Prop := fun x : A => True.
Lemma re_universe_def {A : Type'} : (@re_universe A) = (fun x : A => True).
Proof. exact (REFL (@re_universe A)). Qed.
Definition re_subset {A : Type'} : (A -> Prop) -> (A -> Prop) -> Prop := fun _114620 : A -> Prop => fun _114621 : A -> Prop => forall x : A, (_114620 x) -> _114621 x.
Lemma re_subset_def {A : Type'} : (@re_subset A) = (fun _114620 : A -> Prop => fun _114621 : A -> Prop => forall x : A, (_114620 x) -> _114621 x).
Proof. exact (REFL (@re_subset A)). Qed.
Definition re_compl {A : Type'} : (A -> Prop) -> A -> Prop := fun _114632 : A -> Prop => fun x : A => ~ (_114632 x).
Lemma re_compl_def {A : Type'} : (@re_compl A) = (fun _114632 : A -> Prop => fun x : A => ~ (_114632 x)).
Proof. exact (REFL (@re_compl A)). Qed.
Definition istopology {A : Type'} : ((A -> Prop) -> Prop) -> Prop := fun _114641 : (A -> Prop) -> Prop => (_114641 (@re_null A)) /\ ((_114641 (@re_universe A)) /\ ((forall a : A -> Prop, forall b : A -> Prop, ((_114641 a) /\ (_114641 b)) -> _114641 (@re_intersect A a b)) /\ (forall P : (A -> Prop) -> Prop, (@re_subset (A -> Prop) P _114641) -> _114641 (@re_Union A P)))).
Lemma istopology_def {A : Type'} : (@istopology A) = (fun _114641 : (A -> Prop) -> Prop => (_114641 (@re_null A)) /\ ((_114641 (@re_universe A)) /\ ((forall a : A -> Prop, forall b : A -> Prop, ((_114641 a) /\ (_114641 b)) -> _114641 (@re_intersect A a b)) /\ (forall P : (A -> Prop) -> Prop, (@re_subset (A -> Prop) P _114641) -> _114641 (@re_Union A P))))).
Proof. exact (REFL (@istopology A)). Qed.
Definition neigh {A : Type'} : (Topology A) -> (prod (A -> Prop) A) -> Prop := fun _114654 : Topology A => fun _114655 : prod (A -> Prop) A => exists P : A -> Prop, (@open A _114654 P) /\ ((@re_subset A P (@fst (A -> Prop) A _114655)) /\ (P (@snd (A -> Prop) A _114655))).
Lemma neigh_def {A : Type'} : (@neigh A) = (fun _114654 : Topology A => fun _114655 : prod (A -> Prop) A => exists P : A -> Prop, (@open A _114654 P) /\ ((@re_subset A P (@fst (A -> Prop) A _114655)) /\ (P (@snd (A -> Prop) A _114655)))).
Proof. exact (REFL (@neigh A)). Qed.
Definition closed {A : Type'} : (Topology A) -> (A -> Prop) -> Prop := fun _114675 : Topology A => fun _114676 : A -> Prop => @open A _114675 (@re_compl A _114676).
Lemma closed_def {A : Type'} : (@closed A) = (fun _114675 : Topology A => fun _114676 : A -> Prop => @open A _114675 (@re_compl A _114676)).
Proof. exact (REFL (@closed A)). Qed.
Definition limpt {A : Type'} : (Topology A) -> A -> (A -> Prop) -> Prop := fun _114687 : Topology A => fun _114688 : A => fun _114689 : A -> Prop => forall N' : A -> Prop, (@neigh A _114687 (@pair (A -> Prop) A N' _114688)) -> exists y : A, (~ (_114688 = y)) /\ ((_114689 y) /\ (N' y)).
Lemma limpt_def {A : Type'} : (@limpt A) = (fun _114687 : Topology A => fun _114688 : A => fun _114689 : A -> Prop => forall N' : A -> Prop, (@neigh A _114687 (@pair (A -> Prop) A N' _114688)) -> exists y : A, (~ (_114688 = y)) /\ ((_114689 y) /\ (N' y))).
Proof. exact (REFL (@limpt A)). Qed.
Definition mtop {A : Type'} : (Metric A) -> Topology A := fun _114835 : Metric A => @topology A (fun S' : A -> Prop => forall x : A, (S' x) -> exists e : R, (Rlt (R_of_N (NUMERAL N0)) e) /\ (forall y : A, (Rlt (@mdist A _114835 (@pair A A x y)) e) -> S' y)).
Lemma mtop_def {A : Type'} : (@mtop A) = (fun _114835 : Metric A => @topology A (fun S' : A -> Prop => forall x : A, (S' x) -> exists e : R, (Rlt (R_of_N (NUMERAL N0)) e) /\ (forall y : A, (Rlt (@mdist A _114835 (@pair A A x y)) e) -> S' y))).
Proof. exact (REFL (@mtop A)). Qed.
Definition ball {A : Type'} : (Metric A) -> (prod A R) -> A -> Prop := fun _114846 : Metric A => fun _114847 : prod A R => fun y : A => Rlt (@mdist A _114846 (@pair A A (@fst A R _114847) y)) (@snd A R _114847).
Lemma ball_def {A : Type'} : (@ball A) = (fun _114846 : Metric A => fun _114847 : prod A R => fun y : A => Rlt (@mdist A _114846 (@pair A A (@fst A R _114847) y)) (@snd A R _114847)).
Proof. exact (REFL (@ball A)). Qed.
Definition mr1 : Metric R := @metric R (@ε ((prod R R) -> R) (fun f : (prod R R) -> R => forall x : R, forall y : R, @eq R (f (@pair R R x y)) (Rabs (Rminus y x)))).
Lemma mr1_def : mr1 = (@metric R (@ε ((prod R R) -> R) (fun f : (prod R R) -> R => forall x : R, forall y : R, @eq R (f (@pair R R x y)) (Rabs (Rminus y x))))).
Proof. exact (REFL mr1). Qed.
Definition dorder {A : Type'} : (A -> A -> Prop) -> Prop := fun _114928 : A -> A -> Prop => forall x : A, forall y : A, ((_114928 x x) /\ (_114928 y y)) -> exists z : A, (_114928 z z) /\ (forall w : A, (_114928 w z) -> (_114928 w x) /\ (_114928 w y)).
Lemma dorder_def {A : Type'} : (@dorder A) = (fun _114928 : A -> A -> Prop => forall x : A, forall y : A, ((_114928 x x) /\ (_114928 y y)) -> exists z : A, (_114928 z z) /\ (forall w : A, (_114928 w z) -> (_114928 w x) /\ (_114928 w y))).
Proof. exact (REFL (@dorder A)). Qed.
Definition tends {A B : Type'} : (B -> A) -> A -> (prod (Topology A) (B -> B -> Prop)) -> Prop := fun _114933 : B -> A => fun _114934 : A => fun _114935 : prod (Topology A) (B -> B -> Prop) => forall N' : A -> Prop, (@neigh A (@fst (Topology A) (B -> B -> Prop) _114935) (@pair (A -> Prop) A N' _114934)) -> exists n : B, (@snd (Topology A) (B -> B -> Prop) _114935 n n) /\ (forall m : B, (@snd (Topology A) (B -> B -> Prop) _114935 m n) -> N' (_114933 m)).
Lemma tends_def {A B : Type'} : (@tends A B) = (fun _114933 : B -> A => fun _114934 : A => fun _114935 : prod (Topology A) (B -> B -> Prop) => forall N' : A -> Prop, (@neigh A (@fst (Topology A) (B -> B -> Prop) _114935) (@pair (A -> Prop) A N' _114934)) -> exists n : B, (@snd (Topology A) (B -> B -> Prop) _114935 n n) /\ (forall m : B, (@snd (Topology A) (B -> B -> Prop) _114935 m n) -> N' (_114933 m))).
Proof. exact (REFL (@tends A B)). Qed.
Definition bounded {A B : Type'} : (prod (Metric A) (B -> B -> Prop)) -> (B -> A) -> Prop := fun _114960 : prod (Metric A) (B -> B -> Prop) => fun _114961 : B -> A => exists k : R, exists x : A, exists N' : B, (@snd (Metric A) (B -> B -> Prop) _114960 N' N') /\ (forall n : B, (@snd (Metric A) (B -> B -> Prop) _114960 n N') -> Rlt (@mdist A (@fst (Metric A) (B -> B -> Prop) _114960) (@pair A A (_114961 n) x)) k).
Lemma bounded_def {A B : Type'} : (@bounded A B) = (fun _114960 : prod (Metric A) (B -> B -> Prop) => fun _114961 : B -> A => exists k : R, exists x : A, exists N' : B, (@snd (Metric A) (B -> B -> Prop) _114960 N' N') /\ (forall n : B, (@snd (Metric A) (B -> B -> Prop) _114960 n N') -> Rlt (@mdist A (@fst (Metric A) (B -> B -> Prop) _114960) (@pair A A (_114961 n) x)) k)).
Proof. exact (REFL (@bounded A B)). Qed.
Definition tendsto {A : Type'} : (prod (Metric A) A) -> A -> A -> Prop := fun _114977 : prod (Metric A) A => fun _114978 : A => fun _114979 : A => (Rlt (R_of_N (NUMERAL N0)) (@mdist A (@fst (Metric A) A _114977) (@pair A A (@snd (Metric A) A _114977) _114978))) /\ (Rle (@mdist A (@fst (Metric A) A _114977) (@pair A A (@snd (Metric A) A _114977) _114978)) (@mdist A (@fst (Metric A) A _114977) (@pair A A (@snd (Metric A) A _114977) _114979))).
Lemma tendsto_def {A : Type'} : (@tendsto A) = (fun _114977 : prod (Metric A) A => fun _114978 : A => fun _114979 : A => (Rlt (R_of_N (NUMERAL N0)) (@mdist A (@fst (Metric A) A _114977) (@pair A A (@snd (Metric A) A _114977) _114978))) /\ (Rle (@mdist A (@fst (Metric A) A _114977) (@pair A A (@snd (Metric A) A _114977) _114978)) (@mdist A (@fst (Metric A) A _114977) (@pair A A (@snd (Metric A) A _114977) _114979)))).
Proof. exact (REFL (@tendsto A)). Qed.
Definition tends_num_real : (N -> R) -> R -> Prop := fun _115068 : N -> R => fun _115069 : R => @tends R N _115068 _115069 (@pair (Topology R) (N -> N -> Prop) (@mtop R mr1) N.ge).
Lemma tends_num_real_def : tends_num_real = (fun _115068 : N -> R => fun _115069 : R => @tends R N _115068 _115069 (@pair (Topology R) (N -> N -> Prop) (@mtop R mr1) N.ge)).
Proof. exact (REFL tends_num_real). Qed.
Definition convergent : (N -> R) -> Prop := fun _115124 : N -> R => exists l : R, tends_num_real _115124 l.
Lemma convergent_def : convergent = (fun _115124 : N -> R => exists l : R, tends_num_real _115124 l).
Proof. exact (REFL convergent). Qed.
Definition cauchy : (N -> R) -> Prop := fun _115129 : N -> R => forall e : R, (Rlt (R_of_N (NUMERAL N0)) e) -> exists N' : N, forall m : N, forall n : N, ((N.ge m N') /\ (N.ge n N')) -> Rlt (Rabs (Rminus (_115129 m) (_115129 n))) e.
Lemma cauchy_def : cauchy = (fun _115129 : N -> R => forall e : R, (Rlt (R_of_N (NUMERAL N0)) e) -> exists N' : N, forall m : N, forall n : N, ((N.ge m N') /\ (N.ge n N')) -> Rlt (Rabs (Rminus (_115129 m) (_115129 n))) e).
Proof. exact (REFL cauchy). Qed.
Definition lim : (N -> R) -> R := fun _115134 : N -> R => @ε R (fun l : R => tends_num_real _115134 l).
Lemma lim_def : lim = (fun _115134 : N -> R => @ε R (fun l : R => tends_num_real _115134 l)).
Proof. exact (REFL lim). Qed.
Definition subseq : (N -> N) -> Prop := fun _115139 : N -> N => forall m : N, forall n : N, (N.lt m n) -> N.lt (_115139 m) (_115139 n).
Lemma subseq_def : subseq = (fun _115139 : N -> N => forall m : N, forall n : N, (N.lt m n) -> N.lt (_115139 m) (_115139 n)).
Proof. exact (REFL subseq). Qed.
Definition mono : (N -> R) -> Prop := fun _115146 : N -> R => (forall m : N, forall n : N, (N.le m n) -> Rle (_115146 m) (_115146 n)) \/ (forall m : N, forall n : N, (N.le m n) -> Rge (_115146 m) (_115146 n)).
Lemma mono_def : mono = (fun _115146 : N -> R => (forall m : N, forall n : N, (N.le m n) -> Rle (_115146 m) (_115146 n)) \/ (forall m : N, forall n : N, (N.le m n) -> Rge (_115146 m) (_115146 n))).
Proof. exact (REFL mono). Qed.
Definition sums : (N -> R) -> R -> Prop := fun _115426 : N -> R => fun _115427 : R => tends_num_real (fun n : N => psum (@pair N N (NUMERAL N0) n) _115426) _115427.
Lemma sums_def : sums = (fun _115426 : N -> R => fun _115427 : R => tends_num_real (fun n : N => psum (@pair N N (NUMERAL N0) n) _115426) _115427).
Proof. exact (REFL sums). Qed.
Definition summable : (N -> R) -> Prop := fun _115438 : N -> R => exists s : R, sums _115438 s.
Lemma summable_def : summable = (fun _115438 : N -> R => exists s : R, sums _115438 s).
Proof. exact (REFL summable). Qed.
Definition suminf : (N -> R) -> R := fun _115443 : N -> R => @ε R (fun s : R => sums _115443 s).
Lemma suminf_def : suminf = (fun _115443 : N -> R => @ε R (fun s : R => sums _115443 s)).
Proof. exact (REFL suminf). Qed.
Definition tends_real_real : (R -> R) -> R -> R -> Prop := fun _115511 : R -> R => fun _115512 : R => fun _115513 : R => @tends R R _115511 _115512 (@pair (Topology R) (R -> R -> Prop) (@mtop R mr1) (@tendsto R (@pair (Metric R) R mr1 _115513))).
Lemma tends_real_real_def : tends_real_real = (fun _115511 : R -> R => fun _115512 : R => fun _115513 : R => @tends R R _115511 _115512 (@pair (Topology R) (R -> R -> Prop) (@mtop R mr1) (@tendsto R (@pair (Metric R) R mr1 _115513)))).
Proof. exact (REFL tends_real_real). Qed.
Definition diffl : (R -> R) -> R -> R -> Prop := fun _115541 : R -> R => fun _115542 : R => fun _115543 : R => tends_real_real (fun h : R => Rdiv (Rminus (_115541 (Rplus _115543 h)) (_115541 _115543)) h) _115542 (R_of_N (NUMERAL N0)).
Lemma diffl_def : diffl = (fun _115541 : R -> R => fun _115542 : R => fun _115543 : R => tends_real_real (fun h : R => Rdiv (Rminus (_115541 (Rplus _115543 h)) (_115541 _115543)) h) _115542 (R_of_N (NUMERAL N0))).
Proof. exact (REFL diffl). Qed.
Definition contl : (R -> R) -> R -> Prop := fun _115562 : R -> R => fun _115563 : R => tends_real_real (fun h : R => _115562 (Rplus _115563 h)) (_115562 _115563) (R_of_N (NUMERAL N0)).
Lemma contl_def : contl = (fun _115562 : R -> R => fun _115563 : R => tends_real_real (fun h : R => _115562 (Rplus _115563 h)) (_115562 _115563) (R_of_N (NUMERAL N0))).
Proof. exact (REFL contl). Qed.
Definition differentiable : (R -> R) -> R -> Prop := fun _115574 : R -> R => fun _115575 : R => exists l : R, diffl _115574 l _115575.
Lemma differentiable_def : differentiable = (fun _115574 : R -> R => fun _115575 : R => exists l : R, diffl _115574 l _115575).
Proof. exact (REFL differentiable). Qed.
Definition fld {A : Type'} : (A -> A -> Prop) -> A -> Prop := fun _117705 : A -> A -> Prop => @GSPEC A (fun GEN_PVAR_377 : A => exists x : A, @SETSPEC A GEN_PVAR_377 (exists y : A, (_117705 x y) \/ (_117705 y x)) x).
Lemma fld_def {A : Type'} : (@fld A) = (fun _117705 : A -> A -> Prop => @GSPEC A (fun GEN_PVAR_377 : A => exists x : A, @SETSPEC A GEN_PVAR_377 (exists y : A, (_117705 x y) \/ (_117705 y x)) x)).
Proof. exact (REFL (@fld A)). Qed.
Definition qoset {A : Type'} : (A -> A -> Prop) -> Prop := fun _117760 : A -> A -> Prop => (forall x : A, (@IN A x (@fld A _117760)) -> _117760 x x) /\ (forall x : A, forall y : A, forall z : A, ((_117760 x y) /\ (_117760 y z)) -> _117760 x z).
Lemma qoset_def {A : Type'} : (@qoset A) = (fun _117760 : A -> A -> Prop => (forall x : A, (@IN A x (@fld A _117760)) -> _117760 x x) /\ (forall x : A, forall y : A, forall z : A, ((_117760 x y) /\ (_117760 y z)) -> _117760 x z)).
Proof. exact (REFL (@qoset A)). Qed.
Definition poset {A : Type'} : (A -> A -> Prop) -> Prop := fun _117765 : A -> A -> Prop => (forall x : A, (@IN A x (@fld A _117765)) -> _117765 x x) /\ ((forall x : A, forall y : A, forall z : A, ((_117765 x y) /\ (_117765 y z)) -> _117765 x z) /\ (forall x : A, forall y : A, ((_117765 x y) /\ (_117765 y x)) -> x = y)).
Lemma poset_def {A : Type'} : (@poset A) = (fun _117765 : A -> A -> Prop => (forall x : A, (@IN A x (@fld A _117765)) -> _117765 x x) /\ ((forall x : A, forall y : A, forall z : A, ((_117765 x y) /\ (_117765 y z)) -> _117765 x z) /\ (forall x : A, forall y : A, ((_117765 x y) /\ (_117765 y x)) -> x = y))).
Proof. exact (REFL (@poset A)). Qed.
Definition toset {A : Type'} : (A -> A -> Prop) -> Prop := fun _117770 : A -> A -> Prop => (forall x : A, (@IN A x (@fld A _117770)) -> _117770 x x) /\ ((forall x : A, forall y : A, forall z : A, ((_117770 x y) /\ (_117770 y z)) -> _117770 x z) /\ ((forall x : A, forall y : A, ((_117770 x y) /\ (_117770 y x)) -> x = y) /\ (forall x : A, forall y : A, ((@IN A x (@fld A _117770)) /\ (@IN A y (@fld A _117770))) -> (_117770 x y) \/ (_117770 y x)))).
Lemma toset_def {A : Type'} : (@toset A) = (fun _117770 : A -> A -> Prop => (forall x : A, (@IN A x (@fld A _117770)) -> _117770 x x) /\ ((forall x : A, forall y : A, forall z : A, ((_117770 x y) /\ (_117770 y z)) -> _117770 x z) /\ ((forall x : A, forall y : A, ((_117770 x y) /\ (_117770 y x)) -> x = y) /\ (forall x : A, forall y : A, ((@IN A x (@fld A _117770)) /\ (@IN A y (@fld A _117770))) -> (_117770 x y) \/ (_117770 y x))))).
Proof. exact (REFL (@toset A)). Qed.
Definition woset {A : Type'} : (A -> A -> Prop) -> Prop := fun _117775 : A -> A -> Prop => (forall x : A, (@IN A x (@fld A _117775)) -> _117775 x x) /\ ((forall x : A, forall y : A, forall z : A, ((_117775 x y) /\ (_117775 y z)) -> _117775 x z) /\ ((forall x : A, forall y : A, ((_117775 x y) /\ (_117775 y x)) -> x = y) /\ ((forall x : A, forall y : A, ((@IN A x (@fld A _117775)) /\ (@IN A y (@fld A _117775))) -> (_117775 x y) \/ (_117775 y x)) /\ (forall s : A -> Prop, ((@subset A s (@fld A _117775)) /\ (~ (s = (@set0 A)))) -> exists x : A, (@IN A x s) /\ (forall y : A, (@IN A y s) -> _117775 x y))))).
Lemma woset_def {A : Type'} : (@woset A) = (fun _117775 : A -> A -> Prop => (forall x : A, (@IN A x (@fld A _117775)) -> _117775 x x) /\ ((forall x : A, forall y : A, forall z : A, ((_117775 x y) /\ (_117775 y z)) -> _117775 x z) /\ ((forall x : A, forall y : A, ((_117775 x y) /\ (_117775 y x)) -> x = y) /\ ((forall x : A, forall y : A, ((@IN A x (@fld A _117775)) /\ (@IN A y (@fld A _117775))) -> (_117775 x y) \/ (_117775 y x)) /\ (forall s : A -> Prop, ((@subset A s (@fld A _117775)) /\ (~ (s = (@set0 A)))) -> exists x : A, (@IN A x s) /\ (forall y : A, (@IN A y s) -> _117775 x y)))))).
Proof. exact (REFL (@woset A)). Qed.
Definition wqoset {A : Type'} : (A -> A -> Prop) -> Prop := fun _117780 : A -> A -> Prop => (forall x : A, (@IN A x (@fld A _117780)) -> _117780 x x) /\ ((forall x : A, forall y : A, forall z : A, ((_117780 x y) /\ (_117780 y z)) -> _117780 x z) /\ (forall s : A -> Prop, (@subset A s (@fld A _117780)) -> exists t : A -> Prop, (@finite_set A t) /\ ((@subset A t s) /\ (forall y : A, (@IN A y s) -> exists x : A, (@IN A x t) /\ (_117780 x y))))).
Lemma wqoset_def {A : Type'} : (@wqoset A) = (fun _117780 : A -> A -> Prop => (forall x : A, (@IN A x (@fld A _117780)) -> _117780 x x) /\ ((forall x : A, forall y : A, forall z : A, ((_117780 x y) /\ (_117780 y z)) -> _117780 x z) /\ (forall s : A -> Prop, (@subset A s (@fld A _117780)) -> exists t : A -> Prop, (@finite_set A t) /\ ((@subset A t s) /\ (forall y : A, (@IN A y s) -> exists x : A, (@IN A x t) /\ (_117780 x y)))))).
Proof. exact (REFL (@wqoset A)). Qed.
Definition chain {A : Type'} : (A -> A -> Prop) -> (A -> Prop) -> Prop := fun _117785 : A -> A -> Prop => fun _117786 : A -> Prop => forall x : A, forall y : A, ((@IN A x _117786) /\ (@IN A y _117786)) -> (_117785 x y) \/ (_117785 y x).
Lemma chain_def {A : Type'} : (@chain A) = (fun _117785 : A -> A -> Prop => fun _117786 : A -> Prop => forall x : A, forall y : A, ((@IN A x _117786) /\ (@IN A y _117786)) -> (_117785 x y) \/ (_117785 y x)).
Proof. exact (REFL (@chain A)). Qed.
Definition antichain {A : Type'} : (A -> A -> Prop) -> (A -> Prop) -> Prop := fun _117797 : A -> A -> Prop => fun _117798 : A -> Prop => (@subset A _117798 (@fld A _117797)) /\ (@pairwise A (fun x : A => fun y : A => ~ (_117797 x y)) _117798).
Lemma antichain_def {A : Type'} : (@antichain A) = (fun _117797 : A -> A -> Prop => fun _117798 : A -> Prop => (@subset A _117798 (@fld A _117797)) /\ (@pairwise A (fun x : A => fun y : A => ~ (_117797 x y)) _117798)).
Proof. exact (REFL (@antichain A)). Qed.
Definition strictly {A : Type'} : (A -> A -> Prop) -> A -> A -> Prop := fun _118450 : A -> A -> Prop => fun x : A => fun y : A => (_118450 x y) /\ (~ (_118450 y x)).
Lemma strictly_def {A : Type'} : (@strictly A) = (fun _118450 : A -> A -> Prop => fun x : A => fun y : A => (_118450 x y) /\ (~ (_118450 y x))).
Proof. exact (REFL (@strictly A)). Qed.
Definition properly {A : Type'} : (A -> A -> Prop) -> A -> A -> Prop := fun _118455 : A -> A -> Prop => fun x : A => fun y : A => (_118455 x y) /\ (~ (x = y)).
Lemma properly_def {A : Type'} : (@properly A) = (fun _118455 : A -> A -> Prop => fun x : A => fun y : A => (_118455 x y) /\ (~ (x = y))).
Proof. exact (REFL (@properly A)). Qed.
Definition inseg {A : Type'} : (A -> A -> Prop) -> (A -> A -> Prop) -> Prop := fun _122716 : A -> A -> Prop => fun _122717 : A -> A -> Prop => forall x : A, forall y : A, (_122716 x y) = ((_122717 x y) /\ (@fld A _122716 y)).
Lemma inseg_def {A : Type'} : (@inseg A) = (fun _122716 : A -> A -> Prop => fun _122717 : A -> A -> Prop => forall x : A, forall y : A, (_122716 x y) = ((_122717 x y) /\ (@fld A _122716 y))).
Proof. exact (REFL (@inseg A)). Qed.
Definition linseg {A : Type'} : (A -> A -> Prop) -> A -> A -> A -> Prop := fun _122788 : A -> A -> Prop => fun _122789 : A => fun x : A => fun y : A => (_122788 x y) /\ (@properly A _122788 y _122789).
Lemma linseg_def {A : Type'} : (@linseg A) = (fun _122788 : A -> A -> Prop => fun _122789 : A => fun x : A => fun y : A => (_122788 x y) /\ (@properly A _122788 y _122789)).
Proof. exact (REFL (@linseg A)). Qed.
Definition ordinal {A : Type'} : (A -> A -> Prop) -> Prop := fun _122800 : A -> A -> Prop => (@woset A _122800) /\ (forall x : A, (@fld A _122800 x) -> x = (@ε A (fun y : A => ~ (@properly A _122800 y x)))).
Lemma ordinal_def {A : Type'} : (@ordinal A) = (fun _122800 : A -> A -> Prop => (@woset A _122800) /\ (forall x : A, (@fld A _122800 x) -> x = (@ε A (fun y : A => ~ (@properly A _122800 y x))))).
Proof. exact (REFL (@ordinal A)). Qed.
Definition RC {A : Type'} : (A -> A -> Prop) -> A -> A -> Prop := fun R' : A -> A -> Prop => fun a0 : A => fun a1 : A => forall RC' : A -> A -> Prop, (forall a0' : A, forall a1' : A, ((R' a0' a1') \/ (a1' = a0')) -> RC' a0' a1') -> RC' a0 a1.
Lemma RC_def {A : Type'} : (@RC A) = (fun R' : A -> A -> Prop => fun a0 : A => fun a1 : A => forall RC' : A -> A -> Prop, (forall a0' : A, forall a1' : A, ((R' a0' a1') \/ (a1' = a0')) -> RC' a0' a1') -> RC' a0 a1).
Proof. exact (REFL (@RC A)). Qed.
Definition SC {A : Type'} : (A -> A -> Prop) -> A -> A -> Prop := fun R' : A -> A -> Prop => fun a0 : A => fun a1 : A => forall SC' : A -> A -> Prop, (forall a0' : A, forall a1' : A, ((R' a0' a1') \/ (SC' a1' a0')) -> SC' a0' a1') -> SC' a0 a1.
Lemma SC_def {A : Type'} : (@SC A) = (fun R' : A -> A -> Prop => fun a0 : A => fun a1 : A => forall SC' : A -> A -> Prop, (forall a0' : A, forall a1' : A, ((R' a0' a1') \/ (SC' a1' a0')) -> SC' a0' a1') -> SC' a0 a1).
Proof. exact (REFL (@SC A)). Qed.
Definition RSC {A : Type'} : (A -> A -> Prop) -> A -> A -> Prop := fun _198766 : A -> A -> Prop => @RC A (@SC A _198766).
Lemma RSC_def {A : Type'} : (@RSC A) = (fun _198766 : A -> A -> Prop => @RC A (@SC A _198766)).
Proof. exact (REFL (@RSC A)). Qed.
Definition RTC {A : Type'} : (A -> A -> Prop) -> A -> A -> Prop := fun _198890 : A -> A -> Prop => @RC A (@Relation_Operators.clos_trans A _198890).
Lemma RTC_def {A : Type'} : (@RTC A) = (fun _198890 : A -> A -> Prop => @RC A (@Relation_Operators.clos_trans A _198890)).
Proof. exact (REFL (@RTC A)). Qed.
Definition STC {A : Type'} : (A -> A -> Prop) -> A -> A -> Prop := fun _200401 : A -> A -> Prop => @Relation_Operators.clos_trans A (@SC A _200401).
Lemma STC_def {A : Type'} : (@STC A) = (fun _200401 : A -> A -> Prop => @Relation_Operators.clos_trans A (@SC A _200401)).
Proof. exact (REFL (@STC A)). Qed.
Definition RSTC {A : Type'} : (A -> A -> Prop) -> A -> A -> Prop := fun _200693 : A -> A -> Prop => @RC A (@Relation_Operators.clos_trans A (@SC A _200693)).
Lemma RSTC_def {A : Type'} : (@RSTC A) = (fun _200693 : A -> A -> Prop => @RC A (@Relation_Operators.clos_trans A (@SC A _200693))).
Proof. exact (REFL (@RSTC A)). Qed.
Definition INV {A B : Type'} : (B -> A -> Prop) -> A -> B -> Prop := fun _201638 : B -> A -> Prop => fun _201639 : A => fun _201640 : B => _201638 _201640 _201639.
Lemma INV_def {A B : Type'} : (@INV A B) = (fun _201638 : B -> A -> Prop => fun _201639 : A => fun _201640 : B => _201638 _201640 _201639).
Proof. exact (REFL (@INV A B)). Qed.
Definition RELPOW {A : Type'} : N -> (A -> A -> Prop) -> A -> A -> Prop := @ε ((prod N (prod N (prod N (prod N (prod N N))))) -> N -> (A -> A -> Prop) -> A -> A -> Prop) (fun RELPOW' : (prod N (prod N (prod N (prod N (prod N N))))) -> N -> (A -> A -> Prop) -> A -> A -> Prop => forall _201714 : prod N (prod N (prod N (prod N (prod N N)))), (forall R' : A -> A -> Prop, forall x : A, forall y : A, (RELPOW' _201714 (NUMERAL N0) R' x y) = (x = y)) /\ (forall n : N, forall x : A, forall R' : A -> A -> Prop, forall y : A, (RELPOW' _201714 (N.succ n) R' x y) = (exists z : A, (RELPOW' _201714 n R' x z) /\ (R' z y)))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0))))))))))))).
Lemma RELPOW_def {A : Type'} : (@RELPOW A) = (@ε ((prod N (prod N (prod N (prod N (prod N N))))) -> N -> (A -> A -> Prop) -> A -> A -> Prop) (fun RELPOW' : (prod N (prod N (prod N (prod N (prod N N))))) -> N -> (A -> A -> Prop) -> A -> A -> Prop => forall _201714 : prod N (prod N (prod N (prod N (prod N N)))), (forall R' : A -> A -> Prop, forall x : A, forall y : A, (RELPOW' _201714 (NUMERAL N0) R' x y) = (x = y)) /\ (forall n : N, forall x : A, forall R' : A -> A -> Prop, forall y : A, (RELPOW' _201714 (N.succ n) R' x y) = (exists z : A, (RELPOW' _201714 n R' x z) /\ (R' z y)))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))))))))).
Proof. exact (REFL (@RELPOW A)). Qed.
Definition NORMAL {A : Type'} : (A -> A -> Prop) -> A -> Prop := fun _202372 : A -> A -> Prop => fun _202373 : A => ~ (exists y : A, _202372 _202373 y).
Lemma NORMAL_def {A : Type'} : (@NORMAL A) = (fun _202372 : A -> A -> Prop => fun _202373 : A => ~ (exists y : A, _202372 _202373 y)).
Proof. exact (REFL (@NORMAL A)). Qed.
Definition CR {A : Type'} : (A -> A -> Prop) -> Prop := fun _202384 : A -> A -> Prop => forall x : A, forall y1 : A, forall y2 : A, ((_202384 x y1) /\ (_202384 x y2)) -> exists z : A, (_202384 y1 z) /\ (_202384 y2 z).
Lemma CR_def {A : Type'} : (@CR A) = (fun _202384 : A -> A -> Prop => forall x : A, forall y1 : A, forall y2 : A, ((_202384 x y1) /\ (_202384 x y2)) -> exists z : A, (_202384 y1 z) /\ (_202384 y2 z)).
Proof. exact (REFL (@CR A)). Qed.
Definition WCR {A : Type'} : (A -> A -> Prop) -> Prop := fun _202389 : A -> A -> Prop => forall x : A, forall y1 : A, forall y2 : A, ((_202389 x y1) /\ (_202389 x y2)) -> exists z : A, (@RTC A _202389 y1 z) /\ (@RTC A _202389 y2 z).
Lemma WCR_def {A : Type'} : (@WCR A) = (fun _202389 : A -> A -> Prop => forall x : A, forall y1 : A, forall y2 : A, ((_202389 x y1) /\ (_202389 x y2)) -> exists z : A, (@RTC A _202389 y1 z) /\ (@RTC A _202389 y2 z)).
Proof. exact (REFL (@WCR A)). Qed.
Definition WN {A : Type'} : (A -> A -> Prop) -> Prop := fun _202394 : A -> A -> Prop => forall x : A, exists y : A, (@RTC A _202394 x y) /\ (@NORMAL A _202394 y).
Lemma WN_def {A : Type'} : (@WN A) = (fun _202394 : A -> A -> Prop => forall x : A, exists y : A, (@RTC A _202394 x y) /\ (@NORMAL A _202394 y)).
Proof. exact (REFL (@WN A)). Qed.
Definition SN {A : Type'} : (A -> A -> Prop) -> Prop := fun _202399 : A -> A -> Prop => ~ (exists seq : N -> A, forall n : N, _202399 (seq n) (seq (N.succ n))).
Lemma SN_def {A : Type'} : (@SN A) = (fun _202399 : A -> A -> Prop => ~ (exists seq : N -> A, forall n : N, _202399 (seq n) (seq (N.succ n)))).
Proof. exact (REFL (@SN A)). Qed.
Definition TREE {A : Type'} : (A -> A -> Prop) -> Prop := fun _202404 : A -> A -> Prop => (forall y : A, ~ (@Relation_Operators.clos_trans A _202404 y y)) /\ (exists a : A, (@IN A a (@fld A _202404)) /\ (forall y : A, (@IN A y (@fld A _202404)) -> (y = a) \/ ((@Relation_Operators.clos_trans A _202404 a y) /\ (@ex1 A (fun x : A => _202404 x y))))).
Lemma TREE_def {A : Type'} : (@TREE A) = (fun _202404 : A -> A -> Prop => (forall y : A, ~ (@Relation_Operators.clos_trans A _202404 y y)) /\ (exists a : A, (@IN A a (@fld A _202404)) /\ (forall y : A, (@IN A y (@fld A _202404)) -> (y = a) \/ ((@Relation_Operators.clos_trans A _202404 a y) /\ (@ex1 A (fun x : A => _202404 x y)))))).
Proof. exact (REFL (@TREE A)). Qed.
Definition LF {A : Type'} : (A -> A -> Prop) -> Prop := fun _202409 : A -> A -> Prop => forall x : A, @finite_set A (@GSPEC A (fun GEN_PVAR_407 : A => exists y : A, @SETSPEC A GEN_PVAR_407 (_202409 x y) y)).
Lemma LF_def {A : Type'} : (@LF A) = (fun _202409 : A -> A -> Prop => forall x : A, @finite_set A (@GSPEC A (fun GEN_PVAR_407 : A => exists y : A, @SETSPEC A GEN_PVAR_407 (_202409 x y) y))).
Proof. exact (REFL (@LF A)). Qed.
Definition JOINABLE {_183549 : Type'} : (_183549 -> _183549 -> Prop) -> _183549 -> _183549 -> Prop := fun _203946 : _183549 -> _183549 -> Prop => fun _203947 : _183549 => fun _203948 : _183549 => exists u : _183549, (@RTC _183549 _203946 _203947 u) /\ (@RTC _183549 _203946 _203948 u).
Lemma JOINABLE_def {_183549 : Type'} : (@JOINABLE _183549) = (fun _203946 : _183549 -> _183549 -> Prop => fun _203947 : _183549 => fun _203948 : _183549 => exists u : _183549, (@RTC _183549 _203946 _203947 u) /\ (@RTC _183549 _203946 _203948 u)).
Proof. exact (REFL (@JOINABLE _183549)). Qed.
Definition DOWNFROM : N -> list N := @ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> N -> list N) (fun DOWNFROM' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> N -> list N => forall _232733 : prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))), ((DOWNFROM' _232733 (NUMERAL N0)) = (@nil N)) /\ (forall n : N, (DOWNFROM' _232733 (N.succ n)) = (@cons N n (DOWNFROM' _232733 n)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0))))))))))))))).
Lemma DOWNFROM_def : DOWNFROM = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> N -> list N) (fun DOWNFROM' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) -> N -> list N => forall _232733 : prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))), ((DOWNFROM' _232733 (NUMERAL N0)) = (@nil N)) /\ (forall n : N, (DOWNFROM' _232733 (N.succ n)) = (@cons N n (DOWNFROM' _232733 n)))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 N0)))))))))))))))).
Proof. exact (REFL DOWNFROM). Qed.
Definition loopcheck : (list (prod N term)) -> N -> term -> Prop := @ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) -> (list (prod N term)) -> N -> term -> Prop) (fun loopcheck' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) -> (list (prod N term)) -> N -> term -> Prop => forall _260318 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))), forall env : list (prod N term), forall x : N, (LOOPFREE env) -> forall t : term, (loopcheck' _260318 env x t) = (exists y : N, (@IN N y (free_variables_term t)) /\ ((y = x) \/ (exists s : term, (@List.In (prod N term) (@pair N term y s) env) /\ (loopcheck' _260318 env x s))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))))))))))).
Lemma loopcheck_def : loopcheck = (@ε ((prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) -> (list (prod N term)) -> N -> term -> Prop) (fun loopcheck' : (prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N)))))))) -> (list (prod N term)) -> N -> term -> Prop => forall _260318 : prod N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))), forall env : list (prod N term), forall x : N, (LOOPFREE env) -> forall t : term, (loopcheck' _260318 env x t) = (exists y : N, (@IN N y (free_variables_term t)) /\ ((y = x) \/ (exists s : term, (@List.In (prod N term) (@pair N term y s) env) /\ (loopcheck' _260318 env x s))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N (prod N N))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N (prod N N)))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N (prod N N))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N (prod N N)))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N (prod N N))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N (prod N N)) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N (prod N N) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (@pair N N (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 N0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 N0))))))))))))))))).
Proof. exact (REFL loopcheck). Qed.
