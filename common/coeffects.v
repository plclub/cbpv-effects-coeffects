Require Export cbpv.autosubst2.fintype.
From Coq Require Import FunctionalExtensionality.

(* An initial axiomatization of a partially ordered semiring with decidable
   equality.

   Note that some of our proofs do not require all of the usual semiring
   axioms, such as associativity and commutativity, but the availability of 
   these properties will make the type system more expressive

*)

Structure POSR : Type := mkPOSR {
  (* carrier type *)
  A : Set;  

  (* semiring *)
  zero : A;  
  one : A;   
  add : A -> A -> A; 
  mult : A -> A -> A;

  (* semiring properties for identity elements *)
  add_lident : forall (a : A), add zero a = a;
  add_rident : forall (a : A), add a zero = a;
  mult_lident : forall (a : A), mult one a = a;
  mult_rident : forall (a : A), mult a one = a;
  zero_rannihilates : forall (a : A), mult a zero = zero;
  zero_lannihilates : forall (a : A), mult zero a = zero;

  (* partial order *)
  le : A -> A -> Prop;
  le_refl : forall (a : A), le a a;
  le_trans : forall (a b c : A), le a b -> le b c -> le a c;

  (* decidable equality, must agree with Coq's propositional equality *)
  eqb : A -> A -> bool;
  eqb_eq : forall (a1 a2 : A), a1 = a2 <-> eqb a1 a2 = true;

  (* addition preserves order *)
  le_addl : forall (a1 a2 a3 : A), le a1 a2 -> le (add a3 a1) (add a3 a2);
  le_addr : forall (a1 a2 a3 : A), le a1 a2 -> le (add a1 a3) (add a2 a3)
}.

(* Axiomatization of an instance of this structure *)
Parameter Q_POSR : POSR.
Notation Q := (A Q_POSR).
Notation Qzero := (zero Q_POSR).
Notation Qone := (one Q_POSR).
Notation Qadd := (add Q_POSR).
Notation Qmult := (mult Q_POSR).
Notation Qle := (le Q_POSR).
Notation Qle_refl := (le_refl Q_POSR).
Notation Qle_trans := (le_trans Q_POSR).
Notation Qadd_lident := (add_lident Q_POSR).
Notation Qadd_rident := (add_rident Q_POSR).
Notation Qmult_lident := (mult_lident Q_POSR).
Notation Qmult_rident := (mult_rident Q_POSR).
Notation Qzero_rannihilates := (zero_rannihilates Q_POSR).
Notation Qzero_lannihilates := (zero_lannihilates Q_POSR).
Notation Qeqb := (eqb Q_POSR).
Notation Qeqb_eq := (eqb_eq Q_POSR).
Notation Qle_addl := (le_addl Q_POSR).
Notation Qle_addr := (le_addr Q_POSR).

Create HintDb coeffects.
#[export]Hint Resolve
  le_refl le_trans : coeffects.
#[export]Hint Rewrite
  Qadd_lident Qadd_rident Qmult_lident Qmult_rident
  Qzero_lannihilates Qzero_rannihilates : coeffects.


(* Grade Vectors  *)

Definition gradeVec n := fin n -> Q.

(* pointwise addition of grade vectors *)
Definition gradeVecAdd {n} (γ1 γ2 : gradeVec n) :=
  fun (i : fin n) => Qadd (γ1 i) (γ2 i).

(* scalar multiplication of grade vectors *)
Definition gradeVecScale {n} (q : Q) (γ : gradeVec n) :=
  fun (i : fin n) => Qmult q (γ i).

(* the ordering on grades lifted to an ordering on grade vectors *)
Definition gradeVecLe {n} (γ1 γ2 : gradeVec n) : Prop :=
  forall (i : fin n), Qle (γ1 i) (γ2 i).

(* A grade vector of length n containing all 0s *)
Definition gradeVecZero (n : nat) : gradeVec n :=
  fun (i : fin n) => Qzero.
Arguments gradeVecZero {n}.

(* A grade vector of length n containing all 1s *)
Definition gradeVecOne (n : nat) : gradeVec n :=
    fun (i : fin n) => Qone.
Arguments gradeVecOne {n}.

Notation "γ1 'Q+' γ2" := (gradeVecAdd γ1 γ2) (at level 60).
Notation "q 'Q*' γ" := (gradeVecScale q γ) (at level 50).
Notation "γ1 'Q<=' γ2" := (gradeVecLe γ1 γ2) (at level 70).
Notation "0s" := gradeVecZero (at level 70).
Notation "1s" := gradeVecOne (at level 70).

#[export]Hint Unfold
  gradeVecAdd gradeVecScale gradeVecLe
  gradeVecOne gradeVecZero : coeffects.

(* The ordering on grade vectors is reflexive*)
Lemma gradeVecLeRefl (n : nat) :
  forall (γ : gradeVec n), γ Q<= γ.
Proof. eauto with coeffects. Qed.

(* The ordering on grade vectors is transitive*)
Lemma gradeVecLeTrans (n : nat) :
  forall (γ0 γ1 γ2 : gradeVec n),
    (γ0 Q<= γ1) /\ (γ1 Q<= γ2) ->
      γ0 Q<= γ2.
Proof.
  intros γ0 γ1 γ2 [H1 H2] i.
  eapply Qle_trans; eauto.
Qed.

(* prepending ordered terms preserves ordering on grade vectors *)
Lemma gradeVecLeCons (n : nat) :
  forall q1 q2 (γ0 γ1 : gradeVec n),
    Qle q1 q2 ->
    γ0 Q<= γ1 ->
    (q1 .: γ0) Q<= (q2 .: γ1).
Proof.
  intros q1 q2 γ0 γ1 Hq H [i | ]; eauto.
Qed.

(* the zero vector is a left (additive) identity *)
Lemma gradeVecAddLId (n : nat) :
  forall (γ : gradeVec n),
    (gradeVecZero Q+ γ) = γ.
Proof.
  intros. apply functional_extensionality. intros i.
  unfold gradeVecAdd. rewrite Qadd_lident. reflexivity.
Qed.

(* the zero vector is a right (additive) identity *)
Lemma gradeVecAddRId (n : nat) :
  forall (γ : gradeVec n),
    (γ Q+ gradeVecZero) = γ.
Proof.
  intros γ. apply functional_extensionality. intros i.
  unfold gradeVecAdd. rewrite Qadd_rident. reflexivity.
Qed.

(* 1 is a scalar-multiplication identity *)
Lemma gradeVecScaleId (n : nat) :
  forall (γ : gradeVec n),
    Qone Q* γ = γ.
Proof.
  intros γ. apply functional_extensionality. intros i.
  unfold gradeVecScale. rewrite Qmult_lident. reflexivity.
Qed.

(* addition and scons commute *)
Lemma gradeVecAddCons : forall n (q1 q2 : Q) (γ1 γ2 : gradeVec n),
  (q1 .: γ1 Q+ q2 .: γ2) = (Qadd q1 q2) .: (γ1 Q+ γ2).
Proof.
  intros n q1 q2 γ1 γ2. apply functional_extensionality.
  intros [k | ]; unfold gradeVecAdd; cbn; reflexivity.
Qed.

(* scalar multiplication and scons commute *)
Lemma gradeVecScaleCons : forall n (q1 q2 : Q) (γ : gradeVec n),
  q1 Q* (q2 .: γ) = (Qmult q1 q2) .: (q1 Q* γ).
Proof.
  intros n q1 q2 γ. apply functional_extensionality.
  intros [k | ]; unfold gradeVecScale; cbn; reflexivity.
Qed.

(* the zero vector does not change under scalar multiplication *)
Lemma gradeVecScaleZero : forall n (q : Q),
  q Q* (0s : gradeVec n) = 0s.
Proof.
  intros n q. apply functional_extensionality.
  intros i. unfold gradeVecZero. unfold gradeVecScale.
  rewrite Qzero_rannihilates. reflexivity.
Qed.

(* 0 is a (scalar-multiplicative) annihilator for grade vectors *)
Lemma gradeVecScaleByZero : forall n (γ : gradeVec n),
  Qzero Q* γ = 0s.
Proof.
  intros n γ. apply functional_extensionality.
  intros i. unfold gradeVecScale.
  rewrite Qzero_lannihilates. reflexivity.
Qed.

(* prepending 0 to a zero vector produces another zero vector *)
Lemma gradeVecCons0s : forall n,
    Qzero .: (0s : gradeVec n) = 0s.
Proof.
  intros. apply functional_extensionality. intros [i | ]; auto.
Qed.

(* Left addition respects ordering *)
Lemma gradeVecAddLLe : forall n (γ1 γ2 γ2' : gradeVec n),
  γ2 Q<= γ2' ->
  γ1 Q+ γ2 Q<= γ1 Q+ γ2'.
Proof.
  intros. intros i. unfold gradeVecAdd. apply Qle_addl. auto.
Qed.

(* Right addition respects ordering *)
Lemma gradeVecAddRLe : forall n (γ1 γ1' γ2 : gradeVec n),
  γ1 Q<= γ1' ->
  γ1 Q+ γ2 Q<= γ1' Q+ γ2.
Proof.
  intros. intros i. unfold gradeVecAdd. apply Qle_addr. auto.
Qed.

(* Equality*)

(* grade equality is (propositionally) decidable *)
Lemma Qeq_dec : forall (q1 q2 : Q), q1 = q2 \/ q1 <> q2.
Proof.
  intros. destruct (Qeqb q1 q2) eqn: Heq.
  - left. apply Qeqb_eq. auto.
  - right. intros H. rewrite Qeqb_eq in H. rewrite H in Heq. discriminate.
Qed.

(* grade inequality is (propositionally) decidable *)
Lemma Qeqb_neq : forall (q1 q2 : Q), q1 <> q2 <-> Qeqb q1 q2 = false.
Proof.
  intros. split; intros.
  - destruct (Qeqb q1 q2) eqn: Heq; auto.
    rewrite <- Qeqb_eq in Heq. contradiction.
  - intros Heq. rewrite Qeqb_eq in Heq.
    rewrite H in Heq. discriminate.
Qed.

(* q || 1 - see Resource section of paper *)

Definition q_or_1 (q : Q) : Q :=
  if Qeqb q Qzero then Qone else q.

(* q || 1 is never 0 except in the trivial semiring *)
Lemma q_or_1_neq_0 : forall q,
  q_or_1 q <> Qzero \/ Qone = Qzero.
Proof.
  intros.
  destruct (Qeqb Qone Qzero) eqn: Eq_1_0.
  - right. apply Qeqb_eq. assumption.
  - left. rewrite Qeqb_neq in *. unfold q_or_1.
    destruct (Qeqb q Qzero) eqn: Eq_q_0; auto.
Qed.

(* q || 1 is an idempotent operation *)
Lemma q_or_1_idempotent : forall q,
  q_or_1 (q_or_1 q) = q_or_1 q.
Proof.
  intros. unfold q_or_1. destruct (Qeqb q Qzero) eqn: H.
  - destruct (Qeqb Qone Qzero); auto.
  - rewrite H. auto.
Qed.

Lemma q_or_1_1 : q_or_1 Qone = Qone.
Proof.
  unfold q_or_1. destruct (Qeqb Qone Qzero); auto.
Qed.

(* q' <= q and q' /= 0, or we are in the trivial semiring*)
Definition nonzero_lb (q' : Q) (q : Q) :=
  (Qle q' q /\ q' <> Qzero) \/ Qzero = Qone.

#[export]Hint Resolve
  gradeVecLeRefl gradeVecLeTrans
  gradeVecLeCons gradeVecAddLId gradeVecAddRId
  gradeVecScaleId gradeVecAddCons
  gradeVecAddLLe q_or_1_neq_0 : coeffects.
#[export]Hint Rewrite
  gradeVecLeCons gradeVecAddCons gradeVecScaleCons
  gradeVecAddLId gradeVecScaleByZero gradeVecScaleZero
  gradeVecAddRId gradeVecScaleId gradeVecCons0s
  q_or_1_idempotent q_or_1_1 : coeffects.

(* Tactics for reasoning about coeffects *)

(* solve goals in translation proofs using T-Var 
    where variable corresponds to index 0 *)
Ltac solve_js0 := intros j Hj; remember j as k;
    subst; destruct j; autorewrite with coeffects;
    eauto with coeffects; contradiction.

(* solve goals in translation proofs using T-Var 
    where variable corresponds to index 1 *)
Ltac solve_js1 := intros j Hj; remember j as k;
    subst; destruct j as [j'|]; autorewrite with coeffects;
    eauto with coeffects; remember j' as k'; destruct j'; subst;
    autorewrite with coeffects; eauto with coeffects; contradiction.


