Require Export common.coeffects.

Axiom Qnontrivial : Qone <> Qzero.
Axiom Qsumzero : forall q1 q2, Qle Qzero (Qadd q1 q2) ->
  q1 = Qzero /\ q2 = Qzero.
Axiom Qprodzero : forall q1 q2, Qmult q1 q2 = Qzero ->
  q1 = Qzero \/ q2 = Qzero.

Lemma Q_one_lt_zero : Qle Qzero Qone -> False.
Proof.
  intros H.
  rewrite <- Qadd_lident with (a := Qone) in H.
  apply Qsumzero in H as [_ H]. apply Qnontrivial.
  assumption.
Qed.

Lemma Q_lt_zero : forall q, Qle Qzero q -> q = Qzero.
Proof.
  intros q H.
  rewrite <- Qadd_lident in H.
  apply Qsumzero in H as [_ H]. auto.
Qed.

Lemma q_or_1_lt1 : forall q,
  Qle q Qone -> q_or_1 q = q.
Proof.
  intros.
  destruct (Qeqb q Qzero) eqn: Hq0.
  - rewrite <- Qeqb_eq in Hq0. subst.
    exfalso. apply Q_one_lt_zero. auto.
  - unfold q_or_1. rewrite Hq0. auto.
Qed.
