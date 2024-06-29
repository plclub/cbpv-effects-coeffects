Require Import resource.CBPV.typing resource.CBPV.semtyping.

Lemma fundamental_lemma : forall n (γ : gradeVec n) (Γ : context n),
  (forall V A, VWt γ Γ V A -> SemVWt γ Γ V A) /\
  (forall M B, CWt γ Γ M B -> SemCWt γ Γ M B).
Proof with (eauto with semtyping).
  apply Wt_mutual; eauto ...
Qed.

Lemma soundness:
  (forall V A, VWt null null V A -> exists W,
    EvalVal null null V W) /\
  (forall M B, CWt null null M B ->
    exists T,
    EvalComp null null M T).
Proof with eauto.
  remember ρ_ok_null as Hok. clear HeqHok.
  split; intros;
   apply fundamental_lemma in H; firstorder.
Qed.
