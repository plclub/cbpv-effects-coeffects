Require Import full.CBPV.typing full.CBPV.semtyping.

Lemma fundamental_lemma : forall n (γ : gradeVec n) (Γ : context n),
  (forall V A, VWt γ Γ V A -> SemVWt γ Γ V A) /\
  (forall M B ϕ, CWt γ Γ M B ϕ -> SemCWt γ Γ M B ϕ).
Proof with (eauto with semtyping).
  apply Wt_mutual; eauto ...
  intros. subst. eapply ST_LetZero; eauto.
Qed.

Lemma soundness :
  (forall V A, VWt null null V A -> exists W,
    EvalVal null null V W) /\
  (forall M q A ϕ, CWt null null M (CF q A) ϕ ->
    exists T ϕ1,
    EvalComp null null M T ϕ1 /\ ϕ1 E<= ϕ).
Proof with (eauto with effects).
  remember ρ_ok_null as Hok. clear HeqHok.
  split; intros; apply fundamental_lemma in H; firstorder.
  unfold SemCWt in H. unfold LRM in H.
  specialize H with null.
  apply H in Hok.
  destruct Hok as [T [ϕ1 [ϕ2 [HE [HL Hle]]]]].
  exists T, ϕ1. firstorder; try subst...
Qed.



(*=========================================*)

Lemma soundness_bot :
  (forall ϕ, ϵ E<= ϕ) ->
  (forall V A, VWt null null V A -> exists W,
    EvalVal null null V W) /\
  (forall M B ϕ, CWt null null M B ϕ ->
    exists T ϕ1,
    EvalComp null null M T ϕ1 /\ ϕ1 E<= ϕ).
Proof with (eauto with effects).
  remember ρ_ok_null as Hok. clear HeqHok.
  intros Hbot; split; intros;
   apply fundamental_lemma in H; firstorder.
  unfold SemCWt in H. unfold LRM in H.
  specialize H with null.
  apply H in Hok.
  destruct Hok as [T [ϕ1 [ϕ2 [HE [HL Hle]]]]].
  exists T, ϕ1. firstorder; try subst...
Qed.
