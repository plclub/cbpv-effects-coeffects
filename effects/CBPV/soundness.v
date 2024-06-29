Require Import effects.CBPV.typing effects.CBPV.semtyping.

Lemma fundamental_lemma : forall {n} (Γ : context n),
  (forall V A, VWt Γ V A -> SemVWt Γ V A) /\
  (forall M B ϕ, CWt Γ M B ϕ -> SemCWt Γ M B ϕ).
Proof with (eauto with semtyping).
  apply Wt_mutual; eauto ...
Qed.

Theorem soundness : forall M A ϕ,
  CWt null M (CF A) ϕ -> exists W ϕ', EvalComp null M (CClosRet W) ϕ' /\ ϕ' E<= ϕ.
Proof.
  intros M A ϕ H. destruct (fundamental_lemma null) as [_ Hsem].
  destruct (Hsem M (CF A) ϕ H null) as [T [ϕ1 [ϕ2 [Heval [[Heq [W [Heq' _]]] Hle]]]]]; subst.
  + unfold ρ_ok. intro i. destruct i.
  + exists W. exists ϕ1. split.
    * eassumption.
    * autorewrite with effects in Hle. eassumption.
Qed.
