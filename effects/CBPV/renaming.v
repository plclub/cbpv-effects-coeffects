Require Export cbpv.common.fin_util effects.CBPV.typing.

(* This lemma states that the typing judgement is stable under renaming.  In
   other words, given some renaming function `renamer` that takes a typing
   context of scope `n` to one of scope `m`, we can apply the renamer to convert 
   values and computations from the former to the latter scope.

*)
Lemma type_pres_renaming : forall n Γ,
    (forall V A, (VWt Γ V A)
        -> forall m (renamer: fin n -> fin m) Γ',
            ren_match renamer Γ Γ'
        -> VWt Γ' (ren_Val renamer V) A)
/\  (forall M B ϕ, (CWt Γ M B ϕ)
        -> forall m (renamer: fin n -> fin m) Γ',
            ren_match renamer Γ Γ'
        -> CWt Γ' (ren_Comp renamer M) B ϕ).
Proof with (eauto with effects typing).
    apply Wt_mutual; intros...
    all: cbn...
    all: unfold ren_match in *.
    - (*var*) 
        specialize H with i as Hi.
        rewrite Hi. econstructor.
    - (*abs*) econstructor.
        apply H. intros.
        destruct i as [i' |]; auto.
        simpl. apply H0.
    - (*split*) eapply T_Split with
        (A1 := A1) (A2 := A2).
        + apply H. auto.
        + apply H0. destruct i as [[i''|]|]; auto.
            simpl. apply H1.
    - (*let*) eapply T_Let with
        (A := A)
        (ϕ1 := ϕ1)
        (ϕ2 := ϕ2); auto. apply H0.
        intros [i' |]; auto. simpl. apply H1.
    - (*case*) eapply T_Case with
        (A1 := A1)
        (A2 := A2); auto.
        + apply H0. intros [i' |]; auto. apply H2.
        + apply H1. intros [i' |]; auto. apply H2.
Qed.
