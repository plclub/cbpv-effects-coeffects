Require Export resource.CBN.translation.

Theorem translation_correct :
    forall n (γ : gradeVec n) (Γ : contextL n) e T,
    Wt γ Γ e T ->
    CWt γ (translateContext Γ)
        (translateTerm e) (translateType T).
Proof with (autorewrite with coeffects trans);
    (eauto with coeffects trans renaming typing).
    intros n γ Γ e T H.
    induction H; cbn.
    - (*var*) econstructor...
    - (*abs*) econstructor...
        rewrite contextTranslationHom in IHWt...
    - (*app*) econstructor...
    - (*unit*) econstructor...
    - (*seq*) econstructor...
        apply T_Seq with (γ1 := Qone .: 0s)
            (γ2 := Qzero .: γ2)...
        + econstructor... solve_js0.
        + eapply type_pres_renaming...
        + auto...
    - (*inl*) econstructor...
    - (*inr*) econstructor...
    - (*with*) econstructor...
    - (*fst*) econstructor...
    - (*snd*) econstructor...
    - (*case*)
        eapply T_Let with
        (γ2 := γ2); subst... fold translateType.
        all: rewrite q_or_1_lt1...
        eapply T_Case with
        (γ1 := Qone .: 0s) (γ2 := Qzero .: γ2)
        (A1 := VThunk (translateType T1))
        (A2 := VThunk (translateType T2))...
        + econstructor... solve_js0.
        + eapply type_pres_renaming...
            rewrite contextTranslationHom...
        + eapply type_pres_renaming...
            rewrite contextTranslationHom.
            eapply up_ren_wb...
    - (*box*) econstructor...
    - (*unbox*) eapply T_Let with (γ2 := γ2)...
        fold translateType.
        rewrite contextTranslationHom in IHWt2.
        auto.
    - (*sub*) econstructor...
Qed.