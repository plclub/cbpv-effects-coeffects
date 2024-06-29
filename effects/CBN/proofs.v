Require Export effects.CBN.translation effects.CBPV.renaming.

Theorem translation_correct :
    forall n (Γ : contextL n) e T,
    Wt Γ e T ->
    CWt (translateContext Γ)
        (translateTerm e) (translateType T) ϵ.
Proof with (autorewrite with effects);
    (eauto with trans typing effects).
    intros n Γ e T H.
    induction H; cbn; econstructor...
    - (*var*) econstructor.
    - (*thunk*) rewrite <- contextTranslationHom.
        auto.
    - (*seq*) econstructor.
        rewrite <- eff_idL. econstructor...
            econstructor... econstructor...
            eapply type_pres_renaming with
                (Γ := translateContext Γ); auto.
            apply ren_match_shift.
    - (*sum*) rewrite <- eff_idL. econstructor...
        fold translateType.
        eapply T_Case with
            (A1 := VThunk ϵ (translateType T1))
            (A2 := VThunk ϵ (translateType T2)).
        + econstructor.
        + eapply type_pres_renaming
            with (Γ := translateContext (T1 .: Γ)); auto.
            rewrite contextTranslationHom.
            apply ren_match_up_ren'.
        + eapply type_pres_renaming
            with (Γ := translateContext (T2 .: Γ)); auto.
            rewrite contextTranslationHom.
            apply ren_match_up_ren'.
    - (*ret*) subst...
    - (*bind*) econstructor. cbn in *.
        eapply T_SubEff with (ϕ := (ϵ E+ ϕ1) E+ ϕ2).
        eapply T_Let
            with
            (ϕ1 := ϵ E+ ϕ1) (ϕ2 := ϕ2)
            (A := VThunk ϵ (translateType T1));
            eauto with effects.
        + eapply T_Let with
            (A := VThunk ϕ1 (CF (VThunk ϵ (translateType T1))));
            eauto with effects.
            econstructor. econstructor.
        + rewrite <- contextTranslationHom.
            eapply T_SubEff with (ϕ := ϵ E+ ϕ2).
            eapply T_Let with
            (A :=  VThunk ϕ2 (CF (VThunk ϵ (translateType T2))))
            (ϕ1 := ϵ)
            (ϕ2 := ϕ2); eauto with effects.
            econstructor. econstructor.
            rewrite eff_idL...
        + autorewrite with effects. subst. eauto with effects.
    - (*coerce*) econstructor.
      eapply T_SubEff.
      eapply T_Let with
        (A := VThunk ϕ (CF (VThunk ϵ (translateType T)))) (ϕ1 := ϵ) (ϕ2 := ϕ).
      + cbn in *. eassumption.
      + econstructor. econstructor...
      + autorewrite with effects. eauto with effects.
    - (*tick*) econstructor.
        eapply T_SubEff with (ϕ := tick E+ ϵ).
        eapply T_Let with
            (ϕ1 := tick)
            (ϕ2 := ϵ)
            (A := VUnit); eauto with effects.
            + econstructor; eauto.
            + econstructor. econstructor. econstructor.
                econstructor.
            + rewrite eff_idR...
Qed.
