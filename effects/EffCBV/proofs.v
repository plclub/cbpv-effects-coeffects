Require Export effects.EffCBV.translation effects.CBPV.renaming.

Theorem translation_correct :
    forall n (Γ : contextL n) e T ϕ,
    Wt Γ e T ϕ ->
    CWt (translateContext Γ)
        (translateTerm e) (CF (translateType T)) ϕ.
Proof with (autorewrite with trans effects);
    (eauto with trans typing effects).
    intros n Γ e T ϕ H.
    induction H; cbn.
    - (*var*) econstructor...
    - (*abs*) econstructor. econstructor.
        econstructor.
        rewrite contextTranslationHom in IHWt...
    - (*app*) subst. rewrite eff_assoc.
        eapply T_Let with
        (A := translateType (Abs T1 ϕ3 T2)); eauto with effects.
        + eapply T_Let. eapply type_pres_renaming... eapply ren_match_shift.
          cbn. eapply T_App with (A := translateType T1).
          * econstructor. econstructor.
          * econstructor.
    - (*ret*) econstructor...
    - (*seq*) subst. eapply T_Let... eapply T_Seq.
        + econstructor.
        + eapply type_pres_renaming...
            apply ren_match_shift.
    - (*pair*) subst. eapply T_Let...
        + rewrite <- eff_idR. eapply T_Let.
          * eapply type_pres_renaming... eapply ren_match_shift.
          * econstructor... apply T_VPair; econstructor...
    - (*split*) subst. apply T_Let with
        (A := translateType (Pair T1 T2))...
        apply T_Split
            with (A1 := translateType T1)
            (A2 := translateType T2).
            + cbn. econstructor...
            + eapply type_pres_renaming...
                cbn...
                apply ren_match_up2_ren'.
    - (*inl*) rewrite <- eff_idR. eapply T_Let...
        econstructor. econstructor.
        econstructor.
    - (*inr*) rewrite <- eff_idR. eapply T_Let...
        econstructor. econstructor. econstructor.
    - (*case*) subst. eapply T_Let; subst...
        eapply T_Case with
        (A1 := translateType T1)
        (A2 := translateType T2)...
        + econstructor.
        + eapply type_pres_renaming...
            rewrite contextTranslationHom.
            apply ren_match_up_ren'.
        + eapply type_pres_renaming...
            rewrite contextTranslationHom.
            apply ren_match_up_ren'.
   - (* sub *) eapply T_SubEff...
   - (* tick *) econstructor.
Qed.
