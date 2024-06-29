Require Export cbpv.common.fin_util full.CBPV.typing common.coeffect_renaming.
From Coq Require Import FunctionalExtensionality.

(* The typing judgment is stable under "good" renamings.
   See coeffect_renaming for the definition of ren_wb.
 *)

Lemma type_pres_renaming : forall n γ Γ,
    (forall V A, (VWt γ Γ V A)
        -> forall m (renamer: fin n -> fin m) γ' Γ',
            ren_wb renamer γ γ' Γ Γ'
        -> VWt γ' Γ' (ren_Val renamer V) A)
/\  (forall M B ϕ, (CWt γ Γ M B ϕ)
        -> forall m (renamer: fin n -> fin m) γ' Γ',
            ren_wb renamer γ γ' Γ Γ'
        -> CWt γ' Γ' (ren_Comp renamer M) B ϕ).
Proof with (eauto with effects coeffects typing).
    apply Wt_mutual; intros...
    all: cbn...
    - (*var*) destruct H as [H1 [H2 [H3 H4]]].
        unfold ren_match, default_or_preimage, ren_inj in *.
        specialize H1 with i as H1i. specialize H2 with i as H2i.
        rewrite H2i. apply T_Var.
        rewrite <- H1i. assumption.
        + intros. specialize H3 with j as [H3 | [i' H3]]; rewrite H3...
            subst. specialize e0 with i'. specialize H1 with i' as H1.
            rewrite <- H1. apply e0. intros Hc.
            apply f_equal with (f := renamer) in Hc. contradiction.
    - (*unit*) constructor. destruct H as [H1 [H2 [H3 H4]]].
        unfold ren_match, default_or_preimage, ren_inj in *.
        apply functional_extensionality. intros i.
        specialize H3 with i as [H0 | [j Hj]].
        + rewrite H0. auto with coeffects.
        + specialize H1 with j. subst. rewrite <- H1. auto.
    - (*vpair*) cbn...
        remember (split_ren_add renamer γ γ1 γ2 γ' Γ Γ' e H1) as Hsplit.
        destruct Hsplit as [γ1' [γ2' [γ'le [Hwb1 Hwb2]]]].
        eapply T_VPair; eauto.
    - (*vsub*) remember (match_ren_le renamer γ γ' γ'0 Γ Γ' g H0) as Hsub.
        destruct Hsub as [γ'1 [Hle Hwb]]. eapply T_VSub; eauto.
    - (*abs*) econstructor. eapply H. destruct H0 as [H1 [H2 [H3 H4]]].
        split; unfold ren_match, default_or_preimage, ren_inj in *; intros...
        all: try split... all: try split...
        + destruct i as [i' |]; cbn; try (apply H1)...
        + destruct i as [i' |]; cbn; try (apply H1)...
        + destruct j as [j' | ].
            * specialize H3 with j' as [H3 | [i H3]]; auto.
                right. exists (Some i). rewrite H3. auto.
            * right. exists var_zero. auto.
        + intros.
            destruct i1 as [ i1' | ], i2 as [ i2' | ]; inversion H0; auto.
            f_equal. apply H4. auto.
    - (*app*) remember (split_ren_add renamer γ γ1 (q Q* γ2) γ' Γ Γ' e H1) as Hsplit.
        clear HeqHsplit.
        destruct Hsplit as [γ1' [γ2' [Hg [Hg1 Hg2]]]].
        remember (split_ren_mult renamer
            (q Q* γ2) γ2 γ2' q Γ Γ') as Hsplit.
        clear HeqHsplit. destruct Hsplit as [γ2'' [Hg2'' Hg2wb]]; eauto.
        econstructor.
        + apply H. apply Hg1.
        + apply H0. apply Hg2wb.
        + subst. auto.
    - (*split*) remember (split_ren_add renamer γ (q Q* γ1) γ2 γ' Γ Γ' e H1) as Hsplit.
        clear HeqHsplit.
        destruct Hsplit as [γ1' [γ2' [Hg [Hg1 Hg2]]]].
        remember (split_ren_mult renamer
            (q Q* γ1) γ1 γ1' q Γ Γ') as Hsplit. clear HeqHsplit.
        destruct Hsplit as [γ1'' [Hg1'' Hg1wb]]; eauto.
        econstructor.
        + apply H. apply Hg1wb.
        + apply H0. apply upRen_wb. apply upRen_wb.
            apply Hg2.
        + subst. auto.
    - (*ret*) remember (split_ren_mult renamer γ γ1 γ' q Γ Γ' e H0)
        as Hsplit. clear HeqHsplit.
        destruct Hsplit as [γ1' [Hg1' H1]].
        econstructor; eauto.
    - (*let*)
        remember (split_ren_add renamer γ (q' Q* γ1) γ2 γ' Γ Γ' e0 H1) as Hsplit.
        clear HeqHsplit.
        destruct Hsplit as [γ1' [γ2' [Hg [Hg1 Hg2]]]]; eauto.
        remember (split_ren_mult renamer
            (q' Q* γ1) γ1 γ1' q' Γ Γ') as Hsplit. clear HeqHsplit.
        destruct Hsplit as [γ1'' [Hg1'' Hg1wb]]; eauto.
            econstructor; eauto.
            + apply H0. apply upRen_wb. apply Hg2.
            + subst. auto.
    - (*seq*) remember (split_ren_add renamer γ γ1 γ2 γ' Γ Γ' e H1) as Hsplit.
        clear HeqHsplit.
        destruct Hsplit as [γ1' [γ2' [Hg [Hg1 Hg2]]]].
        econstructor; eauto.
    - (*case*) remember (split_ren_add renamer γ (q Q* γ1) γ2 γ' Γ Γ' e H2)
        as Hsplit. clear HeqHsplit.
        destruct Hsplit as [γ1' [γ2' [Hg [Hg1 Hg2]]]].
        remember (split_ren_mult renamer
            (q Q* γ1) γ1 γ1' q Γ Γ') as Hsplit. clear HeqHsplit.
        destruct Hsplit as [γ1'' [Hg1'' Hg1wb]]; eauto.
        econstructor; eauto.
        + apply H0. apply upRen_wb. apply Hg2.
        + apply H1. apply upRen_wb. apply Hg2.
        + subst. eauto.
    - (*tick*) econstructor; auto. destruct H as [H1 [H2 [H3 H4]]].
      unfold ren_match, default_or_preimage, ren_inj in *.
      apply functional_extensionality. intros i. specialize H3 with i.
      destruct H3 as [Heq | [j Hj]].
      + subst. auto.
      + specialize H1 with j. rewrite Hj. subst. rewrite <- H1. auto.
    - (*csub*) remember (match_ren_le renamer γ γ' γ'0 Γ Γ' g H0) as Hsub.
        destruct Hsub as [γ'1 [Hle Hwb]]. eapply T_CSub; eauto.
    - (*letzero*) assert (e' : γ = Qzero Q* γ1 Q+ γ2). {  rewrite gradeVecScaleByZero. rewrite gradeVecAddLId. auto. }
      remember (split_ren_add renamer γ (Qzero Q* γ1) γ2 γ' Γ Γ' e' H1) as Hsplit.
      clear HeqHsplit.
      destruct Hsplit as [γ1' [γ2' [Hg [Hg1 Hg2]]]]; eauto.
      remember (split_ren_mult renamer
                  (Qzero Q* γ1) γ1 γ1' Qzero Γ Γ') as Hsplit. clear HeqHsplit.
      destruct Hsplit as [γ1'' [Hg1'' Hg1wb]]; eauto.
      eapply T_LetZero with (γ := γ') (γ1 := γ1''); eauto.
      + apply H0. apply upRen_wb.
        rewrite Hg1''. rewrite gradeVecScaleByZero. rewrite gradeVecAddLId. auto.
Qed.




