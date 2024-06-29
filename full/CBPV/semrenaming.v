Require Export cbpv.common.fin_util full.CBPV.typing common.coeffect_renaming.
From Coq Require Import FunctionalExtensionality.


(* WIP: renaming for the semantics too *)


Require Import full.CBPV.semantics.

Inductive VClos_equiv : VClos -> VClos -> Prop := 
  | equiv_Unit : 
    VClos_equiv VClosUnit VClosUnit
  | equiv_Thunk : forall m1 γ1 ρ1 M1 m2 γ2 ρ2 M2 (renamer : fin m1 -> fin m2), 
      ren_wb renamer γ1 γ2 ρ1 ρ2 ->
      M2 = ren_Comp renamer M1 ->
      VClos_equiv (VClosThunk m1 γ1 ρ1 M1) (VClosThunk m2 γ2 ρ2 M2)
  | equiv_Pair W1 W1' W2 W2' : 
      VClos_equiv W1 W1' ->
      VClos_equiv W2 W2' ->
      VClos_equiv (VClosPair W1 W2) (VClosPair W1' W2')
  | equiv_Inl W W' :
      VClos_equiv W W' -> 
      VClos_equiv (VClosInl W) (VClosInl W')
  | equiv_Inr W W' :
      VClos_equiv W W' -> 
      VClos_equiv (VClosInr W) (VClosInr W')
.

Inductive CClos_equiv : CClos -> CClos -> Prop := 
  | equiv_Ret q W W' : 
    VClos_equiv W W' -> 
    CClos_equiv (CClosRet q W) (CClosRet q W')
  | equiv_Abs q m1 γ1 ρ1 M1 m2 γ2 ρ2 M2 (renamer : fin m1 -> fin m2) : 
      ren_wb renamer γ1 γ2 ρ1 ρ2 ->
      M2 = ren_Comp (up_ren renamer) M1 ->
      CClos_equiv (CClosAbs m1 q γ1 ρ1 M1)(CClosAbs m2 q γ2 ρ2 M2)
  | equiv_CPair m1 γ1 ρ1 M1 M1' m2 γ2 ρ2 M2 M2' (renamer : fin m1 -> fin m2) : 
      ren_wb renamer γ1 γ2 ρ1 ρ2 ->
      M2 = ren_Comp renamer M1 ->
      M2' = ren_Comp renamer M1' ->
      CClos_equiv (CClosPair m1 γ1 ρ1 M1 M1') (CClosPair m2 γ2 ρ2 M2 M2').


#[global] Hint Constructors VClos_equiv CClos_equiv.

Lemma VClos_equiv_refl : forall W, VClos_equiv W W.
Proof. Admitted.

Lemma EvalVal_renaming : forall n γ Γ,
    (forall V W, (EvalVal γ Γ V W)
        -> forall m (renamer: fin n -> fin m) γ' Γ',
            ren_wb renamer γ γ' Γ Γ'
        -> exists W', VClos_equiv W W' /\ EvalVal γ' Γ' (ren_Val renamer V) W').
Proof with (eauto with effects coeffects semantics).
    induction 1; intros...
    all: cbn...
    - (*var*) destruct H2 as [H1' [H2 [H3 H4]]].
        unfold ren_match, default_or_preimage, ren_inj in *.
        specialize H1 with i as H1i. specialize H2 with i as H2i.
        exists W. split. eapply VClos_equiv_refl.
        eapply E_Var.
        rewrite <- H2i. auto.
        rewrite <- H1'. assumption.
        + intros. specialize H3 with j as [H3 | [i' H3]]; rewrite H3...
            subst. specialize H1 with i'. specialize H1' with i' as H1'.
            rewrite <- H1'. apply H1. intros Hc.
            apply f_equal with (f := renamer) in Hc. contradiction.
    - (*unit*) 
        exists VClosUnit. split; eauto.
        constructor. destruct H0 as [H1 [H2 [H3 H4]]].
        unfold ren_match, default_or_preimage, ren_inj in *.
        apply functional_extensionality. intros i.
        specialize H3 with i as [H0 | [j Hj]].
        + rewrite H0. auto with coeffects.
        + specialize H1 with j. subst. rewrite <- H1. auto.
    - (*thunk*)
      subst.
      exists (VClosThunk m γ'0 Γ' (ren_Comp renamer M)).
      split; eauto.
      eapply E_Thunk; eauto.
    - (*vpair*)
      edestruct (split_ren_add renamer γ γ1 γ2 γ' ρ Γ' ltac:(eauto) ltac:(eauto)) as 
        [γ1' [γ2' [Hg [Hg1 Hg2]]]].
      edestruct IHEvalVal1 as [W1' [Eq1 Ev1]]; eauto.
      edestruct IHEvalVal2 as [W2' [Eq2 Ev2]]; eauto.
      exists (VClosPair W1' W2').  econstructor; eauto.
      econstructor; eauto.
    - (*vinl*) 
      edestruct IHEvalVal as [W1' [Eq1 Ev1]]; eauto.
      exists (VClosInl W1').  econstructor; eauto.
      econstructor; eauto.
    - (*vinr*) 
      edestruct IHEvalVal as [W1' [Eq1 Ev1]]; eauto.
      exists (VClosInr W1').  econstructor; eauto.
      econstructor; eauto.
    - (* sub *)
      edestruct (match_ren_le renamer γ γ' γ'0 ρ Γ' ltac:(eauto) ltac:(eauto)) as 
          [γ'1 [Hs Hle]].
      clear H1.
      edestruct (IHEvalVal _ renamer γ'1) as [W1' [Eq1 Ev1]]; eauto.
      exists W1'.  econstructor; eauto.
      econstructor; eauto.
Qed.

Lemma EvalComp_renaming: forall n γ Γ, 
    (forall M T ϕ, (EvalComp γ Γ M T ϕ)
        -> forall m (renamer: fin n -> fin m) γ' Γ',
            ren_wb renamer γ γ' Γ Γ'
        -> exists T', CClos_equiv T T' /\ EvalComp γ' Γ' (ren_Comp renamer M) T' ϕ).
Proof with (eauto with effects coeffects semantics).
    induction 1; intros...
    all: cbn...
    Admitted.
(*
    - (*abs*) 
      exists (CClosAbs _ q' γ' Γ' (ren_Comp (up_ren renamer) M)). 
      split; eauto.
      econstructor. eapply H. destruct H0 as [H1 [H2 [H3 H4]]].
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
            f_equal. apply H4. auto. *)
(*    - (*app*) 
      destruct (split_ren_add renamer γ γ1 (q Q* γ2) γ'0 ρ Γ' ltac:(eauto) ltac:(eauto)) as [γ1' [γ2' [Hg [Hg1 Hg2]]]].
      destruct (split_ren_mult renamer (q Q* γ2) γ2 γ2' q ρ Γ') as [γ2'' [Hg2'' Hg2wb]]; eauto.
      edestruct IHEvalComp1 as [T1' [Eq1 Ev1]]. eauto.
      inversion Eq1. subst.
      destruct (IHEvalComp2 (S m2) (up_ren renamer0) (q .: γ3) (W .: ρ2)).      
      eapply upRen_wb.
      
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
Admitted.

*)
