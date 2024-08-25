Require Export effects.CBPV.semantics effects.CBPV.typing.

Definition LRM {n} (LR : CompTy -> CClos -> E -> Prop) (B : CompTy) (ρ : env n) (M : Comp n) (ϕ : E) :=
  exists T ϕ1 ϕ2 , EvalComp ρ M T ϕ1 /\ LR B T ϕ2 /\ (ϕ1 E+ ϕ2 E<= ϕ).

Fixpoint LRV (A : ValTy) (W : VClos) : Prop :=
    match A with
    | VUnit => W = VClosUnit
    | VThunk ϕ B => exists m ρ M,
      W = VClosThunk m ρ M /\ LRM LRC B ρ M ϕ
    | VPair A1 A2 => exists W1 W2,
      W = VClosPair W1 W2 /\ LRV A1 W1 /\ LRV A2 W2
    | VSum A1 A2 => exists W',
      (W = VClosInl W' /\ LRV A1 W')
      \/ (W = VClosInr W' /\ LRV A2 W')
    end
  with LRC (B : CompTy) (T : CClos) (ϕ : E) :=
    match B with
    | CF A => ϕ = ϵ /\ (exists W, T = CClosRet W /\ LRV A W)
    | CPair B1 B2 => exists m ρ M1 M2, T = CClosPair m ρ M1 M2 /\
                                     LRM LRC B1 ρ M1 ϕ /\
                                     LRM LRC B2 ρ M2 ϕ
    | CAbs A B => exists m ρ M, T = CClosAbs m ρ M /\
      (forall W, LRV A W -> LRM LRC B (W .: ρ) M ϕ)
    end.

Definition ρ_ok {n} ρ Γ := forall (i : fin n), (LRV (Γ i) (ρ i)).

Definition SemVWt {n} (Γ : context n) V A :=
  forall ρ, ρ_ok ρ Γ -> exists W, EvalVal ρ V W /\ LRV A W.

Definition SemCWt {n} (Γ : context n) M B ϕ :=
  forall ρ, ρ_ok ρ Γ -> LRM LRC B ρ M ϕ.

Lemma ρ_ok_cons n ρ (Γ : context n) W A
  (H1 : LRV A W)
  (H2 : ρ_ok ρ Γ) :
  ρ_ok (W .: ρ) (A .: Γ).
Proof.
  unfold ρ_ok. intros. unfold scons.
  destruct i; auto; contradiction.
Qed.

Lemma ρ_ok_cons2 n ρ (Γ : context n) W1 W2 A1 A2
  (H1 : LRV A1 W1)
  (H2 : LRV A2 W2)
  (H3 : ρ_ok ρ Γ) :
  ρ_ok (W1 .: (W2 .: ρ)) (A1 .: (A2 .: Γ)).
Proof. apply ρ_ok_cons; try apply ρ_ok_cons; assumption. Qed.

Section SemTyping.

Context {n : nat} (Γ : context n) (ϕ : E).

(* Semantic typing rules. *)

(* Values*)
  Lemma ST_Var i :
    (* ------------------------ *)
    SemVWt Γ (var_Val i) (Γ i).
  Proof.
    unfold SemVWt. intros ρ H. unfold ρ_ok in H.
    exists (ρ i). split.
      + apply E_Var; auto.
      + apply H.
  Qed.

  Lemma ST_Thunk M B :
    SemCWt Γ M B ϕ ->
    (* ------------------------------ *)
    SemVWt Γ (vThunk M) (VThunk ϕ B).
  Proof.
    unfold SemCWt, SemVWt. intros IH ρ H.
    specialize IH with ρ.
    apply IH in H as [T [ϕ1 [ϕ2 [HE [HA Hle]]]]].
    eexists. split.
    - constructor.
    - repeat eexists; eassumption.
  Qed.

  Lemma ST_Unit :
    (* ------------------- *)
    SemVWt Γ vUnit VUnit.
  Proof.
    unfold SemVWt. intros ρ H. eexists. split. eauto with semantics. reflexivity.
  Qed.

  Lemma ST_VPair V1 V2 A1 A2 :
    SemVWt Γ V1 A1 ->
    SemVWt Γ V2 A2 ->
    (* ------------------------------ *)
    SemVWt Γ (vPair V1 V2) (VPair A1 A2).
  Proof.
    unfold SemVWt. intros IH1 IH2 ρ H.
    specialize IH1 with ρ. apply IH1 in H as IH1'.
      destruct IH1' as [W1 [H1E H1L]]. clear IH1.
    specialize IH2 with ρ. apply IH2 in H as IH2'.
      destruct IH2' as [W2 [H2E H2L]]. clear IH2.
    eexists. split.
    econstructor; eassumption.
    firstorder.
  Qed.

  Lemma ST_Inl V A1 A2 :
    SemVWt Γ V A1 ->
    (* ----------------------- *)
    SemVWt Γ (vInl V) (VSum A1 A2).
  Proof.
    unfold SemVWt. intros IH ρ H.
    specialize IH with ρ. apply IH in H as [W [HE HL]].
    exists (VClosInl W). split.
    - constructor. assumption.
    - exists W. left. split; auto.
  Qed.

  Lemma ST_Inr V A1 A2 :
    SemVWt Γ V A2 ->
    (* ----------------------- *)
    SemVWt Γ (vInr V) (VSum A1 A2).
  Proof.
    unfold SemVWt. intros IH ρ H.
    specialize IH with ρ. apply IH in H as [W [HE HL]].
    exists (VClosInr W). split.
    - constructor. assumption.
    - exists W. auto.
  Qed.

(*Computations*)

  Lemma ST_Abs A M B :
    SemCWt (A .: Γ) M B ϕ ->
    (* ------------- *)
    SemCWt Γ (cAbs M) (CAbs A B) ϕ.
  Proof.
    unfold SemCWt. intros IH ρ H.
    unfold LRM. exists (CClosAbs n ρ M), ϵ, ϕ. split; try split.
    + econstructor. auto.
    + simpl. exists n, ρ, M; firstorder.
      apply IH. apply ρ_ok_cons; assumption.
    + rewrite eff_idL. apply subeff_refl.
Qed.

  Lemma ST_App M A B V :
    SemCWt Γ M (CAbs A B) ϕ ->
    SemVWt Γ V A ->
    (* --------------- *)
    SemCWt Γ (cApp M V) B ϕ.
  Proof.
    unfold SemCWt in *; unfold SemVWt in *; intros.
    unfold LRM.
    apply H in H1 as Hm. apply H0 in H1 as Hv.
    destruct Hv as [W [HWE HWL]].
    destruct Hm as [T' [ϕ1' [ϕ2' [He [HLRC Heff]]]]].
    destruct HLRC as [m [ρ' [M' [HT' H']]]].
    apply H' in HWL as [T [ϕ1 [ϕ2 [HTE [HTL Heff']]]]].
    exists T. eexists. eexists.
    split; try split; auto.
    + econstructor; subst; eauto.
    + eauto.
    + autorewrite with effects. eauto with effects.
  Qed.

  Lemma ST_Force V B :
    SemVWt Γ V (VThunk ϕ B) ->
    (* -------------- *)
    SemCWt Γ (cForce V) B ϕ.
  Proof.
    unfold SemVWt, SemCWt. intros IH ρ H.
    specialize IH with ρ.
    apply IH in H as
      [W [HE [m' [ρ' [M' [HW [T [ϕ1 [ϕ2 [HEM' [HL Heff]]]]]]]]]]].
    unfold LRM.
    exists T, ϕ1, ϕ2. split; try split; auto.
    econstructor; subst; eauto.
  Qed.

  Lemma ST_Split V A1 A2 N B :
    SemVWt Γ V (VPair A1 A2) ->
    SemCWt (A1 .: (A2 .: Γ)) N B ϕ ->
    (* -------------------- *)
    SemCWt Γ (cSplit V N) B ϕ.
  Proof.
    unfold SemVWt, SemCWt. intros IHV IHN ρ H.
    apply IHV in H as HV.
    destruct HV as [W [HWE HWL]].
    simpl in HWL. destruct HWL as [W1 [W2 [HW [HWL1 HWL2]]]].
    subst.
    apply ρ_ok_cons2
      with (W1 := W1) (W2 := W2) (A1 := A1) (A2 := A2) in H; auto.
    apply IHN in H as HN.
    destruct HN as [T [ϕ1 [ϕ2 [HTE [HTL Hle]]]]].
    exists T. eexists. eexists.
    split; try split; eauto.
    econstructor; eauto.
  Qed.

  Lemma ST_Ret V A :
    SemVWt Γ V A ->
    ϕ = ϵ ->
    (* ----------------- *)
    SemCWt Γ (cRet V) (CF A) ϕ.
  Proof.
    unfold SemVWt, SemCWt. intros IH IHϕ ρ H.
    apply IH in H as H'.
    destruct H' as [W [HWE HWL]].
    exists (CClosRet W). eexists. eexists.
    split; try split.
    - econstructor; eauto.
    - simpl. split; eauto.
    - subst. autorewrite with effects. eauto with effects.
  Qed.

  Lemma ST_Let M A N B ϕ1 ϕ2 :
    SemCWt Γ M (CF A) ϕ1 ->
    SemCWt (A .: Γ) N B ϕ2 ->
    ϕ = ϕ1 E+ ϕ2 ->
    (* ---------------- *)
    SemCWt Γ (cLet M N) B ϕ.
  Proof.
    unfold SemCWt. intros IHM IHN IHϕ ρ H.
    apply IHM in H as HM.
    destruct HM as [TM [ϕ1M [ϕ2M [HTME [HTML HleM]]]]].
    simpl in HTML.
    destruct HTML as [He [W [HTM HLW]]].
    subst.
    apply ρ_ok_cons with (W := W) (A := A) in H as H'; auto.
    apply IHN in H' as HN.
    destruct HN as [T [ϕ1N [ϕ2N [HEN [HLN HleN]]]]].
    exists T. eexists. eexists.
    split; try split; eauto.
    - econstructor; eauto.
    - autorewrite with effects. eauto with effects.
Qed.

  Lemma ST_CPair M1 B1 M2 B2 :
    SemCWt Γ M1 B1 ϕ ->
    SemCWt Γ M2 B2 ϕ ->
    (* --------------------------- *)
    SemCWt Γ (cPair M1 M2) (CPair B1 B2) ϕ.
  Proof.
    unfold SemCWt. intros IH1 IH2 ρ H.
    specialize IH1 with ρ. apply IH1 in H as IH1'.
      destruct IH1' as [T1 [ϕ11 [ϕ12 [H1E [H1L H1le]]]]]. clear IH1.
    specialize IH2 with ρ. apply IH2 in H as IH2'.
      destruct IH2' as [T2 [ϕ21 [ϕ22 [H2E [H2L H2le]]]]]. clear IH2.
    repeat eexists. eapply E_CPair. all: eauto.
    autorewrite with effects. auto with effects.
  Qed.

  Lemma ST_Fst M B1 B2 :
    SemCWt Γ M (CPair B1 B2) ϕ ->
    (* ------------------ *)
    SemCWt Γ (cFst M) B1 ϕ.
  Proof.
    unfold SemCWt. intros IH ρ H.
    specialize IH with ρ.
    apply IH in H.
    destruct H as [T' [ϕ1' [ϕ2' [HE' [HL' Hle']]]]].
    simpl in HL'.
      destruct HL' as [m [ρ' [M1 [M2 [HT
        [[T [ϕ1 [ϕ2 [HLE [HLR Hle]]]]] _]]]]]].
    subst. unfold LRM.
    exists T. eexists. eexists. split; try split; eauto.
    - eapply E_Fst. all: eauto.
    - autorewrite with effects. eauto with effects.
Qed.

  Lemma ST_Snd M B1 B2 :
    SemCWt Γ M (CPair B1 B2) ϕ ->
    (* ------------------ *)
    SemCWt Γ (cSnd M) B2 ϕ.
  Proof.
    unfold SemCWt. intros IH ρ H.
    specialize IH with ρ.
    apply IH in H.
    destruct H as [T' [ϕ1' [ϕ2' [HE' [HL' Hle']]]]].
    simpl in HL'.
      destruct HL' as [m [ρ' [M1 [M2 [HT
        [_ [T [ϕ1 [ϕ2 [HLE [HLR Hle]]]]]]]]]]].
    subst. unfold LRM.
    exists T. eexists. eexists. split; try split; eauto.
    - eapply E_Snd. all: eauto.
    - autorewrite with effects. eauto with effects.
Qed.

  Lemma ST_Seq V N B :
    SemVWt Γ V VUnit ->
    SemCWt Γ N B ϕ ->
    (*------------------*)
    SemCWt Γ (cSeq V N) B ϕ.
  Proof.
    unfold SemVWt, SemCWt. intros IHV IHM ρ H.
    specialize IHV with ρ.
    apply IHM in H as HM.
    destruct HM as [T [ϕ1 [ϕ2 [HE [HLT Hle]]]]].
    exists T. eexists. eexists. split; try split; eauto.
    econstructor; auto.
    apply IHV in H as HV.
    destruct HV as [W [HW HLW]].
    simpl in HLW. subst. auto.
Qed.

  Lemma ST_Case V A1 A2 M1 B M2 :
    SemVWt Γ V (VSum A1 A2) ->
    SemCWt (A1 .: Γ) M1 B ϕ ->
    SemCWt (A2 .: Γ) M2 B ϕ ->
    (*------------------------------*)
    SemCWt Γ (cCase V M1 M2) B ϕ.
  Proof.
    unfold SemVWt, SemCWt. intros IHV IH1 IH2 ρ H.
    apply IHV in H as HV.
    destruct HV as [W [HWE HWL]].
    destruct HWL as [W' [[HW' HL] | [HW' HL]]].
    - apply ρ_ok_cons with (W := W') (A := A1) in H as H1; auto.
      apply IH1 in H1 as H1'.
      destruct H1' as [T [ϕ1 [ϕ2 [HE [HLB Hle]]]]].
      exists T. eexists. eexists.
      split; try split; eauto.
      econstructor; eauto. subst. eauto.
    - apply ρ_ok_cons with (W := W') (A := A2) in H as H2; auto.
      apply IH2 in H2 as H2'.
      destruct H2' as [T [ϕ1 [ϕ2 [HE [HLB Hle]]]]].
      exists T. eexists. eexists.
      split; try split; eauto.
      solve [ econstructor; eauto; subst; eauto ].
  Qed.

  Lemma ST_Tick :
    ϕ = tick ->
    (* -------------------------------- *)
    SemCWt Γ cTick (CF VUnit) ϕ.
  Proof.
    unfold SemCWt. intros IHIHϕ ρ H.
    repeat eexists. eapply E_Tick.
    - try eassumption.
    - rewrite eff_idR. subst. apply subeff_refl.
Qed.

  Lemma ST_CSub M B :
    SemCWt Γ M B ϕ ->
    (* --------------- *)
    SemCWt Γ M B ϕ.
  Proof.
    unfold SemCWt. intros IH ρ H. auto.
Qed.

  Lemma ST_SubEff M B ϕ' :
    SemCWt Γ M B ϕ ->
    ϕ E<= ϕ' ->
    (* --------------- *)
    SemCWt Γ M B ϕ'.
  Proof.
    unfold SemCWt. intros IH IHϕ ρ H.
    specialize IH with ρ. apply IH in H as [T [ϕ1 [ϕ2 [HTE [HTL Hle]]]]].
    repeat eexists. all: eauto with effects.
  Qed.

End SemTyping.

#[export]Hint Resolve ST_Var ST_Thunk ST_Unit ST_VPair ST_Inl ST_Inr ST_Abs
  ST_App ST_Force ST_Ret ST_Let ST_Split ST_CPair ST_Fst ST_Snd
  ST_Seq ST_Case ST_Tick ST_CSub ST_SubEff : semtyping.
