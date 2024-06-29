Require Export resource.CBPV.semantics resource.CBPV.typing common.resource_axioms.

Definition LRM {n} (LR : CompTy -> CClos -> Prop) (B : CompTy) (γ : gradeVec n) (ρ : env n) (M : Comp n) :=
  exists T , EvalComp γ ρ M T /\ LR B T.

Fixpoint LRV (A : ValTy) (W : VClos) : Prop :=
    match A with
    | VUnit => W = VClosUnit
    | VThunk B => exists m γ ρ M,
      W = VClosThunk m γ ρ M /\ LRM LRC B γ ρ M
    | VPair A1 A2 => exists W1 W2,
      W = VClosPair W1 W2 /\ LRV A1 W1 /\ LRV A2 W2
    | VSum A1 A2 => exists W',
      (W = VClosInl W' /\ LRV A1 W')
      \/ (W = VClosInr W' /\ LRV A2 W')
    end
  with LRC (B : CompTy) (T : CClos) :=
    match B with
    | CF q A => ((q = Qzero /\ T = CClosRet q JUNK) \/
      (q <> Qzero /\ exists W, T = CClosRet q W /\ LRV A W))
    | CPair B1 B2 => exists m γ ρ M1 M2, T = CClosPair m γ ρ M1 M2 /\
                                     LRM LRC B1 γ ρ M1 /\
                                     LRM LRC B2 γ ρ M2
    | CAbs q A B => exists m γ ρ M, T = CClosAbs m q γ ρ M /\
      ((q = Qzero /\ LRM LRC B (Qzero .: γ) (JUNK .: ρ) M) \/
      (q <> Qzero /\ forall W, LRV A W -> LRM LRC B (q .: γ) (W .: ρ) M))
    end.

Definition ρ_ok {n} γ ρ Γ := forall (i : fin n), (γ i = Qzero \/ LRV (Γ i) (ρ i)).

Definition SemVWt {n} (γ : gradeVec n) (Γ : context n) V A :=
  forall ρ, ρ_ok γ ρ Γ -> exists W, EvalVal γ ρ V W /\ LRV A W.

Definition SemCWt {n} (γ : gradeVec n) (Γ : context n) M B :=
  forall ρ, ρ_ok γ ρ Γ -> LRM LRC B γ ρ M.

Lemma ρ_ok_null : ρ_ok null null null.
Proof.
  unfold ρ_ok. intros. destruct i.
Qed.

Lemma ρ_ok_cons n q γ ρ (Γ : context n) W A
  (H1 : q = Qzero \/ LRV A W)
  (H2 : ρ_ok γ ρ Γ) :
  ρ_ok (q .: γ) (W .: ρ) (A .: Γ).
Proof.
  unfold ρ_ok. intros. unfold scons.
  destruct H1, i; auto; contradiction.
Qed.

Lemma ρ_ok_cons2 n q1 q2 γ ρ (Γ : context n) W1 W2 A1 A2
  (H1 : q1 = Qzero \/ LRV A1 W1)
  (H2 : q2 = Qzero \/ LRV A2 W2)
  (H3 : ρ_ok γ ρ Γ) :
  ρ_ok (q1 .: (q2 .: γ)) (W1 .: (W2 .: ρ)) (A1 .: (A2 .: Γ)).
Proof. apply ρ_ok_cons; try apply ρ_ok_cons; assumption. Qed.

Lemma ρ_ok_sum : forall n (γ : gradeVec n) γ1 γ2 ρ Γ,
  γ = γ1 Q+ γ2 -> ρ_ok γ ρ Γ ->
  ρ_ok γ1 ρ Γ /\ ρ_ok γ2 ρ Γ.
Proof.
  intros. unfold ρ_ok in H0. split.
  intros i. specialize H0 with i as [H0 | H0].
  left. rewrite H in H0. unfold gradeVecAdd in H0.
  edestruct Qsumzero. rewrite H0. eauto with coeffects. assumption.
  right. assumption.
  intros i. specialize H0 with i as [H0 | H0].
  left. rewrite H in H0. unfold gradeVecAdd in H0.
  edestruct Qsumzero. rewrite H0. eauto with coeffects. assumption.
  right. assumption.
Qed.

Lemma ρ_ok_prod : forall n q (γ : gradeVec n) ρ Γ,
  ρ_ok (q Q* γ) ρ Γ ->
  q = Qzero \/ ρ_ok γ ρ Γ.
Proof.
  intros. destruct Qeq_dec with (q1 := q) (q2 := Qzero) as [Heq | Hneq]; firstorder.
  right. unfold ρ_ok in *. intros i; specialize H with i as [H | H]; firstorder.
  left. unfold gradeVecScale in H. apply Qprodzero in H as [H | H]; firstorder.
Qed.

Lemma ρ_ok_le : forall n (γ γ' : gradeVec n) ρ Γ,
  gradeVecLe γ γ' ->
  ρ_ok γ ρ Γ ->
  ρ_ok γ' ρ Γ.
Proof.
  unfold ρ_ok. intros.
  unfold gradeVecLe in H.
  specialize H with i.
  specialize H0 with i as [H0 | H0]; auto. left.
  rewrite H0 in H. apply Q_lt_zero in H. auto.
Qed.

Section SemTyping.

Context {n : nat} (γ : gradeVec n) (Γ : context n) .

(* Semantic typing rules. *)

(* Values*)
  Lemma ST_Var i :
    γ i = Qone ->
    (forall (j : fin n), j <> i -> γ j = Qzero) ->
    SemVWt γ Γ (var_Val i) (Γ i).
  Proof.
    unfold SemVWt. intros Hqi Hqj ρ H. unfold ρ_ok in H.
    specialize H with i as [H | H].
    - rewrite H in Hqi. destruct Qnontrivial. auto.
    - exists (ρ i). split.
      + apply E_Var; auto.
      + assumption.
  Qed.

  Lemma ST_Thunk M B :
    SemCWt γ Γ M B ->
    SemVWt γ Γ (vThunk M) (VThunk B).
  Proof.
    unfold SemCWt, SemVWt. intros IH ρ H.
    specialize IH with ρ.
    apply IH in H.
    destruct H as [T [HA Hle]].
    eexists. split.
    - constructor. auto.
    - repeat eexists; eassumption.
  Qed.

  Lemma ST_Unit :
    γ = (0s : gradeVec n) ->
    SemVWt γ Γ vUnit VUnit.
  Proof.
    unfold SemVWt. intros ρ H. eexists. split. eauto with semantics. reflexivity.
  Qed.

  Lemma ST_VPair V1 V2 A1 A2 γ1 γ2 :
    SemVWt γ1 Γ V1 A1 ->
    SemVWt γ2 Γ V2 A2 ->
    γ = γ1 Q+ γ2 ->
    (* ------------------------------ *)
    SemVWt γ Γ (vPair V1 V2) (VPair A1 A2).
  Proof.
    unfold SemVWt. intros IH1 IH2 IHq ρ H.
    eapply ρ_ok_sum in IHq as IHq'.
    destruct IHq' as [H1 H2].
    specialize IH1 with ρ. apply IH1 in H1 as IH1'.
      destruct IH1' as [W1 [H1E H1L]]. clear IH1.
    specialize IH2 with ρ. apply IH2 in H2 as IH2'.
      destruct IH2' as [W2 [H2E H2L]]. clear IH2.
    eexists. split.
    econstructor; eassumption.
    firstorder.
    auto.
  Qed.

  Lemma ST_Inl V A1 A2 :
    SemVWt γ Γ V A1 ->
    (* ----------------------- *)
    SemVWt γ Γ (vInl V) (VSum A1 A2).
  Proof.
    unfold SemVWt. intros IH ρ H.
    specialize IH with ρ. apply IH in H as [W [HE HL]].
    exists (VClosInl W). split.
    - constructor. assumption.
    - exists W. left. split; auto.
  Qed.

  Lemma ST_Inr V A1 A2 :
    SemVWt γ Γ V A2 ->
    (* ----------------------- *)
    SemVWt γ Γ (vInr V) (VSum A1 A2).
  Proof.
    unfold SemVWt. intros IH ρ H.
    specialize IH with ρ. apply IH in H as [W [HE HL]].
    exists (VClosInr W). split.
    - constructor. assumption.
    - exists W. auto.
  Qed.

  Lemma ST_VSub V A γ' :
    SemVWt γ' Γ V A ->
    γ Q<= γ' ->
    (* ------------------ *)
    SemVWt γ Γ V A.
  Proof.
    unfold SemVWt. intros IH IHγ ρ H.
    specialize IH with ρ. eapply ρ_ok_le in H.
    apply IH in H as [W [HE HL]].
    repeat eexists. eapply E_VSub. all: eauto.
  Qed.

(*Computations*)

  Lemma ST_Abs q q' A M B :
    SemCWt (q .: γ) (A .: Γ) M B ->
    Qle q' q ->
    (* ------------- *)
    SemCWt γ Γ (cAbs q M) (CAbs q' A B).
  Proof.
    unfold SemCWt. intros IH IHq ρ H.
    repeat eexists.
    econstructor. eassumption. eauto.
    edestruct Qeq_dec as [Heq | Hneq].
    - left. split. eassumption. subst. apply Q_lt_zero in IHq. subst.
      eapply ρ_ok_cons in H. apply IH in H. eassumption. left. auto.
    - right. split. eassumption. intros. eapply ρ_ok_cons with (W := W) in H.
      apply IH in H as [T [HT Hle]].
      repeat eexists. eapply E_CSub. all: eauto with coeffects.
  Qed.

  Lemma ST_App q M A B V γ1 γ2 :
    SemCWt γ1 Γ M (CAbs q A B) ->
    SemVWt γ2 Γ V A ->
    γ = γ1 Q+ (q Q* γ2) ->
    (* --------------- *)
    SemCWt γ Γ (cApp M V) B.
  Proof.
  intros. unfold SemCWt. intros.
  eapply ρ_ok_sum with (γ2 := q Q* γ2) in H2 as [H3 H22]; eauto.
  eapply ρ_ok_prod in H22. assert (q <> Qzero -> ρ_ok γ2 ρ Γ).
  { intros. destruct H22. contradiction. eauto. }
  unfold SemCWt in H. specialize H with ρ as Hg1.
  apply Hg1 in H3 as [T' [HT'eval HT']]. clear Hg1.
  destruct HT' as [m [γ' [ρ' [M' [Ht' [Heq | Hneq]]]]]].
  - (*q = 0*) destruct Heq as [Hq [T [HTeval HT]]].
    repeat eexists. eapply E_AppAbsZero. rewrite Ht' in HT'eval.
    rewrite Hq in H1. autorewrite with coeffects in H1. subst.
    all: eauto.
  - (*q <> 0*) destruct Hneq as [Hq HWall].
    apply H2 in Hq as Hg2. apply H0 in Hg2 as [W [HWeval HW]].
    apply HWall in HW as [T [HTeval HT]]. repeat eexists.
    eapply E_AppAbs. rewrite Ht' in HT'eval. all: eauto.
  Qed.

  Lemma ST_Force V B :
    SemVWt γ Γ V (VThunk B) ->
    (* -------------- *)
    SemCWt γ Γ (cForce V) B.
  Proof.
    unfold SemVWt, SemCWt. intros IH ρ H.
    specialize IH with ρ. apply IH in H as [W [HE HL]].
    inversion HL as [m [γ' [ρ' [M [HW [T [HT HTL]]]]]]].
    repeat eexists. subst. econstructor. all: eauto.
  Qed.

  Lemma ST_Split q V A1 A2 N B γ1 γ2 :
    SemVWt γ1 Γ V (VPair A1 A2) ->
    SemCWt (q .: (q .: γ2)) (A1 .: (A2 .: Γ)) N B ->
    γ = (q Q* γ1) Q+ γ2 ->
    (* -------------------- *)
    SemCWt γ Γ (cSplit q V N) B.
  Proof.
    unfold SemVWt, SemCWt. intros IHV IHN IHq ρ H.
    eapply ρ_ok_sum with (γ1 := q Q* γ1) in H as [H' H'']; try eassumption.
    apply ρ_ok_prod in H'.
    specialize IHV with ρ.
    destruct (Qeq_dec q Qzero).
    - rewrite H in IHq. autorewrite with coeffects in IHq. subst.
      specialize IHN with (JUNK .: (JUNK .: ρ)).
      eapply ρ_ok_cons2 in H'' as Hok.
      apply IHN in Hok as [T [Heval HLR]].
      repeat eexists. eapply E_SplitZero. all: eauto.
    - destruct H'; try contradiction.
      apply IHV in H0 as [W [HWeval [W1 [W2 [HWeq [HW1 HW2]]]]]].
      specialize IHN with (W1 .: (W2 .: ρ)).
      eapply ρ_ok_cons2 in H''.
      apply IHN in H'' as [T [HTE HTL]].
      repeat eexists. subst. eapply E_Split. all: eauto.
  Qed.

  Lemma ST_Ret q V A γ1 :
    SemVWt γ1 Γ V A ->
    γ = q Q* γ1 ->
    (* ----------------- *)
    SemCWt γ Γ (cRet q V) (CF q A).
  Proof.
    unfold SemVWt, SemCWt. intros IH IHq ρ H.
    specialize IH with ρ.
    destruct (Qeq_dec q Qzero).
    - rewrite H0 in IHq. autorewrite with coeffects in IHq. subst.
      repeat eexists. eapply E_RetZero. all: auto.
      econstructor. split; auto.
    - subst. assert (ρ_ok γ1 ρ Γ).
      { apply ρ_ok_prod in H as []; auto. contradiction. }
      apply IH in H1 as [W [HE HL]].
      repeat eexists. eapply E_Ret. all: eauto.
      simpl. right. split; eauto.
  Qed.

  Lemma ST_Let q1 q2 q' M A N B γ1 γ2 :
    q' = q_or_1 q2 ->
    SemCWt γ1 Γ M (CF q1 A) ->
    SemCWt (Qmult q1 q' .: γ2) (A .: Γ) N B ->
    γ = (q' Q* γ1) Q+ γ2 ->
    (* ---------------- *)
    SemCWt γ Γ (cLet q2 M N) B.
  Proof.
    unfold SemCWt. intros Hq' IHM IHN IHq ρ H.
    specialize IHM with ρ. eapply ρ_ok_sum in IHq as IHq'.
    destruct IHq' as [Hg1 Hg2].
    eapply ρ_ok_prod in Hg1 as [Hg1 | Hg1]. all: try eassumption.
    - exfalso. subst. remember (q_or_1_neq_0 q2) as Hc.
      destruct Hc as [Hc | Hc]; try contradiction.
      apply Qnontrivial; auto.
    - apply IHM in Hg1 as IHM'.
      destruct IHM' as [TM [HME HML]].
      clear IHM.
      destruct HML as
        [ [Hz HTM] | [Hq1 [W [HWeval HWL]]] ].
      + subst. autorewrite with coeffects in IHN. eapply ρ_ok_cons in Hg2 as Hg2'.
        eapply IHN in Hg2' as [T [HTE HTL]]. repeat eexists.
        eapply E_LetRet. all: eauto. autorewrite with coeffects. eauto.
      + eapply ρ_ok_cons in Hg2.
        apply IHN in Hg2 as [T [HTE HTL]]. repeat eexists.
        subst. eapply E_LetRet. all: eauto.
  Qed.

  Lemma ST_CPair M1 B1 M2 B2 :
    SemCWt γ Γ M1 B1 ->
    SemCWt γ Γ M2 B2 ->
    (* --------------------------- *)
    SemCWt γ Γ (cPair M1 M2) (CPair B1 B2).
  Proof.
    unfold SemCWt. intros IH1 IH2 ρ H.
    specialize IH1 with ρ. apply IH1 in H as IH1'.
      destruct IH1' as [T1 [H1E H1L]]. clear IH1.
    specialize IH2 with ρ. apply IH2 in H as IH2'.
      destruct IH2' as [T2 [H2E H2L]]. clear IH2.
    repeat eexists. eapply E_CPair. all: eauto.
  Qed.

  Lemma ST_Fst M B1 B2 :
    SemCWt γ Γ M (CPair B1 B2) ->
    (* ------------------ *)
    SemCWt γ Γ (cFst M) B1.
  Proof.
    unfold SemCWt. intros IH ρ H.
    specialize IH with ρ.
    apply IH in H as [T' [HE' HL']].
    inversion HL' as [m [γ' [ρ' [M1 [M2 [HT' [HT _]]]]]]].
    destruct HT as [T [HE HL]]. repeat eexists.
    subst. eapply E_Fst. all: eauto.
  Qed.

  Lemma ST_Snd M B1 B2 :
    SemCWt γ Γ M (CPair B1 B2) ->
    (* ------------------ *)
    SemCWt γ Γ (cSnd M) B2.
  Proof.
    unfold SemCWt. intros IH ρ H.
    specialize IH with ρ.
    apply IH in H as [T' [HE' HL']].
    inversion HL' as [m [γ' [ρ' [M1 [M2 [HT' [_ HT]]]]]]].
    destruct HT as [T [HE HL]]. repeat eexists.
    subst. eapply E_Snd. all: eauto.
  Qed.

  Lemma ST_Seq V N B γ1 γ2 :
    SemVWt γ1 Γ V VUnit ->
    SemCWt γ2 Γ N B ->
    γ = γ1 Q+ γ2 ->
    (*------------------*)
    SemCWt γ Γ (cSeq V N) B.
  Proof.
    unfold SemVWt, SemCWt. intros IHV IHM IHq ρ H.
    specialize IHV with ρ.
    eapply ρ_ok_sum in IHq as IHq'.
    destruct IHq' as [Hg1 Hg2]. apply IHV in Hg1 as IHV'.
      destruct IHV' as [W [HWE HWL]]. clear IHV.
    inversion HWL. subst.
    specialize IHM with ρ. apply IHM in Hg2 as IHM'.
    destruct IHM' as [T [HTE HTL]]. clear IHM.
    repeat eexists. eapply E_Seq. all: eauto.
  Qed.

  Lemma ST_Case q V A1 A2 M1 B M2 γ1 γ2 :
    SemVWt γ1 Γ V (VSum A1 A2) ->
    SemCWt (q .: γ2) (A1 .: Γ) M1 B ->
    SemCWt (q .: γ2) (A2 .: Γ) M2 B ->
    γ = (q Q* γ1) Q+ γ2 ->
    Qle q Qone ->
    (*------------------------------*)
    SemCWt γ Γ (cCase q V M1 M2) B.
  Proof.
    unfold SemVWt, SemCWt. intros IHV IH1 IH2 IHq1 IHq2 ρ H.
    specialize IHV with ρ.
    eapply ρ_ok_sum in IHq1 as IHq1'. destruct IHq1' as [Hgq1 Hg2].
    all: try eassumption. eapply ρ_ok_prod in Hgq1 as [Hq | Hg1].
    - subst. apply Q_one_lt_zero in IHq2. contradiction.
    - apply IHV in Hg1 as IHV'.
      destruct IHV' as [W' [HWE' HWL']]. clear IHV.
      inversion HWL' as [W [[HW HWL] | [HW HWL]]].
      + subst. eapply ρ_ok_cons in Hg2.
        apply IH1 in Hg2 as [T [HTE HTL]]. repeat eexists.
        eapply E_Casel. all: eauto.
      + subst. eapply ρ_ok_cons in Hg2.
        apply IH2 in Hg2 as [T [HTE HTL]]. repeat eexists.
        eapply E_Caser. all: eauto.
  Qed.

  Lemma ST_CSub M B γ' :
    SemCWt γ' Γ M B ->
    γ Q<= γ' ->
    (* --------------- *)
    SemCWt γ Γ M B.
  Proof.
    unfold SemCWt. intros IH IHγ ρ H.
    specialize IH with ρ. eapply ρ_ok_le in H.
    apply IH in H as [T [HTE HTL]].
    repeat eexists. eapply E_CSub. all: eauto.
  Qed.

End SemTyping.

#[export]Hint Resolve ST_Var ST_Thunk ST_Unit ST_VPair ST_Inl ST_Inr ST_VSub ST_Abs
  ST_App ST_Force ST_Ret ST_Let ST_Split ST_CPair ST_Fst ST_Snd
  ST_Seq ST_Case ST_CSub : semtyping.
