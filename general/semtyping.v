Require Export general.semantics general.typing.

(* Definition of the logical relation for values and computations. *)
Fixpoint LRV (A : ValTy) (W : VClos) : Prop :=
  match A with
  | VUnit => W = VClosUnit
  | VThunk B => exists m γ ρ M, W = VClosThunk m γ ρ M /\ exists T, EvalComp γ ρ M T /\ LRC B T
  | VPair A1 A2 => exists W1 W2, W = VClosPair W1 W2 /\ LRV A1 W1 /\ LRV A2 W2
  | VSum A1 A2 => exists W', (W = VClosInl W' /\ LRV A1 W') \/ (W = VClosInr W' /\ LRV A2 W')
  end
with LRC (B : CompTy) (T : CClos) :=
  match B with
  | CF q A => exists W, T = CClosRet q W /\ LRV A W
  | CPair B1 B2 => exists m γ ρ M1 M2, T = CClosPair  m γ ρ M1 M2 /\
                                 (exists T1, EvalComp γ ρ M1 T1 /\ LRC B1 T1) /\
                                 (exists T2, EvalComp γ ρ M2 T2 /\ LRC B2 T2)
  | CAbs q A B => exists m γ ρ M, T = CClosAbs m q γ ρ M /\ forall W, LRV A W -> exists T1, EvalComp (q .: γ) (W .: ρ) M T1 /\ LRC B T1
  end.

Definition ρ_ok {n} ρ Γ := forall (i : fin n), LRV (Γ i) (ρ i).

(* Semantic Typing for Values *)
Definition SemVWt {n} (γ : gradeVec n) (Γ : context n) V A := forall ρ, ρ_ok ρ Γ -> exists W, EvalVal γ ρ V W /\ LRV A W.

(* Semantic Typing for Computations *)
Definition SemCWt {n} (γ : gradeVec n) (Γ : context n) M B := forall ρ, ρ_ok ρ Γ -> exists T, EvalComp γ ρ M T /\ LRC B T.

Lemma ρ_ok_null : ρ_ok null null.
Proof.
  unfold ρ_ok. intros. destruct i.
Qed.

Lemma ρ_ok_cons n ρ (Γ : context n) W A
  (h1 : LRV A W)
  (h2 : ρ_ok ρ Γ) :
  ρ_ok (W .: ρ) (A .: Γ).
Proof. unfold ρ_ok. intros. unfold scons. destruct i; auto. Qed.

Lemma ρ_ok_cons2 n ρ (Γ : context n) W1 W2 A1 A2
  (h1 : LRV A1 W1)
  (h2 : LRV A2 W2)
  (h3 : ρ_ok ρ Γ) :
  ρ_ok (W1 .: (W2 .: ρ)) (A1 .: (A2 .: Γ)).
Proof. apply ρ_ok_cons; try apply ρ_ok_cons; assumption. Qed.


Section SemTyping.

  Context {n : nat} (γ : gradeVec n) (Γ : context n).

(* Semantic typing rules. *)

(* Values*)
  Lemma ST_Var i :
    (γ i) = Qone ->
    (forall (j : fin n), j <> i -> (γ j) = Qzero) ->
    SemVWt γ Γ (var_Val i) (Γ i).
  Proof.
    unfold SemVWt. intros Hqi Hqj ρ H. unfold ρ_ok in H.
    specialize H with i. exists (ρ i). split.
    - apply E_Var; auto.
    - assumption.
  Qed.

  Lemma ST_Thunk M B :
    SemCWt γ Γ M B ->
    SemVWt γ Γ (vThunk M) (VThunk B).
  Proof.
    unfold SemCWt, SemVWt. intros IH ρ H.
    specialize IH with ρ.
    apply IH in H.
    exists (VClosThunk n γ ρ M). split.
    - constructor.
    - simpl. exists n, γ, ρ, M. auto.
  Qed.

  Lemma ST_Unit :
    γ = (0s : gradeVec n) ->
    SemVWt γ Γ vUnit VUnit.
  Proof.
    unfold SemVWt. intros ρ H. exists VClosUnit. split.
    - constructor. subst. auto.
    - reflexivity.
  Qed.

  Lemma ST_VPair V1 V2 A1 A2 γ1 γ2 :
    SemVWt γ1 Γ V1 A1 ->
    SemVWt γ2 Γ V2 A2 ->
    γ = (γ1 Q+ γ2) ->
    (* ------------------------------ *)
    SemVWt γ Γ (vPair V1 V2) (VPair A1 A2).
  Proof.
    unfold SemVWt. intros IH1 IH2 IHq ρ H.
    specialize IH1 with ρ. apply IH1 in H as IH1'.
      destruct IH1' as [W1 [H1E H1L]]. clear IH1.
    specialize IH2 with ρ. apply IH2 in H as IH2'.
      destruct IH2' as [W2 [H2E H2L]]. clear IH2.
    exists (VClosPair W1 W2). split.
    - apply E_VPair with (γ1 := γ1) (γ2 := γ2); auto.
    - firstorder.
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
    - exists W. auto.
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

(*Computations*)

  Lemma ST_Abs q' q A M B :
    SemCWt (q .: γ) (A .: Γ) M B ->
    Qle q' q ->
    (* ------------- *)
    SemCWt γ Γ (cAbs q M) (CAbs q' A B).
  Proof.
    unfold SemCWt. intros IH LT ρ H.
    exists (CClosAbs n q' γ ρ M). split.
    - constructor. auto.
    - simpl. exists n, γ, ρ, M. firstorder.
      specialize IH with (W .: ρ).
      apply ρ_ok_cons with (W := W) (A := A) in H; auto.
      destruct (IH H) as [T [h1 h2]].
      exists T. split.
      eapply E_SubM; eauto with coeffects. auto.
  Qed.

  Lemma ST_App q M A B V γ1 γ2 :
    SemCWt γ1 Γ M (CAbs q A B) ->
    SemVWt γ2 Γ V A ->
    γ = (γ1 Q+ (q Q* γ2)) ->
    (* --------------- *)
    SemCWt γ Γ (cApp M V) B.
  Proof.
    unfold SemCWt, SemVWt. intros IHM IHV IHq ρ H.
    specialize IHM with ρ. apply IHM in H as IHM'.
      destruct IHM' as [T' [HME HML]]. clear IHM.
    specialize IHV with ρ. apply IHV in H as IHV'.
      destruct IHV' as [W [HVE HVL]]. clear IHV.
    inversion HML as [m [γ' [ρ' [M' [HT' HTL]]]]].
    specialize HTL with W. apply HTL in HVL. clear HTL.
    destruct HVL as [T [HE HL]].
    exists T. subst. split.
    - apply E_AppAbs with (m := m) (q := q) (γ' := γ') (ρ' := ρ')
      (M' := M') (W := W) (γ1 := γ1) (γ2 := γ2); auto.
    - assumption.
  Qed.

  Lemma ST_Force V B :
    SemVWt γ Γ V (VThunk B) ->
    (* -------------- *)
    SemCWt γ Γ (cForce V) B.
  Proof.
    unfold SemVWt, SemCWt. intros IH ρ H.
    specialize IH with ρ. apply IH in H as [W [HE HL]].
    inversion HL as [m [γ' [ρ' [M [HW [T [HT HTL]]]]]]].
    exists T. subst. split.
    - apply E_ForceThunk with (γ' := γ') (ρ' := ρ') (M := M); assumption.
    - assumption.
  Qed.

  Lemma ST_Split q V A1 A2 N B γ1 γ2 :
    SemVWt γ1 Γ V (VPair A1 A2) ->
    SemCWt (q .: (q .: γ2)) (A1 .: (A2 .: Γ)) N B ->
    γ = ((q Q* γ1) Q+ γ2) ->
    (* -------------------- *)
    SemCWt γ Γ (cSplit q V N) B.
  Proof.
    unfold SemVWt, SemCWt. intros IHV IHN IHq ρ H.
    specialize IHV with ρ. apply IHV in H as IHV'.
      destruct IHV' as [W [HWE HWL]]. clear IHV.
    inversion HWL as [W1 [W2 [HW [HWL1 HWL2]]]].
    specialize IHN with (W1 .: (W2 .: ρ)).
    apply ρ_ok_cons2
      with (W1 := W1) (W2 := W2) (A1 := A1) (A2 := A2) in H; try assumption.
    apply IHN in H as [T [HTE HTL]].
    exists T. subst. split.
    - apply E_Split with (W1 := W1) (W2 := W2) (γ1 := γ1) (γ2 := γ2); auto using gradeVecLeRefl.
    - assumption.
  Qed.

  Lemma ST_Ret q V A γ1 :
    SemVWt γ1 Γ V A ->
    γ = (q Q* γ1) ->
    (* ----------------- *)
    SemCWt γ Γ (cRet q V) (CF q A).
  Proof.
    unfold SemVWt, SemCWt. intros IH IHq ρ H.
    specialize IH with ρ. apply IH in H as [W [HE HL]].
    exists (CClosRet q W). split.
    - apply E_Ret with (γ' := γ1); subst; auto using gradeVecLeRefl.
    - simpl. exists W. auto.
  Qed.

  Lemma ST_Let q1 q2 M A N B γ1 γ2 :
    SemCWt γ1 Γ M (CF q1 A) ->
    SemCWt (Qmult q1 q2 .: γ2) (A .: Γ) N B ->
    γ = ((q2 Q* γ1) Q+ γ2 ) ->
    (* ---------------- *)
    SemCWt γ Γ (cLet q2 M N) B.
  Proof.
    unfold SemCWt. intros IHM IHN IHq ρ H.
    specialize IHM with ρ. apply IHM in H as IHM'.
      destruct IHM' as [TM [HME HML]]. clear IHM.
    inversion HML as [W [HW HWL]].
    specialize IHN with (W .: ρ).
      apply ρ_ok_cons with (W := W) (A := A) in H; try assumption.
      apply IHN in H as [T [HTE HTL]].
    exists T. subst. split.
    - apply E_LetRet with (W := W) (q1 := q1) (γ1 := γ1) (γ2 := γ2); auto using gradeVecLeRefl.
    - assumption.
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
    exists (CClosPair n γ ρ M1 M2). split.
    - constructor.
    - exists n, γ, ρ, M1, M2. firstorder.
  Qed.

  Lemma ST_Fst M B1 B2 :
    SemCWt γ Γ M (CPair B1 B2) ->
    (* ------------------ *)
    SemCWt γ Γ (cFst M) B1.
  Proof.
    unfold SemCWt. intros IH ρ H.
    specialize IH with ρ. apply IH in H as [T' [HE' HL']].
    inversion HL' as [m [γ' [ρ' [M1 [M2 [HT' [HT1 HT2]]]]]]].
    destruct HT1 as [T1 [HE1 HL1]].
    exists T1. subst. split.
    - apply E_Fst
        with (γ' := γ') (ρ' := ρ') (M1 := M1) (M2 := M2); assumption.
    - assumption.
  Qed.

  Lemma ST_Snd M B1 B2 :
    SemCWt γ Γ M (CPair B1 B2) ->
    (* ------------------ *)
    SemCWt γ Γ (cSnd M) B2.
  Proof.
    unfold SemCWt. intros IH ρ H.
    specialize IH with ρ. apply IH in H as [T' [HE' HL']].
    inversion HL' as [m [γ' [ρ' [M1 [M2 [HT' [HT1 HT2]]]]]]].
    destruct HT2 as [T2 [HE2 HL2]].
    exists T2. subst. split.
    - apply E_Snd
        with (γ' := γ') (ρ' := ρ') (M1 := M1) (M2 := M2); assumption.
    - assumption.
  Qed.

  Lemma ST_Seq V N B γ1 γ2 :
    SemVWt γ1 Γ V VUnit ->
    SemCWt γ2 Γ N B ->
    γ = (γ1 Q+ γ2) ->
    (*------------------*)
    SemCWt γ Γ (cSeq V N) B.
  Proof.
    unfold SemVWt, SemCWt. intros IHV IHM IHq ρ H.
    specialize IHV with ρ. apply IHV in H as IHV'.
      destruct IHV' as [W [HWE HWL]]. clear IHV.
    inversion HWL. subst.
    specialize IHM with ρ. apply IHM in H as IHM'.
      destruct IHM' as [T [HTE HTL]]. clear IHM.
    exists T. split.
    - apply E_Seq with (γ1 := γ1) (γ2 := γ2); auto using gradeVecLeRefl.
    - assumption.
  Qed.

  Lemma ST_Case q V A1 A2 M1 B M2 γ1 γ2 :
    SemVWt γ1 Γ V (VSum A1 A2) ->
    SemCWt (q .: γ2) (A1 .: Γ) M1 B ->
    SemCWt (q .: γ2) (A2 .: Γ) M2 B ->
    γ = ((q Q* γ1) Q+ γ2) ->
    Qle q Qone ->
    (*------------------------------*)
    SemCWt γ Γ (cCase q V M1 M2) B.
  Proof.
    unfold SemVWt, SemCWt. intros IHV IH1 IH2 IHq1 IHq2 ρ H.
    specialize IHV with ρ. apply IHV in H as IHV'.
    destruct IHV' as [W' [HWE' HWL']]. clear IHV.
    inversion HWL' as [W [[HW HWL] | [HW HWL]]].
    - apply ρ_ok_cons with (W := W) (A := A1) in H; try assumption.
        apply IH1 in H as [T [HTE HTL]].
      exists T. subst. split.
      + apply E_Casel with (W := W) (γ1 := γ1) (γ2 := γ2); auto using gradeVecLeRefl.
      + assumption.
    - apply ρ_ok_cons with (W := W) (A := A2) in H; try assumption.
        apply IH2 in H as [T [HTE HTL]].
      exists T. subst. split.
      + apply E_Caser with (W := W) (γ1 := γ1) (γ2 := γ2); auto using gradeVecLeRefl.
      + assumption.
  Qed.

  Lemma ST_SubV  (γ1 : gradeVec n) V A :
    SemVWt γ1 Γ V A ->
    γ Q<= γ1 ->
    SemVWt γ Γ V A.
  Proof.
    unfold SemVWt, SemCWt. intros IHV QLE.
    intros ρ H.
    specialize IHV with ρ. apply IHV in H as IHV'.
    destruct IHV' as [W [EV LR]].
    exists W. split. eapply E_SubV; eauto. auto.
  Qed.

  Lemma ST_SubM  (γ1 : gradeVec n) M B :
    SemCWt γ1 Γ M B ->
    γ Q<= γ1 ->
    SemCWt γ Γ M B.
  Proof.
    unfold SemVWt, SemCWt. intros IHV QLE.
    intros ρ H.
    specialize IHV with ρ. apply IHV in H as IHV'.
    destruct IHV' as [W [EV LR]].
    exists W. split. eapply E_SubM; eauto. auto.
  Qed.

End SemTyping.

#[export]Hint Resolve ST_Var ST_Thunk ST_Unit ST_VPair ST_Inl ST_Inr ST_Abs
  ST_App ST_Force ST_Ret ST_Let ST_Split ST_CPair ST_Fst ST_Snd
  ST_Seq ST_Case ST_SubV ST_SubM : semtyping.

