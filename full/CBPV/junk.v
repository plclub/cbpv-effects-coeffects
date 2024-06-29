Require Import common.junk_axioms.
Require Export full.CBPV.syntax full.CBPV.semantics full.CBPV.semtyping.
Require Import Coq.Program.Equality.
Require Import ssreflect.

(* This file proves that skipping O-marked values and pure, unused
computations doesn't matter. It does this by constructing a logical relation
between a combined system with the general semantics and the combined system
with the resource-aware semantics and shows that these two semantics produce
related values and terminals.  *)



Module G.

Inductive EvalComp {n} (γ : gradeVec n) (ρ : env n) : Comp n -> CClos -> E -> Prop :=
| E_Abs q q' M ϕ :
  Qle q' q ->
  ϕ = ϵ ->
  (* ========================================== *)
  EvalComp γ ρ (cAbs q M) (CClosAbs n q' γ ρ M) ϕ

| E_CPair M1 M2 ϕ :
  ϕ = ϵ ->
  (* ================================================= *)
  EvalComp γ ρ (cPair M1 M2) (CClosPair n γ ρ M1 M2) ϕ

| E_AppAbs m q M M' V T W γ' γ1 γ2 ρ' ϕ1 ϕ2 ϕ :
  EvalComp γ1 ρ M (CClosAbs m q γ' ρ' M') ϕ1 ->
  EvalVal γ2 ρ V W ->
  EvalComp (q .: γ') (W .: ρ') M' T ϕ2 ->
  γ = γ1 Q+ (q Q* γ2) ->
  ϕ = ϕ1 E+ ϕ2 ->
  (* ======================================== *)
  EvalComp γ ρ (cApp M V) T ϕ

| E_Split q V N W1 W2 T γ1 γ2 ϕ :
  EvalVal γ1 ρ V (VClosPair W1 W2) ->
  EvalComp (q .: (q .: γ2)) (W1 .: (W2 .: ρ)) N T ϕ ->
  γ = (q Q* γ1) Q+ γ2 ->
  (* ================================================ *)
  EvalComp γ ρ (cSplit q V N) T ϕ

| E_Ret q V W γ' ϕ :
  EvalVal γ' ρ V W ->
  γ = q Q* γ' ->
  ϕ = ϵ ->
  (* ==================================== *)
  EvalComp γ ρ (cRet q V) (CClosRet q W) ϕ

(* NOTE: this rule is modified to match the
   q or 1 rule of the resource semantics.
   If q is 0, then it would make sense to rewrite the
   expression using cLet0 instead of with cLet 0.
 *)
| E_LetRet q' q1 q2 M N W T γ1 γ2 ϕ1 ϕ2 ϕ :
  q' = q_or_1 q2 ->
  EvalComp γ1 ρ M (CClosRet q1 W) ϕ1 ->
  EvalComp (Qmult q1 q' .: γ2) (W .: ρ) N T ϕ2 ->
  γ = (q' Q* γ1) Q+ γ2 ->
  ϕ = ϕ1 E+ ϕ2 ->
  (* ========================================== *)
  EvalComp γ ρ (cLet q2 M N) T ϕ

| E_ForceThunk m V M T  γ' ρ' ϕ :
  EvalVal γ ρ V (VClosThunk m γ' ρ' M) ->
  EvalComp γ' ρ' M T ϕ ->
  (* ===================================== *)
  EvalComp γ ρ (cForce V) T ϕ

| E_Fst m M M1 M2 T γ' ρ' ϕ1 ϕ2 ϕ :
  EvalComp γ ρ M (CClosPair m γ' ρ' M1 M2) ϕ1 ->
  EvalComp γ' ρ' M1 T ϕ2 ->
  ϕ = ϕ1 E+ ϕ2 ->
  (* ========================================= *)
  EvalComp γ ρ (cFst M) T ϕ

| E_Snd m M M1 M2 T γ' ρ' ϕ1 ϕ2 ϕ :
  EvalComp γ ρ M (CClosPair m γ' ρ' M1 M2) ϕ1 ->
  EvalComp γ' ρ' M2 T ϕ2 ->
  ϕ = ϕ1 E+ ϕ2 ->
  (* ========================================= *)
  EvalComp γ ρ (cSnd M) T ϕ

| E_Seq V N T γ1 γ2 ϕ :
  EvalVal γ1 ρ V VClosUnit ->
  EvalComp γ2 ρ N T ϕ ->
  γ = γ1 Q+ γ2 ->
  (* ======================= *)
  EvalComp γ ρ (cSeq V N) T ϕ

| E_Casel q V M1 M2 W T γ1 γ2 ϕ :
  EvalVal γ1 ρ V (VClosInl W) ->
  EvalComp (q .: γ2) (W .: ρ) M1 T ϕ ->
  γ = (q Q* γ1) Q+ γ2 ->
  Qle q Qone ->
  (* ================================= *)
  EvalComp γ ρ (cCase q V M1 M2) T ϕ

| E_Caser q V M1 M2 W T γ1 γ2 ϕ :
  EvalVal γ1 ρ V (VClosInr W) ->
  EvalComp (q .: γ2) (W .: ρ) M2 T ϕ ->
  γ = (q Q* γ1) Q+ γ2 ->
  Qle q Qone ->
  (* ================================= *)
  EvalComp γ ρ (cCase q V M1 M2) T ϕ

| E_Tick ϕ :
  γ = (0s : gradeVec n) ->
  ϕ = tick ->
  EvalComp γ ρ cTick (CClosRet Qone VClosUnit) tick

| E_CSub M T γ' ϕ :
  EvalComp γ' ρ M T ϕ ->
  γ Q<= γ' ->
  (* ================== *)
  EvalComp γ ρ M T ϕ

(* NOTE: we need to add a new evaluation rule
   for the new syntactic form. This rule does not
   require that M be pure. *)
| E_LetRetZero q1 M N W T γ1 γ2 ϕ1 ϕ2 ϕ :
  EvalComp γ1 ρ M (CClosRet q1 W) ϕ1 ->
  EvalComp (Qzero .: γ2) (W .: ρ) N T ϕ2 ->
  γ = γ2 ->
  ϕ = ϕ1 E+ ϕ2 ->
  (* ========================================== *)
  EvalComp γ ρ (cLet0 M N) T ϕ


.


End G.

Hint Constructors EvalVal G.EvalComp : general_semantics.

(* ********************************************************************** *)

(* This needs to be a logical relation between the general semantics and the resource-specialized semantics *)

Definition LRM {n} (LR : CompTy -> CClos -> CClos -> E -> Prop) (B : CompTy) (γ : gradeVec n) (ρ1 ρ2 : env n) (M1 M2 : Comp n) (ϕ : E) :=
  exists T1 T2 ϕ1 ϕ2 ,   G.EvalComp γ ρ1 M1 T1 ϕ1
                  /\ EvalComp γ ρ2 M2 T2 ϕ1
                  /\ LR B T1 T1 ϕ2
                  /\ LR B T1 T2 ϕ2
                  /\ (ϕ1 E+ ϕ2 E<= ϕ).

Fixpoint LRV (A : ValTy) (W1 : VClos) (W2 : VClos) : Prop :=
    match A with
    | VUnit => W1 = VClosUnit /\ W2 = VClosUnit
    | VThunk ϕ B =>
       exists m γ ρ1 M1 ρ2 M2,
        W1 = VClosThunk m γ ρ1 M1
        /\ W2 = VClosThunk m γ ρ2 M2
        /\ LRM LRC B γ ρ1 ρ2 M1 M2 ϕ
    | VPair A1 A2 => exists W11 W21 W12 W22,
      W1 = VClosPair W11 W12
      /\ W2 = VClosPair W21 W22
      /\ LRV A1 W11 W21 /\ LRV A2 W12 W22
    | VSum A1 A2 => exists W1' W2',
        (W1 = VClosInl W1' /\ W2 = VClosInl W2' /\ LRV A1 W1' W2')
      \/ (W1 = VClosInr W1' /\ W2 = VClosInr W2' /\ LRV A2 W1' W2')
    end
  with LRC (B : CompTy) (T1 : CClos) (T2 : CClos) (ϕ : E) :=
    match B with
    | CF q A =>
        ϕ = ϵ  (* return is pure *)
        /\ ((q = Qzero -> exists W1 W2,
              T1 = CClosRet q W1 /\ T2 = CClosRet q W2
              /\ (W2 = W1 \/ W2 = JUNK)
              /\ LRV A W1 W1)
           /\ (q <> Qzero -> exists W1 W2,
              T1 = CClosRet q W1 /\ T2 = CClosRet q W2
              /\ LRV A W1 W1 /\ LRV A W1 W2))
    | CPair B1 B2 =>
        exists m γ ρ1 M11 M12 ρ2 M21 M22,
        T1 = CClosPair m γ ρ1 M11 M12
        /\ T2 = CClosPair m γ ρ2 M21 M22
        /\ LRM LRC B1 γ ρ1 ρ2 M11 M21 ϕ
        /\ LRM LRC B2 γ ρ1 ρ2 M12 M22 ϕ
    | CAbs q A B => exists m γ ρ1 ρ2  M1 M2,
         T1 = CClosAbs m q γ ρ1 M1
        /\ T2 = CClosAbs m q γ ρ2 M2
        /\ ((q = Qzero /\
            (forall W1, LRV A W1 W1 ->
                  LRM LRC B (Qzero .: γ) (W1 .: ρ1) (JUNK .: ρ1) M1 M1 ϕ /\
                  LRM LRC B (Qzero .: γ) (W1 .: ρ1) (JUNK .: ρ2) M1 M2 ϕ))
            \/ (q <> Qzero /\
              (forall W1 W2,
                  LRV A W1 W1 -> LRV A W1 W2 ->
                  LRM LRC B (q .: γ) (W1 .: ρ1) (W1 .: ρ1) M1 M1 ϕ /\
                  LRM LRC B (q .: γ) (W1 .: ρ1) (W2 .: ρ2) M1 M2 ϕ)))
    end.

Scheme ValTy_ind' := Induction for ValTy Sort Prop
    with CompTy_ind' := Induction for CompTy Sort Prop.

Combined Scheme ty_mutual from ValTy_ind', CompTy_ind'.

Definition ρ_ok {n} γ ρ1 ρ2 Γ :=
  (forall (i : fin n), LRV (Γ i) (ρ1 i) (ρ1 i)) /\
  forall (i : fin n), (γ i = Qzero) \/ (γ i <> Qzero /\ LRV (Γ i) (ρ1 i) (ρ2 i)).

Definition SemVWt {n} (γ : gradeVec n) (Γ : context n) V1 V2 A :=
  forall ρ1 ρ2, ρ_ok γ ρ1 ρ2 Γ ->
           exists W1 W2, EvalVal γ ρ1 V1 W1 /\ EvalVal γ ρ2 V2 W2 /\ LRV A W1 W1 /\ LRV A W1 W2.

Definition SemCWt {n} (γ : gradeVec n) (Γ : context n) M1 M2 B ϕ :=
  forall ρ1 ρ2, ρ_ok γ ρ1 ρ2 Γ -> LRM LRC B γ ρ1 ρ2 M1 M2 ϕ.

Lemma ρ_ok_cons0 n γ ρ1 ρ2 (Γ : context n) W1 A
  (H0 : LRV A W1 W1)
  (H2 : ρ_ok γ ρ1 ρ2 Γ) :
  ρ_ok (Qzero .: γ) (W1 .: ρ1) (JUNK .: ρ2) (A .: Γ).
Proof.
  unfold ρ_ok in *.
  unfold scons.
  destruct H2.
  split; intros i; destruct i; eauto.
Qed.

Lemma ρ_ok_cons {n q γ ρ1 ρ2}{Γ : context n}{W1 W2 A}
  (H0 : LRV A W1 W1)
  (H1 : q = Qzero \/ (q <> Qzero /\ LRV A W1 W2))
  (H2 : ρ_ok γ ρ1 ρ2 Γ) :
  ρ_ok (q .: γ) (W1 .: ρ1) (W2 .: ρ2) (A .: Γ).
Proof.
  unfold ρ_ok in *. unfold scons.
  destruct H2.
  split; intros i; destruct i; eauto.
Qed.

Lemma ρ_ok_cons2 n q1 q2 γ ρ1 ρ2  (Γ : context n) W1 W1' W2 W2' A1 A2
  (H0 : LRV A1 W1 W1)
  (H00 : LRV A2 W2 W2)
  (H1 : (q1 = Qzero) \/ (q1 <> Qzero /\ LRV A1 W1 W1'))
  (H2 : (q2 = Qzero) \/ (q2 <> Qzero /\ LRV A2 W2 W2'))
  (H3 : ρ_ok γ ρ1 ρ2 Γ) :
  ρ_ok (q1 .: (q2 .: γ)) (W1 .: (W2 .: ρ1)) (W1' .: (W2' .: ρ2)) (A1 .: (A2 .: Γ)).
Proof. apply ρ_ok_cons; try apply ρ_ok_cons; try assumption. Qed.


Lemma ρ_ok_sum : forall {n}{γ : gradeVec n}{ γ1 γ2 ρ1 ρ2 Γ},
  γ = γ1 Q+ γ2 -> ρ_ok γ ρ1 ρ2 Γ ->
  ρ_ok γ1 ρ1 ρ2 Γ /\ ρ_ok γ2 ρ1 ρ2 Γ.
Proof.
  intros. unfold ρ_ok in *.
  destruct H0.
  repeat split; eauto; subst.
  - intros i.
    move: (H1 i) => [E |[NE LR]].
    + unfold gradeVecAdd in E.
      edestruct Qsumzero. rewrite -> E. eauto with coeffects. left; auto.
    + destruct (Qeq_dec (γ1 i) Qzero). left. auto. right. auto.
  - intros i.
    move: (H1 i) => [E |[NE LR]].
    + unfold gradeVecAdd in E.
      edestruct Qsumzero. rewrite -> E. eauto with coeffects. left; auto.
    + destruct (Qeq_dec (γ2 i) Qzero). left. auto. right. auto.
Qed.

Lemma dist_prod {n}{q}{γ : gradeVec n}{i} :  (q Q* γ) i = Qmult q (γ i).
  unfold "Q*". auto.
Qed.

Lemma ρ_ok_diag : forall {n} {γ : gradeVec n} {ρ1 ρ2 Γ},
  ρ_ok γ ρ1 ρ2 Γ ->
  ρ_ok γ ρ1 ρ1 Γ.
Proof. intros.
       unfold ρ_ok in *.
       destruct H.
       split; eauto.
       intros i; eauto.
       destruct (Qeq_dec (γ i) Qzero). left. auto.
       right. split; auto.
Qed.

Lemma ρ_ok_diag_any : forall {n} {γ1: gradeVec n} {ρ Γ},
  ρ_ok γ1 ρ ρ Γ -> forall γ2,
  ρ_ok γ2 ρ ρ Γ.
Proof.
  intros.
  unfold ρ_ok in *.
  destruct H. split; eauto.
  intros i; eauto.
  destruct (Qeq_dec (γ2 i) Qzero).
  left. auto.
  right. eauto.
Qed.

Lemma ρ_ok_prod : forall {n q}{γ : gradeVec n}{ρ1 ρ2 Γ},
  ρ_ok (q Q* γ) ρ1 ρ2 Γ ->
  ((q = Qzero) \/ (q <> Qzero /\ ρ_ok γ ρ1 ρ2 Γ)).
Proof.
  intros.
  destruct H as [h1 h2].
  destruct Qeq_dec with (q1 := q) (q2 := Qzero) as [Heq | Hneq].
  left. auto.
  right. split. auto.
  unfold ρ_ok. split. auto.
  intros i; specialize h2 with i as [H0 | H0]; firstorder.
  left. unfold gradeVecScale in H0. apply Qprodzero in H0 as [H0 | H0]; firstorder.
  right. split; auto.
  rewrite dist_prod in H.
  intro h. rewrite h in H. autorewrite with coeffects in H. apply H. auto.
Qed.

Lemma ρ_ok_le : forall {n}{γ γ' : gradeVec n}{ρ1 ρ2 Γ},
  gradeVecLe γ γ' ->
  ρ_ok γ ρ1 ρ2 Γ ->
  ρ_ok γ' ρ1 ρ2 Γ.
Proof.
  unfold ρ_ok in *. intros.
  destruct H0 as [gh h].
  unfold gradeVecLe in H.
  split; auto. intro i.
  specialize H with i.
  specialize h with i as [h0 | [h0 h1]]; auto. left.
  rewrite h0 in H. apply Q_lt_zero in H. auto.
  destruct (Qeq_dec (γ' i) Qzero). left. auto.
  right. split; auto.
Qed.

Lemma ST_CSub {n:nat} {γ:gradeVec n}{ Γ M1 M2 B γ' ϕ }:
  SemCWt γ' Γ M1 M2 B ϕ ->
  γ Q<= γ' ->
  (* --------------- *)
  SemCWt γ Γ M1 M2 B ϕ.
Proof.
  unfold SemCWt. intros IH IHγ ρ1 ρ2 H.
  specialize IH with ρ1 ρ2. eapply ρ_ok_le in H.
  apply IH in H as [T1 [T2 [ϕ1 [ϕ2 [HTE1 [HTE2 [HTL1 [HTL2 Hle]]]]]]]].
  repeat eexists; eauto.
  eapply G.E_CSub; eauto.
  eapply E_CSub; eauto.
  auto.
Qed.


Lemma ST_ESub {n:nat} {γ:gradeVec n}{ Γ M1 M2 B ϕ ϕ' }:
  SemCWt γ Γ M1 M2 B ϕ ->
  ϕ E<= ϕ' ->
  (* --------------- *)
  SemCWt γ Γ M1 M2 B ϕ'.
Proof.
  unfold SemCWt.
  intros IH IHe ρ1 ρ2 H.
  specialize (IH ρ1 ρ2 H).
  move: IH => [T1 [T2 [ϕ1 [ϕ2 [HTE1 [HTE2 [HTL1 [HTL2 Hle]]]]]]]].
  repeat eexists; eauto with effects.
Qed.


Lemma fundamental : forall n (γ : gradeVec n) (Γ : context n),
  (forall V A, VWt γ Γ V A -> SemVWt γ Γ V V A) /\
  (forall M B ϕ, CWt γ Γ M B ϕ -> SemCWt γ Γ M M B ϕ).
Proof.
  apply Wt_mutual.
  all: intros n γ Γ.
  - (* var *)
    intros i P Q.
    intros ρ1 ρ2 Hρ.
    unfold ρ_ok in Hρ. destruct Hρ as [h1 h2].
    destruct (h2 i). rewrite P in H. eapply Qnontrivial in H. done.
    destruct H as [NZ LR].
    exists (ρ1 i). exists (ρ2 i).
    repeat split; eauto using E_Var.
  - (* thunk *)
    intros M B ϕ TM IHM.
    intros ρ1 ρ2 Hρ.
    destruct (IHM _ _ Hρ) as
      [T1 [T2 [ϕ1 [ϕ2 [ET1 [EHT2 [R1 [R12 Hle]]]]]]]].
    move: (IHM _ _ (ρ_ok_diag Hρ)) => HD.

    eexists. eexists.
    repeat split; eauto with semantics.
    simpl.
    eexists. eexists. eexists. eexists. eexists. eexists.
    repeat split; eauto.
    simpl.
    eexists. eexists. eexists. eexists. eexists. eexists.
    repeat split; eauto.
  - (* unit *)
    intros ->. intros ρ1 ρ2 Hρ.
    eexists. eexists. repeat split; eauto with semantics.
  - (* pair *)
    intros.
    intros ρ1 ρ2 Hρ.
    move: (ρ_ok_sum e Hρ) => [h0 h1].
    destruct (H0 _ _ h1) as [W1 [W2 [EW1 [EW2 [RW1 RW12]]]]].
    destruct (H _ _ h0) as [W1' [W2' [EW1' [EW2' [RW1' RW12']]]]].
    eexists. eexists.
    repeat split; eauto with semantics.
    simpl. repeat eexists; auto.
    simpl. repeat eexists; auto.
  - (* inl *)
    intros.
    intros ρ1 ρ2 Hρ.
    move: (H _ _ Hρ) => [W1 [W2 [EW1 [EW2 [RW1 RW12]]]]].
    eexists. eexists.
    repeat split; eauto with semantics.
    simpl. repeat eexists; auto.
    simpl. repeat eexists; auto.
  - (* inr *)
    intros.
    intros ρ1 ρ2 Hρ.
    move: (H _ _ Hρ) => [W1 [W2 [EW1 [EW2 [RW1 RW12]]]]].
    eexists. eexists.
    repeat split; eauto with semantics.
    simpl. repeat eexists; auto.
    simpl. repeat eexists; auto.
  - (* sub *)
   intros.
    intros ρ1 ρ2 Hρ.
    move: (ρ_ok_le g Hρ) => Hρ'.
    move: (H _ _ Hρ') => [W1 [W2 [EW1 [EW2 [RW1 RW12]]]]].
    eexists. eexists.
    repeat split; eauto with semantics.
  - (* abs *)
    intros. intros ρ1 ρ2 Hρ.
    destruct (Qeq_dec q' Qzero) as [-> | h].
    + (* zero *)
      unfold LRM.
      apply Q_lt_zero in l. subst q. simpl.
      eexists. eexists. exists ϵ. exists ϕ.
      repeat split.
      ++ eapply G.E_Abs with (q' := Qzero); eauto with coeffects.
      ++ eapply E_Abs with (q' := Qzero); eauto with coeffects.
      ++ eexists. eexists. eexists. eexists. exists M. exists M.
         repeat split; auto.
         left. repeat split; auto.
         eapply H; eauto using ρ_ok_cons, ρ_ok_diag.
         eapply H; eauto using ρ_ok_cons, ρ_ok_diag.
      ++ eexists. eexists. eexists. eexists. exists M. exists M.
         repeat split; auto.
         left. repeat split; auto.
         eapply H; eauto using ρ_ok_cons, ρ_ok_diag.
         eapply H; eauto using ρ_ok_cons, ρ_ok_diag.
      ++ autorewrite with effects. eauto with effects.
    + (* nonzero *)
      eexists. eexists. exists ϵ. exists ϕ.
      repeat split.
      ++ eapply G.E_Abs; eauto.
      ++ eapply E_Abs; eauto.
      ++ eexists. eexists. eexists.  eexists. exists M. exists M.
         repeat split. right. split; auto.
         intros W1 W2 LW1 LW1W2.
         eapply @ST_CSub with (γ := q' .: γ) in H. 2: { eauto with coeffects. }
         split;
         eapply H; eauto using ρ_ok_cons, ρ_ok_diag.
      ++ eexists. eexists. eexists.  eexists. exists M. exists M.
         repeat split. right. split; auto.
         intros W1 W2 LW1 LW1W2.
         eapply @ST_CSub with (γ := q' .: γ) in H. 2: { eauto with coeffects. }
         split;
         eapply H; eauto using ρ_ok_cons, ρ_ok_diag.
      ++ autorewrite with effects. eauto with effects.
  - (* APP *)
    intros. unfold SemCWt. intros.
    rewrite e in H1.
    eapply ρ_ok_sum in H1; eauto. destruct H1 as [h0 h1].
    move: (ρ_ok_prod h1) =>OK.
    move: (ρ_ok_diag_any (ρ_ok_diag h1) γ2) => OK2.
    (* induction hypothesis for M *)
    unfold SemCWt in H. specialize H with ρ1 ρ2 as Hg1.
    apply Hg1 in h0 as [T1 [T2 [ϕ1 [ϕ2 [HT1'eval [HT2'eval [R1 [R12 Hle']]]]]]]]. clear Hg1.
    destruct R12 as [m [γ' [ρ1' [ρ2' [M1' [M2' [-> [-> h0]]]]]]]].

    destruct OK as [-> |[ne h2]].
    + (* q = 0 *)
      destruct h0. 2: { destruct  H1. done. }
      move: H1 => [_ H1].
      (* IH for V *)
      move: (H0 _ _ OK2) => [W1 [W2 [EV1 [EV2 [RW1 RW12]]]]].
      move: (H1 _ RW1) =>
        [_
         [T1'' [T2'' [ϕ1'' [ϕ2'' [ET1'' [ET2'' [RT11'' [RT12'' Hle''']]]]]]]]].
      unfold LRM.
      exists T1''. exists T2''. eexists. eexists.
      repeat split.
      ++ eapply @G.E_AppAbs with (W := W1); eauto with coeffects effects.
      ++ autorewrite with coeffects in e. subst.
         eapply E_AppAbsZero; eauto with coeffects effects.
      ++ eauto.
      ++ eauto.
      ++ rewrite eff_assoc. eauto with effects.
    + (* q <> 0 *)
      destruct h0 as [[t _]|[_ LRB]].  done.

      (* induction hypothesis for V *)
      move: (H0 ρ1 ρ2 h2) => [W1 [W2 [EV1 [EV2 [RW1 RW1W2]]]]].
      move: (LRB _ _ RW1 RW1W2) =>
        [_
         [T1'' [T2'' [ϕ1'' [ϕ2'' [ET1'' [ET2'' [RT11'' [RT12'' Hle''']]]]]]]]].
      unfold LRM.
      exists T1''. exists T2''. eexists. eexists.
      repeat split.
      ++ eapply @G.E_AppAbs with (W := W1); eauto with coeffects effects.
      ++ autorewrite with coeffects in e. subst.
         eapply E_AppAbs; eauto with coeffects effects.
      ++ eauto.
      ++ eauto.
      ++ rewrite eff_assoc. eauto with effects.
  - (* force *)
    unfold SemVWt, SemCWt.
    intros.
    move: (H _ _ H0) => [W1 [W2 [h2 [h3 [h4 h5]]]]].
    simpl in h4.
    move: h4 => [m' [γ' [ρ1' [M1' [ρ' [M2' h]]]]]].
    move: h => [h1' [h2' h3']].
    simpl in h5.
    move: h5 => [m'' [γ'' [ρ1'' [M1'' [ρ'' [M2'' h]]]]]].
    move: h => [h1'' [h2'' h3'']].
    subst.
    destruct h3' as [T1 [T2 [ϕ1' [ϕ2' [HTE1 [HTE2 [HTL1 [HTL2 Hle]]]]]]]].
    destruct h3'' as [T1' [T2' [ϕ1'' [ϕ2'' [HTE1' [HTE2' [HTL1' [HTL2' Hle']]]]]]]].

    unfold LRM.
    rewrite h1'' in h2.
    exists T1'. exists T2'. exists ϕ1''. exists ϕ2''.
    repeat split; eauto with general_semantics semantics.
  - (* split *)
    unfold SemCWt, SemVWt.
    intros.
    move: (ρ_ok_sum e H1) => [Hqγ1 OK2].
    move: (ρ_ok_prod Hqγ1) => [qe | [qne OK1]].
    + (* zero *)
      subst.
      autorewrite with coeffects.
      move: (ρ_ok_diag_any (ρ_ok_diag H1) γ1) => OK1.
      move: (H _ _ OK1) => [W1 [W2 [h2 [h3 [h4 h5]]]]].
      clear H.
      (* use IH for V *)
      simpl in h4.
      move: h4 => [W11 [W21 [W12 [W22 [E1 [E2 [R11 R12]]]]]]].
      rewrite E1 in E2. inversion E2. subst. clear E2.
      (*  use IH for N *)
      edestruct H0 as [T1 [T2 [ϕ1' [ϕ2' [HTE1 [HTE2 [HTL1 [HTL2 Hle]]]]]]]].
      eapply ρ_ok_cons. eapply R11. left; auto.
      eapply ρ_ok_cons. eapply R12. left; auto.
      eapply OK2.
      (* LRM *)
      eexists. eexists. eexists. eexists.
      repeat split; eauto.
      eapply G.E_Split; eauto. autorewrite with coeffects. auto.
      eapply E_SplitZero; eauto.
    + (* nonzero *)
      (* use IH for V *)
      move: (H _ _ OK1) => [W1 [W2 [h2 [h3 [h4 h5]]]]].
      clear H.
      simpl in h4.
      move: h4 => [W11' [W21' [W12' [W22' [E1' [E2' [R11' R12']]]]]]].
      simpl in h5.
      move: h5 => [W11 [W21 [W12 [W22 [E1 [E2 [R11 R12]]]]]]].
      subst. inversion E2'. inversion E1. subst.
      (*  use IH for N *)
      move: (ρ_ok_cons R12' (or_intror (conj qne R12)) OK2) => h.
      move: (ρ_ok_cons R11' (or_intror (conj qne R11)) h) => OK.
      edestruct (H0 _ _ OK)
        as [T1 [T2 [ϕ1' [ϕ2' [HTE1 [HTE2 [HTL1 [HTL2 Hle]]]]]]]].
      clear H0 h.
      (* LRM *)
      eexists. eexists. eexists. eexists.
      repeat split; eauto with semantics general_semantics.
  - (* ret *)
    intros. subst.
    intros ρ1 ρ2 Hρ.
    move: (ρ_ok_diag_any (ρ_ok_diag Hρ) γ1) => OK1.
    move: (ρ_ok_prod Hρ) => [h0 | [h1 OK2]].
    + (* q is zero *)
      subst. autorewrite with coeffects.
      move: (H _ _ OK1) => [W1 [W2 [h3 [h4 [h5 h6]]]]].

      eexists. eexists. eexists. eexists.
      repeat split; eauto with general_semantics semantics.
      instantiate (1 := CClosRet Qzero W1).
      eapply G.E_Ret; eauto. autorewrite with coeffects. auto.
      intro h. exists W1. exists W1. repeat split; eauto.
      intro h. done.
      intro h. exists W1. exists JUNK. repeat split; eauto.
      intro h. done.
      autorewrite with effects. eauto with effects.
    + (* q is nonzero *)
      move: (H _ _ OK2) => [W1 [W2 [h2 [h3 [h4 h5]]]]].
      eexists. eexists. eexists. eexists.
      repeat split; eauto with general_semantics semantics.
      intros _. eexists. eexists. repeat split; eauto.
      intros _. eexists. eexists. repeat split; eauto.
      intros h. done.
      intros _. exists W1. exists W2. repeat split; eauto.
      autorewrite with effects. eauto with effects.

  - (* let *)
    intros.
    intros ρ1 ρ2 Hρ.
    (* split up the resources *)
    move: (ρ_ok_sum e0 Hρ) => [OKM hg2].
    move: (ρ_ok_prod OKM) => [hg1 | [h1 hg1]].
    + (* this is a contradiction: q' cannot be zero *)
      exfalso. subst. remember (q_or_1_neq_0 q2) as Hc.
      destruct Hc as [Hc | Hc]; try contradiction.
      apply Qnontrivial; auto.
    + (* q' <> 0 *)
    (* Induction hypothesis for M *)
    destruct (H _ _ hg1) as
      [T1 [T2 [ϕ1' [ϕ2' [HTE1 [HTE2 [HTL1 [HTL2 Hle]]]]]]]]. clear H.
    simpl in HTL2.
    move: HTL2 => [EE [q1z q1nz]].
    destruct (Qeq_dec q1 Qzero).
    ++ (* q1 = 0 *)
      specialize (q1z H). clear q1nz.
      subst q1.
      rewrite Qzero_lannihilates in H0.
      move: q1z => [W1 [W2 [ET1 [ET2 [EQO RWW]]]]].
      subst T1. subst T2.
      destruct EQO as [SAME | EJUNK].
      +++ (* diagonal == same results case *)
        have OKN2: (ρ_ok (Qzero .: γ2)
                      (W1 .: ρ1) (W2 .: ρ2) (A .: Γ)).
        eapply ρ_ok_cons; eauto.
        move: (H0 _ _ OKN2) =>
              [Ts1 [Ts2 [ϕs1 [ϕs2 [HTEs1 [HTEs2 [HTLs1 [HTLs2 Hles]]]]]]]].
        subst.
        exists Ts1. exists Ts2. exists (ϕ1' E+ ϕs1). exists ϕs2.
        repeat split.
        eapply G.E_LetRet with (q' := q_or_1 q2) (q1 := Qzero); eauto.
        rewrite Qzero_lannihilates.
        eapply HTEs1.
        eapply E_LetRet with (q' := q_or_1 q2) (q1 := Qzero); eauto; eauto.
        rewrite Qzero_lannihilates.
        eapply HTEs2.
        eauto.
        eauto.
        rewrite eff_assoc.
        eauto with effects.
      +++ (* JUNK case *)
        have OKN1: (ρ_ok (Qzero .: γ2)
                      (W1 .: ρ1) (JUNK .: ρ2) (A .: Γ)).
        eapply ρ_ok_cons; eauto.
        move: (H0 _ _ OKN1) =>
              [Td1 [Td2 [ϕd1 [ϕd2 [HTEd1 [HTEd2 [HTLd1 [HTLd2 Hlde]]]]]]]].
        subst.
        exists Td1. exists Td2. exists (ϕ1' E+ ϕd1). exists ϕd2.
        repeat split.
        eapply G.E_LetRet with (q' := q_or_1 q2) (q1 := Qzero); eauto.
        rewrite Qzero_lannihilates.
        eapply HTEd1.
        eapply E_LetRet with (q' := q_or_1 q2) (q1 := Qzero); eauto; eauto.
        rewrite Qzero_lannihilates.
        eapply HTEd2.
        eauto.
        eauto.
        rewrite eff_assoc.
        eauto with effects.
    ++ (* q1 <> 0 *)
      specialize (q1nz H). clear q1z.
      move: q1nz => [W1 [W2 [ET1 [ET2 [RWW RW12]]]]].
      have OKN1: (ρ_ok (Qmult q1 q' .: γ2)
                  (W1 .: ρ1) (W2 .: ρ2) (A .: Γ)).
      eapply ρ_ok_cons; eauto.
      right. split; auto.
      intro h. apply Qprodzero in h.
      destruct h as [EQ | EQ]; try done.
      move: (H0 _ _ OKN1) =>
      [T1' [T2' [ϕ1'' [ϕ2'' [HTE1' [HTE2' [HTL1' [HTL2' Hle']]]]]]]].
      subst T1. subst T2.
      simpl in HTL1.
      move: HTL1 => [EQ [_ h]].
      destruct h as [W1' [W2' [h1' [h2' [h3' h4']]]]].
      auto.
      eexists. eexists. eexists. eexists.
      repeat split; eauto with general_semantics semantics.
      rewrite eff_assoc.
      subst ϕ. eauto with effects.
  - (* cpair *)
    unfold SemCWt. intros.
    move: (H _ _ H1) => IH1.
    move: (H _ _ (ρ_ok_diag H1)) => IH2.
    move: (H0 _ _ H1) => IH3.
    move: (H0 _ _ (ρ_ok_diag H1)) => IH4.

    unfold LRM.
    eexists (CClosPair _ γ ρ1 M1 M2).
    eexists (CClosPair _ γ ρ2 M1 M2).
    eexists ϵ. eexists ϕ.
    repeat split; eauto with general_semantics semantics.
    simpl.
    eexists. eexists. eexists. eexists.
    eexists. eexists. eexists. eexists.
    repeat split; eauto.
    simpl.
    eexists. eexists. eexists. eexists.
    eexists. eexists. eexists. eexists.
    repeat split; eauto.
    autorewrite with effects; eauto with effects.

  - (* cfst *)
    unfold SemCWt. intros.
    move: (H _ _ H0) => IH1.
    move: (H _ _ (ρ_ok_diag H0)) => IH2.
    unfold LRM.
    destruct IH1 as [T1 [T2 [ϕ1 [ϕ2 [HTE1 [HTE2 [HTL1 [HTL2 Hle]]]]]]]].
    destruct IH2 as [T1' [T2' [ϕ1' [ϕ2' [HTE1' [HTE2' [HTL1' [HTL2' Hle']]]]]]]].
    simpl in HTL2.
    destruct HTL2 as [m3 [γ3 [ρ3 [M31 [M32 [ρ4 [M41 [M42
                     [h1 [h2 [h3 _]]]]]]]]]]].
    subst.
    destruct h3 as [T31 [T32 [ϕ31 [ϕ32 [HTE31 [HTE32 [HTL31 [HTL32 Hle3]]]]]]]].
    exists T31. exists T32. exists (ϕ1 E+ ϕ31). eexists.

    repeat split; eauto with general_semantics semantics.
    rewrite eff_assoc. eauto with effects.
  - (* csnd *)
    unfold SemCWt. intros.
    move: (H _ _ H0) => IH1.
    move: (H _ _ (ρ_ok_diag H0)) => IH2.
    unfold LRM.
    destruct IH1 as [T1 [T2 [ϕ1 [ϕ2 [HTE1 [HTE2 [HTL1 [HTL2 Hle]]]]]]]].
    destruct IH2 as [T1' [T2' [ϕ1' [ϕ2' [HTE1' [HTE2' [HTL1' [HTL2' Hle']]]]]]]].
    simpl in HTL2.
    destruct HTL2 as [m3 [γ3 [ρ3 [M31 [M32 [ρ4 [M41 [M42
                     [h1 [h2 [_ h4]]]]]]]]]]].
    subst.
    destruct h4 as [T31 [T32 [ϕ31 [ϕ32 [HTE31 [HTE32 [HTL31 [HTL32 Hle3]]]]]]]].
    exists T31. exists T32. exists (ϕ1 E+ ϕ31). eexists.

    repeat split; eauto with general_semantics semantics.
    rewrite eff_assoc. eauto with effects.

  - (* cseq *)
    unfold SemVWt, SemCWt. intros.
    move: (ρ_ok_sum e H1) => [OKV OKN].
    move: (H _ _ OKV) => [W1 [W2 [h2 [h3 [h4 h5]]]]].
    clear H.
    simpl in h5. move: h5 => [e1 e2]. subst.
    move: (H0 _ _ OKN) => [T1 [T2 [ϕ1 [ϕ2 [HTE1 [HTE2 [HTL1 [HTL2 Hle]]]]]]]].
    clear H0.

    eexists. eexists. eexists. eexists.
    repeat split; eauto with general_semantics semantics.
  - (* ccase *)
    unfold SemVWt, SemCWt. intros.
    move: (ρ_ok_sum e H2) => [OKV' OKN].
    move: (ρ_ok_prod OKV') => [h| [h OKV]].
    + (* q = 0 *)
      subst.
      eapply Q_one_lt_zero in l.
      done.
    + (* q <> 0 *)
      move: (H _ _ OKV) => [W1 [W2 [h2 [h3 [h4 h5]]]]]. clear H.
      simpl in h4.
      move: h4 => [W1' [W2' [[h6 [h7 h8]]|[h6 [h7 h8]]]]].
      ++ (* inl *)
        subst. inversion h7. subst. clear h7.
        simpl in h5.
        move: h5 => [W1'' [W2'' [[h6' [h7' h8']]|[h6' [h7' h8']]]]].
        2: { subst. discriminate. }
        subst. inversion h6'. clear h6'. subst.
        edestruct H0 as [T1 [T2 [ϕ1 [ϕ2 [HTE1 [HTE2 [HTL1 [HTL2 Hle]]]]]]]].
        eapply ρ_ok_cons; eauto.
        eexists. eexists. eexists. eexists.
        repeat split; eauto with general_semantics semantics.
      ++ (* inr *)
        subst. inversion h7. subst. clear h7.
        simpl in h5.
        move: h5 => [W1'' [W2'' [[h6' [h7' h8']]|[h6' [h7' h8']]]]].
        { subst. discriminate. }
        subst. inversion h6'. clear h6'. subst.
        edestruct H1 as [T1 [T2 [ϕ1 [ϕ2 [HTE1 [HTE2 [HTL1 [HTL2 Hle]]]]]]]].
        eapply ρ_ok_cons; eauto.
        eexists. eexists. eexists. eexists.
        repeat split; eauto with general_semantics semantics.

  - (* tick *)
    intros. subst.
    intros ρ1 ρ2 Hρ.
    repeat eexists; eauto with general_semantics semantics.
    autorewrite with effects. eauto with effects.
  - (* csub *)
    eauto using ST_CSub.

  - (* esub *)
    eauto using ST_ESub.

  - (* let0 *)

    intros.
    have EQ: γ = (Qzero Q* γ1) Q+ γ2.
    autorewrite with coeffects. auto.
    intros ρ1 ρ2 Hρ.

    rewrite EQ in Hρ.
    eapply ρ_ok_sum in Hρ; eauto. destruct Hρ as [h0 h1].
    move: (ρ_ok_diag_any (ρ_ok_diag h1) γ1) => OK1.

    (* IH for M *)
    move: (H _ _ OK1) => [T1 [T2 [ϕ1 [Φ2 [h2 [h3 [h4 [h5 h6]]]]]]]].
    simpl in h4.
    move: h4 => [eq [q1z q1nz]].
    simpl in h5.
    move: h5 => [_ [q1z' q1nz']].

    destruct (Qeq_dec q1 Qzero).
    + specialize (q1z H1).
      move: (q1z' H1) => [W1 [W2 [h7 [h8 [h9 h10]]]]].
      clear q1nz q1nz'.
      subst T1. subst T2.

      (* IH for N *)
      have OK': (ρ_ok (Qzero .: γ2) (W1 .: ρ1) (JUNK .: ρ2) (A .: Γ)).
      eapply ρ_ok_cons; eauto.

      move: (H0 _ _ OK') => [T1' [T2' [ϕ1' [Φ2' [h2' [h3' [h4' [h5' h6']]]]]]]].
      subst. autorewrite with effects in h6.
      apply pure_bot2 in h6. subst.
      repeat eexists; eauto with general_semantics semantics.
      eapply E_LetRetZero; eauto.
      autorewrite with coeffects.
      autorewrite with effects. eauto.
      autorewrite with effects. eauto.
    + specialize (q1nz H1).
      move: (q1nz' H1) => [W1 [W2 [h7 [h8 [h9 h10]]]]].
      clear q1z q1z' q1nz q1nz'.
      subst T1. subst T2.

      (* IH for N *)
      have OK': (ρ_ok (Qzero .: γ2) (W1 .: ρ1) (JUNK .: ρ2) (A .: Γ)).
      eapply ρ_ok_cons; eauto.

      move: (H0 _ _ OK') => [T1' [T2' [ϕ1' [Φ2' [h2' [h3' [h4' [h5' h6']]]]]]]].
      subst.
      autorewrite with effects in h6.
      apply pure_bot2 in h6. subst.
      repeat eexists; eauto with general_semantics.
      eapply E_LetRetZero; eauto.
      autorewrite with effects coeffects. eauto.
      autorewrite with effects. eauto.
Qed.


Lemma ρ_ok_null :  ρ_ok null null null null.
unfold ρ_ok. split.
intro i. destruct i. intro i. destruct i.
Qed.

Definition ret_false := (CClosRet Qone (VClosInl VClosUnit)).
Definition ret_true  := (CClosRet Qone (VClosInr VClosUnit)).

(* If a term has type F1 bool, then both semantics
   either evaluate to true or both evaluate to false. *)
Corollary resource_simulation:
  forall M ϕ,
    CWt null null M (CF Qone (VSum VUnit VUnit)) ϕ ->
    (exists ϕ1, G.EvalComp null null M ret_false ϕ1 /\
    EvalComp null null M ret_false ϕ1) \/
    (exists ϕ1, G.EvalComp null null M ret_true ϕ1 /\
    EvalComp null null M ret_true ϕ1).

Proof.
  intros.
  move: (fundamental _ null null) => [_ h].
  specialize (h M (CF Qone (VSum VUnit VUnit)) ϕ H).
  specialize (h null null ρ_ok_null).
  unfold LRM in h.
  destruct h as [T1 [T2 [ϕ1 [ϕ2 [Ev1 [Ev2 [R1 [R2 EE]]]]]]]].
  simpl in R2.
  move: R2 => [eq [_ h1]].
  specialize (h1 ltac:(eauto using Qnontrivial)).
  destruct h1 as [W1 [W2 [EQ1 [EQ2 hh]]]].
  subst. destruct hh as [_ [W1' [W2' hh]]].
  autorewrite with effects in EE.
  destruct hh as [[l1 [l2 [l3 l4]]]| [r1 [r2 [r3 r4]]]].
  + subst. left. eexists. split;  eauto.
  + subst. right. eexists. split;  eauto.
Qed.
