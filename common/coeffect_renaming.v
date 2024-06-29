Require Export cbpv.common.fin_util.
Require Export cbpv.common.coeffects.
From Coq Require Import FunctionalExtensionality.

Create HintDb renaming.


(* Renaming proofs for type systems with coeffects *)

(* A 'good' renaming from γ ⋅ Γ to γ' ⋅ Γ' :
   
    γ' = ξ ∘ γ  and Γ' = ξ ∘ Γ

   only weakening with 0
   for every index in γ', it either corresponds to an index in γ (after
   renaming) or the grade is 0

   no contraction
   the renamer is injective 

*)

Definition ren_wb {n m A} (renamer : fin n -> fin m)
    (γ : gradeVec n) (γ' : gradeVec m)
    (Γ : fin n -> A) (Γ' : fin m -> A) : Prop :=
    ren_match renamer γ γ'
    /\ ren_match renamer Γ Γ'
    /\ default_or_preimage Qzero γ' renamer
    /\ ren_inj renamer.

Definition match_ren_le {n m A} (renamer : fin n -> fin m) (γ1 γ2 : gradeVec n) (γ1' : gradeVec m)
  (Γ : fin n -> A) (Γ' : fin m -> A) :
  γ1 Q<= γ2 ->
  ren_wb renamer γ1 γ1' Γ Γ' ->
  exists γ2' , γ1' Q<= γ2' /\ ren_wb renamer γ2 γ2' Γ Γ'.
Proof.
  intros Hg [H1 [H2 [H3 H4]]].
  unfold default_or_preimage in H3. exists (match_pre_id renamer γ2 Qzero).
  repeat split. all: auto.
  - intros j. unfold match_pre_id. destruct (ren_preimage_dec renamer j).
    + subst. unfold ren_match in H1. rewrite <- H1. apply Hg.
    + specialize H3 with j as [H3 | [i H3]].
        * rewrite H3. apply Qle_refl.
        * specialize H with i. subst. contradiction.
  - apply match_pre_id_inj_sound. auto.
  - intros j. unfold match_pre_id. destruct (ren_preimage_dec renamer j). all: eauto.
Qed.

Lemma split_ren_add {n m A} (renamer : fin n -> fin m)
    (γ γ1 γ2 : gradeVec n) (γ' : gradeVec m)
    (Γ : fin n -> A) (Γ' : fin m -> A) :
    γ = γ1 Q+ γ2 ->
    ren_wb renamer γ γ' Γ Γ' ->
    exists γ1' γ2', (γ' = γ1' Q+ γ2')
        /\ ren_wb renamer γ1 γ1' Γ Γ' /\ ren_wb renamer γ2 γ2' Γ Γ'.
Proof.
    intros Hq [H1 [H2 [H3 H4]]].
    unfold default_or_preimage in H3.
    exists (match_pre_id renamer γ1 Qzero).
    exists (match_pre_id renamer γ2 Qzero).
    split; try split; try split; try split; try split;
        try apply match_pre_id_inj_sound; auto.
    apply functional_extensionality.
    intros j. unfold gradeVecAdd. unfold match_pre_id.
    destruct (ren_preimage_dec renamer j).
    - unfold ren_match in H1. specialize H1 with i. subst.
        rewrite <- H1. auto with coeffects.
    - specialize H3 with j as [H3 | [i H3]].
        + rewrite H3. autorewrite with coeffects. eauto with coeffects.
        + specialize H with i. subst. contradiction.
Qed.

Lemma split_ren_mult {n m A} (renamer : fin n -> fin m)
    (γ γ1 : gradeVec n) (γ' : gradeVec m)
    (q : Q)
    (Γ : fin n -> A) (Γ' : fin m -> A) :
    γ = q Q* γ1 ->
    ren_wb renamer γ γ' Γ Γ' ->
    exists γ1', (γ' = q Q* γ1')
        /\ ren_wb renamer γ1 γ1' Γ Γ'.
Proof.
    intros Hq [H1 [H2 [H3 H4]]].
    exists (match_pre_id renamer γ1 Qzero).
    split; try split; try split; try split; try apply match_pre_id_inj_sound; auto.
    unfold gradeVecLe. unfold gradeVecScale. apply functional_extensionality.
    intros j. unfold match_pre_id. destruct (ren_preimage_dec renamer j).
    - subst. rewrite <- H1. auto with coeffects.
    - unfold default_or_preimage in H3. specialize H3 with j as [H3 | [i H3] ].
        + rewrite H3. autorewrite with coeffects. eauto with coeffects.
        + specialize H with i. subst. contradiction.
Qed.

Lemma shift_wb {A} : forall n (γ : gradeVec n) Γ (A0 : A),
    ren_wb shift γ (Qzero .: γ) Γ (A0 .: Γ).
Proof with eauto.
    intros; split; try split; try split.
    - unfold default_or_preimage. destruct j as [j' | ]; eauto. right. exists j'. auto.
    - unfold ren_inj. intros i1 i2 H. inversion H. auto.
Qed.

Lemma up_ren_wb {A} : forall n (γ : gradeVec n) q Γ (A1 A0 : A),
    ren_wb up_ren'(q .: γ) (q .: (Qzero .: γ)) (A1 .: Γ) (A1 .: (A0 .: Γ)).
Proof with eauto.
    intros. split; try split; try split;
        try solve [unfold ren_match; intros; destruct i; auto].
    - unfold default_or_preimage. destruct j as [[j'' | ] | ]; auto; right;
        [ exists (Some j'') | exists var_zero ]; auto.
    - unfold ren_inj. intros i1 i2 H.
        destruct i1 as [i1' | ], i2 as [i2' | ]; inversion H; auto.
Qed.

Lemma up2_ren_wb {A} : forall n (γ : gradeVec n) q1 q2 Γ (A1 A2 A0 : A),
    ren_wb up2_ren' (q1 .: (q2 .: γ)) (q1 .: (q2 .: (Qzero .: γ)))
        (A1 .: (A2 .: Γ)) (A1 .: (A2 .: (A0 .: Γ))).
Proof.
    intros. split... all: try split... all: try split...
    all: try solve [unfold ren_match; intros; destruct i as [[i'' |] | ]; auto].
    - unfold default_or_preimage; destruct j as [[[j''' | ] | ] | ]; auto; right;
        [ exists (Some (Some j''')) | exists (Some None) | exists var_zero ];
        auto.
    - unfold ren_inj; intros i1 i2 H;
        destruct i1 as [[ i1'' | ] | ], i2 as [[ i2'' | ] | ];
        inversion H; auto.
Qed.

Lemma upRen_wb {A} : forall n m (renamer : ren n m)
    γ γ' q Γ Γ' (A0 : A),
    ren_wb renamer γ γ' Γ Γ' ->
    ren_wb (up_ren renamer) (q .: γ)
        (q .: γ') (A0 .: Γ) (A0 .: Γ').
Proof.
    intros. destruct H as [H1 [H2 [H3 H4]]]. split... all: try split...
    all: try solve [unfold ren_match in *; intros; destruct i as [i'| ];
        auto; cbn; specialize H1 with i'; auto]. split...
    - unfold default_or_preimage in *.
        intros. destruct j as [j'| ].
        + specialize H3 with j' as [H3 | [i H3]].
            * left. auto.
            * right. exists (Some i). rewrite H3. auto.
        + right. exists var_zero. auto.
    - unfold ren_inj. intros.
        destruct i1 as [i1' | ], i2 as [i2' | ]; inversion H; auto.
        f_equal. apply H4. auto.
Qed.

#[global] Hint Resolve shift_wb up_ren_wb up2_ren_wb : renaming.
