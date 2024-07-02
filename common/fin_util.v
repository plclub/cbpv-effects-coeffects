Require Export autosubst2.fintype.

(* Boolean equality of finite sets *)
Definition fin_eqb {n} : fin n -> fin n -> bool.
Proof.
    induction n.
    - intros. contradiction.
    - intros i1 i2. destruct i1 as [i1' | ] eqn: H1, i2 as [i2' | ] eqn: H2.
        + (*i1 = Some i1', i2 = Some i2'*)
            destruct (IHn i1' i2') eqn: IHe.
            * (*i1' = i2'*) apply true.
            * (*i1' <> i2'*) apply false.
        + (*i1 = Some i1', i2 = None*) apply false.
        + (*i1 = None, i2 = Some i2'*) apply false.
        + (*i1 = None, i2 = None*) apply true.
Defined.

(* Boolean equality of finite sets corresponds to propositional equality *)
Lemma fin_eqb_eq : forall n (i1 i2 : fin n),
    fin_eqb i1 i2 = true <-> i1 = i2.
Proof.
    induction n.
    - intros. contradiction.
    - intros. split; intros H.
        + destruct i1 as [i1' | ], i2 as [i2' | ]; try inversion H; auto.
            f_equal. apply IHn. destruct (fin_eqb i1' i2') eqn: He; auto.
        + subst. destruct i2 as [i2' | ]; auto.
            specialize IHn with i2' i2' as [IHn1 IHn2].
            specialize IHn2 with (1 := eq_refl i2').
            simpl. rewrite IHn2. reflexivity.
Qed.

(* Boolean inequality of finite sets corresponds to propositional inequality *)
Lemma fin_eqb_neq : forall n (i1 i2 : fin n),
    fin_eqb i1 i2 = false <-> i1 <> i2.
Proof.
    intros. split; intros.
    - intros Heq. apply fin_eqb_eq in Heq. rewrite Heq in H. discriminate.
    - destruct (fin_eqb i1 i2) eqn: He; auto. rewrite fin_eqb_eq in He.
        contradiction.
Qed.

(*A renaming that maps 0 to 0 and everything else to itself + 1*)
Definition up_ren' {n} := (up_ren (shift (n := n))).

(*A renaming that maps 0 to 0, 1 to 1,
    and everything else to itself + 1 *)
Definition up2_ren' {n} := (up_ren (up_ren' (n := n))).

(*Fixpoint upn_ren {n} (m : nat) : ren (n + m) (1 + n + m) :=
    match m with
    | 0 => up_ren id
    | S m' => up_ren (upn_ren m')
    end. TODO*)

(* injectivity of a renaming *)
Definition ren_inj {n m} (renamer : ren n m) :=
    (forall i1 i2, renamer i1 = renamer i2 -> i1 = i2).

(* fm is a weakening of fn *)
Definition ren_match {n m X} (renamer : ren n m)
    (fn : fin n -> X) (fm : fin m -> X) :=
    forall i, fn i = fm (renamer i).

(* fm maps every element to id except those with a preimage in fin n *)
Definition default_or_preimage {n m X} (id : X) (fm : fin m -> X) (renamer : ren n m) :=
    (forall j, fm j = id \/ exists i, j = renamer i).

(* sum type reflecting that everything in fin j either does or doesn't have a preimage in fin n *)
Inductive ren_preimage_cases {n m} (renamer : ren n m) (j : fin m) : Type :=
    | preimage (i : fin n) (H : j = renamer i) : ren_preimage_cases renamer j
    | no_preimage (H : forall (i : fin n), renamer i <> j) : ren_preimage_cases renamer j
    .

(* decidability of j having a preimage in fin n *)
Definition ren_preimage_dec {n m} :
    forall (renamer : ren n m) (j : fin m), ren_preimage_cases renamer j.
Proof.
    induction n; intros.
    - eapply no_preimage. intros. destruct i.
    - destruct (fin_eqb (renamer None) j) eqn: HNone.
        + apply preimage with (i := None). rewrite fin_eqb_eq in HNone. auto.
        + remember (fun jn => renamer (shift jn)) as renamer_n.
            destruct (IHn renamer_n j).
            * apply preimage with (i := shift i). subst. reflexivity.
            * apply no_preimage. intros. destruct i as [i' |].
                -- specialize H with i'. intros Hj; subst. contradiction.
                -- rewrite fin_eqb_neq in HNone. auto.
Qed.

(* constructs a weakening of fn by sending an element j of fin m to
    either fn applied to j's preimage (if any) or to the default value *)
Definition match_pre_id {n m X} (renamer : ren n m) (fn : fin n -> X)
    (default : X) : fin m -> X := fun j =>
    match ren_preimage_dec renamer j with
    | preimage _ _ i H => fn i
    | no_preimage _ _ H => default
    end.

(* For any injective renaming, match_pre_id constructs a valid weakening of fn *)
Lemma match_pre_id_inj_sound :
    forall n m X (renamer : ren n m) (fn : fin n -> X) (default : X),
    ren_inj renamer ->
    ren_match renamer fn (match_pre_id renamer fn default) /\
    default_or_preimage default (match_pre_id renamer fn default) renamer.
Proof.
    intros. split.
    - unfold ren_match. intros. unfold match_pre_id.
        destruct (ren_preimage_dec renamer (renamer i)) eqn: Hc.
        + f_equal. apply H. assumption.
        + clear Hc. specialize H0 with i. contradiction.
    - unfold default_or_preimage. intros. unfold match_pre_id.
        destruct (ren_preimage_dec renamer j) eqn: Hc.
        + right. exists i. assumption.
        + left. reflexivity.
Qed.

(* If we add a new element to the head of our map, that is a valid
    weakening under shift. *)
Lemma ren_match_shift :
    forall n X (fn : fin n -> X) x_new,
    ren_match shift fn (x_new .: fn).
Proof.
    unfold ren_match. intros. auto.
Qed.

(* If we add a new element immediately after the head of our map, 
    that is a valid weakening under up_ren'. *)
Lemma ren_match_up_ren' :
    forall n X (fn : fin n -> X) x x_new,
    ren_match up_ren' (x .: fn) (x .: (x_new .: fn)).
Proof.
    unfold ren_match. intros.
    destruct i as [i' | ]; auto.
Qed.

(* If we add a new element two indices after the head of our map, 
    that is a valid weakening under up2_ren'. *)
Lemma ren_match_up2_ren' :
    forall n X (fn : fin n -> X) x1 x2 x_new,
    ren_match up2_ren'
        (x1 .: (x2 .: fn))
        (x1 .: (x2 .: (x_new .: fn))).
Proof.
    unfold ren_match. intros.
    destruct i as [[i'' |] | ]; auto.
Qed.


(* instantiate an equality between equivalent functions. *)
Lemma x_equal
     : forall (A B : Type) (f g : A -> B) (x : A), f = g -> f x = g x.
Proof. intros. rewrite H. auto. Qed.

(* map for environments *)
Definition env_map {n}{A B} (f : A -> B) (ρ : fin n -> A) : fin n -> B :=
  fun x => f (ρ (x)).

(* env_map f commutes with scons *)
Lemma env_map_cons {n} {A B} (a : A) (b : fin n -> A) (f : A -> B) : 
  env_map f ( a .: b ) = f a .: env_map f b .
Proof.
  unfold env_map. fext. intro x.
  unfold scons. destruct x. auto. auto.
Qed.

(* scons is injective in the first argument *)
Lemma scons_inj1 {n A} (a c : A) (b d : fin n -> A) : ( a .: b ) = (c .: d) -> a = c.
Proof.
  intros h.
  pose (h1 := x_equal _ _ (a .: b) (c .: d) var_zero h).
  simpl in h1.
  auto.
Qed.

(* scons is injective in the second argument *)
Lemma scons_inj2 {n A} (a c : A) (b d : fin n -> A) : ( a .: b ) = (c .: d) -> b = d.
Proof.
  intros h.
  fext. intro x.
  pose (h1 := x_equal _ _ (a .: b) (c .: d) (shift x) h).
  simpl in h1.
  auto.
Qed.
