Require Export resource.CBV.syntax.

Definition contextL n := fin n -> Ty.

(*Syntactic typing judgements*)
(*Identical to CBN except for pair/with intro/elimination*)
Inductive Wt {n} (γ : gradeVec n) (Γ : contextL n) : Tm n -> Ty -> Prop :=
    | T_var i :
        γ i = Qone ->
        (forall (j : fin n), j <> i -> γ j = Qzero) ->
        (* ------------------------------------------------ *)
        Wt γ Γ (var_Tm i) (Γ i)
    | T_abs q q' e T1 T2 :
        Wt (q .: γ) (T1 .: Γ) e T2 ->
        Qle q' q ->
        (* ------------------------------------ *)
        Wt γ Γ (abs q e) (Abs q' T1 T2)
    | T_app q q' e1 e2 T1 T2 γ1 γ2 :
        q' = q_or_1 q -> (*RESOURCE-SPECIFIC*)
        Wt γ1 Γ e1 (Abs q' T1 T2) ->
        Wt γ2 Γ e2 T1 ->
        γ = γ1 Q+ (q' Q* γ2) ->
        (* ---------------------------- *)
        Wt γ Γ (app q e1 e2) T2
    | T_unit :
        γ = (0s : gradeVec n) ->
        (* ----------------------- *)
        Wt γ Γ unit Unit
    | T_seq e1 e2 T γ1 γ2 :
        Wt γ1 Γ e1 Unit ->
        Wt γ2 Γ e2 T ->
        γ = γ1 Q+ γ2 ->
        (*------------------------*)
        Wt γ Γ (seq e1 e2) T
    | T_pair e1 e2 T1 T2 γ1 γ2 :
        Wt γ1 Γ e1 T1 ->
        Wt γ2 Γ e2 T2 ->
        γ = γ1 Q+ γ2 ->
        (* --------------------------------------- *)
        Wt γ Γ (pair e1 e2) (Pair T1 T2)
    | T_split q q' e1 e2 T1 T2 γ1 γ2 :
        q' = q_or_1 q -> (*RESOURCE-SPECIFIC*)
        Wt γ1 Γ e1 (Pair T1 T2) ->
        Wt (q' .: (q' .: γ2)) (T1 .: (T2 .: Γ)) e2 T2 ->
        γ = (q' Q* γ1) Q+ γ2 ->
        (* ----------------------------- *)
        Wt γ Γ (split q e1 e2) T2
    | T_inl e T1 T2 :
        Wt γ Γ e T1 ->
        (* -------------------------------- *)
        Wt γ Γ (inl e) (Sum T1 T2)
    | T_inr e T1 T2 :
        Wt γ Γ e T2 ->
        (* --------------------------------- *)
        Wt γ Γ (inr e) (Sum T1 T2)
    | T_case q e e1 e2 T1 T2 T γ1 γ2 :
        Wt γ1 Γ e (Sum T1 T2) ->
        Wt (q .: γ2) (T1 .: Γ) e1 T ->
        Wt (q .: γ2) (T2 .: Γ) e2 T ->
        γ = (q Q* γ1) Q+ γ2 ->
        Qle q Qone ->
        (*-------------------------------*)
        Wt γ Γ (case q e e1 e2) T
    | T_box q q' e T γ1 :
        q' = q_or_1 q -> (*RESOURCE-SPECIFIC*)
        Wt γ1 Γ e T ->
        γ = (q' Q* γ1) ->
        (*---------------------------------*)
        Wt γ Γ (box q e) (Box q' T)
    | T_unbox q1 q2 q' e1 e2 T1 T2 γ1 γ2 :
        q' = q_or_1 q2 -> (*RESOURCE-SPECIFIC*)
        Wt γ1 Γ e1 (Box q1 T1) ->
        Wt ((Qmult q1 q') .: γ2) (T1 .: Γ) e2 T2 ->
        γ = (q' Q* γ1) Q+ γ2 ->
        (*-------------------------------*)
        Wt γ Γ (unbox q2 e1 e2) T2
    | T_sub e T γ' :
        Wt γ' Γ e T ->
        γ Q<= γ' ->
        (*---------------------*)
        Wt γ Γ e T.

Create HintDb types.
Hint Constructors Wt : types.
#[export] Hint Resolve T_var T_abs T_app T_unit
    T_seq T_pair T_split T_inl T_inr T_case
    T_box T_unbox : types.
