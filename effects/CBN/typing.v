Require Export effects.CBN.syntax.

Definition contextL n := fin n -> Ty.

(*Syntactic typing judgements*)
(*Identical to CBV except for pair/with intro/elimination*)
Inductive Wt {n} (Γ : contextL n) : Tm n -> Ty -> Prop :=
    | T_var i :
        (* ------------------ *)
        Wt Γ (var_Tm i) (Γ i)

    | T_abs e T1 T2 :
        Wt (T1 .: Γ) e T2 ->
        (* ------------- *)
        Wt Γ (abs e) (Abs T1 T2)

    | T_app e1 e2 T1 T2 :
        Wt Γ e1 (Abs T1 T2) ->
        Wt Γ e2 T1 ->
        (* --------------- *)
        Wt Γ (app e1 e2) T2

    | T_unit :
        (* ------------- *)
        Wt Γ unit Unit

    | T_seq e1 e2 T :
        Wt Γ e1 Unit ->
        Wt Γ e2 T ->
        (*------------------*)
        Wt Γ (seq e1 e2) T

    | T_inl e T1 T2 :
        Wt Γ e T1 ->
        (* ----------------------- *)
        Wt Γ (inl e) (Sum T1 T2)

    | T_inr e T1 T2 :
        Wt Γ e T2 ->
        (* ----------------------- *)
        Wt Γ (inr e) (Sum T1 T2)

    | T_prod e1 e2 T1 T2 :
        Wt Γ e1 T1 ->
        Wt Γ e2 T2 ->
        (*--------------------*)
        Wt Γ (prod e1 e2) (With T1 T2)

    | T_fst e T1 T2 :
        Wt Γ e (With T1 T2) ->
        (* ------------------ *)
        Wt Γ (fst e) T1

    | T_snd e T1 T2 :
        Wt Γ e (With T1 T2) ->
        (* ---------------------------- *)
        Wt Γ (snd e) T2

    | T_case e e1 e2 T1 T2 T :
        Wt Γ e (Sum T1 T2) ->
        Wt (T1 .: Γ) e1 T ->
        Wt (T2 .: Γ) e2 T ->
        (*-------------------------------*)
        Wt Γ (case e e1 e2) T

    | T_ret e T ϕ :
        Wt Γ e T ->
        ϕ = ϵ ->
        (*-------------------------------*)
        Wt Γ (ret e) (Mon ϕ T)

    | T_bind e1 e2 T1 T2 ϕ1 ϕ2 ϕ :
        Wt Γ e1 (Mon ϕ1 T1) ->
        Wt (T1 .: Γ) e2 (Mon ϕ2 T2) ->
        ϕ = ϕ1 E+ ϕ2 ->
        (*--------------------------------------*)
        Wt Γ (bind e1 e2) (Mon ϕ T2)

    | T_coerce e T ϕ ϕ' :
        Wt Γ e (Mon ϕ T) ->
        ϕ E<= ϕ' ->
        (*---------------------------------*)
        Wt Γ (coerce e) (Mon ϕ' T)

    | T_tickT :
        (*----------------------------*)
        Wt Γ tickT (Mon tick Unit).


Create HintDb types.
Hint Constructors Wt : types.
#[export] Hint Resolve T_var T_abs T_app T_unit
    T_seq T_prod T_fst T_snd T_inl T_inr T_case
    T_ret T_bind T_coerce T_tickT
    : types.
