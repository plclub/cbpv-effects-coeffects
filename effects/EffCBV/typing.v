Require Export effects.EffCBV.syntax.

Definition contextL n := fin n -> Ty.

(*Syntactic typing judgements*)
Inductive Wt {n} (Γ : contextL n) : Tm n -> Ty -> E -> Prop :=
    | T_var i :
        (* ------------------------------------------------ *)
        Wt Γ (var_Tm i) (Γ i) ϵ

    | T_abs e T1 T2 ϕ :
        Wt (T1 .: Γ) e T2 ϕ ->
        (* ------------------------------------ *)
        Wt Γ (abs e) (Abs T1 ϕ T2) ϵ

    | T_app e1 e2 T1 T2 ϕ ϕ1 ϕ2 ϕ3 :
        Wt Γ e1 (Abs T1 ϕ3 T2) ϕ1 ->
        Wt Γ e2 T1 ϕ2 ->
        ϕ = ϕ1 E+ ϕ2 E+ ϕ3 ->
        (* ---------------------------- *)
        Wt Γ (app e1 e2) T2 ϕ

    | T_unit :
        (* ----------------------- *)
        Wt Γ unit Unit ϵ

    | T_seq e1 e2 T ϕ ϕ1 ϕ2 :
        Wt Γ e1 Unit ϕ1 ->
        Wt Γ e2 T ϕ2 ->
        ϕ = ϕ1 E+ ϕ2 ->
        (*------------------------*)
        Wt Γ (seq e1 e2) T ϕ

    | T_pair e1 e2 T1 T2 ϕ ϕ1 ϕ2:
        Wt Γ e1 T1 ϕ1 ->
        Wt Γ e2 T2 ϕ2 ->
        ϕ = ϕ1 E+ ϕ2 ->
        (* --------------------------------------- *)
        Wt Γ (pair e1 e2) (Pair T1 T2) ϕ

    | T_split e1 e2 T1 T2 ϕ ϕ1 ϕ2 :
        Wt Γ e1 (Pair T1 T2) ϕ1 ->
        Wt (T1 .: (T2 .: Γ)) e2 T2 ϕ2 ->
        ϕ = ϕ1 E+ ϕ2 ->
        (* ----------------------------- *)
        Wt Γ (split e1 e2) T2 ϕ

    | T_inl e T1 T2 ϕ :
        Wt Γ e T1 ϕ ->
        (* -------------------------------- *)
        Wt Γ (inl e) (Sum T1 T2) ϕ

    | T_inr e T1 T2 ϕ :
        Wt Γ e T2 ϕ ->
        (* --------------------------------- *)
        Wt Γ (inr e) (Sum T1 T2) ϕ

    | T_case e e1 e2 T1 T2 T ϕ ϕ1 ϕ2:
        Wt Γ e (Sum T1 T2) ϕ1 ->
        Wt (T1 .: Γ) e1 T ϕ2 ->
        Wt (T2 .: Γ) e2 T ϕ2 ->
        ϕ = ϕ1 E+ ϕ2 ->
        (*-------------------------------*)
        Wt Γ (case e e1 e2) T ϕ

    | T_sub e T ϕ ϕ' :
      Wt Γ e T ϕ ->
      ϕ E<= ϕ' ->
      (*--------------------*)
      Wt Γ e T ϕ'

    | T_tickT :
        (*----------------------------*)
        Wt Γ tickT Unit tick.

Create HintDb types.
Hint Constructors Wt : types.
#[export] Hint Resolve T_var T_abs T_app T_unit
    T_seq T_pair T_split T_inl T_inr T_case
    T_sub T_tickT : types.
