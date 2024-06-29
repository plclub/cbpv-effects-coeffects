Require Export full.CBV.syntax.
Require Import common.effects.

Module CBV.

Inductive VClos : Type := 
| VClosUnit
| VClosAbs m (γ : gradeVec m) (q : Q) (ρ : fin m -> VClos) (e : Tm (S m))
| VClosPair (W1 W2 : VClos)
| VClosInl (W : VClos)
| VClosInr (W : VClos)
| VClosBox (q: Q) (W : VClos)
| VClosRet (W : VClos)
.

Definition env (n : nat) := fin n -> VClos.


Inductive Eval {n} (γ : gradeVec n) (ρ : env n) : Tm n -> VClos -> E -> Prop :=
  | E_Var i W :
    W = ρ i ->
    γ i = Qone ->
    (forall (j : fin n), j <> i -> γ j = Qzero) ->
    (* ============================================== *)
    Eval γ ρ (var_Tm  i) W ϵ

  | E_Unit :
    γ = (0s : gradeVec n) ->
    (* =========================== *)
    Eval γ ρ (unit) VClosUnit ϵ

  | E_Seq V N T γ1 γ2 ϕ1 ϕ2 :
    Eval γ1 ρ V VClosUnit ϕ1 ->
    Eval γ2 ρ N T ϕ2 ->
    γ = γ1 Q+ γ2 ->
    (* ======================= *)
    Eval γ ρ (seq V N) T (ϕ1 E+ ϕ2)


  | E_Abs q M γ' :
    γ = γ' ->
    (* ========================================== *)
    Eval γ ρ (abs q M) (VClosAbs n γ' q ρ M) ϵ


  | E_AppAbs m q M M' V T W γ' γ1 γ2 ρ' ϕ1 ϕ2 ϕ3 ϕ :
    Eval γ1 ρ M (VClosAbs m γ' q ρ' M') ϕ1 ->
    Eval γ2 ρ V W  ϕ2 ->
    Eval (q .: γ') (W .: ρ') M' T ϕ2 ->
    γ = γ1 Q+ (q Q* γ2) ->
    q <> Qzero ->
    ϕ = ϕ1 E+ ϕ2 E+ ϕ3 ->
  (* ======================================== *)
    Eval γ ρ (app q M V) T ϕ


  | E_VPair V1 V2 W1 W2 γ1 γ2 ϕ1 ϕ2 :
    Eval γ1 ρ V1 W1 ϕ1 ->
    Eval γ2 ρ V2 W2 ϕ2 ->
    γ = γ1 Q+ γ2 ->
    (* ========================================= *)
    Eval γ ρ (pair V1 V2) (VClosPair W1 W2) (ϕ1 E+ ϕ2)


  | E_Split q V N W1 W2 T γ1 γ2 ϕ1 ϕ2 :
    Eval γ1 ρ V (VClosPair W1 W2) ϕ1 ->
    Eval (q .: (q .: γ2)) (W1 .: (W2 .: ρ)) N T ϕ2 ->
    γ = (q Q* γ1) Q+ γ2 ->
    q <> Qzero ->
    (* ================================================ *)
    Eval γ ρ (split q V N) T (ϕ1 E+ ϕ2)


  | E_Inl V W ϕ :
    Eval γ ρ V W ϕ ->
    (* =============================== *)
    Eval γ ρ (inl V) (VClosInl W) ϕ

  | E_Inr V W ϕ :
    Eval γ ρ V W ϕ ->
    (* ================================ *)
    Eval γ ρ (inr V) (VClosInr W) ϕ

  | E_Casel q V M1 M2 W T γ1 γ2 ϕ1 ϕ2 :
    Eval γ1 ρ V (VClosInl W) ϕ1 ->
    Eval (q .: γ2) (W .: ρ) M1 T ϕ2 ->
    γ = (q Q* γ1) Q+ γ2 ->
    Qle q Qone ->
    (* ================================= *)
    Eval γ ρ (case q V M1 M2) T (ϕ1 E+ ϕ2)

  | E_Caser q V M1 M2 W T γ1 γ2 ϕ1 ϕ2 :
    Eval γ1 ρ V (VClosInr W) ϕ1 ->
    Eval (q .: γ2) (W .: ρ) M2 T ϕ1 ->
    γ = (q Q* γ1) Q+ γ2 ->
    Qle q Qone ->
    (* ================================= *)
    Eval γ ρ (case q V M1 M2) T (ϕ1 E+ ϕ2)

  | E_Tick ϕ :
    γ = (0s : gradeVec n) ->
    ϕ = tick ->
    Eval γ ρ tickT (VClosRet VClosUnit) tick


  | E_Ret V W ϕ :
    Eval γ ρ V W ϕ ->
    (* ==================================== *)
    Eval γ ρ (ret V) (VClosRet W) ϕ

  | E_BindRet q2 q' M N W T γ1 γ2 ϕ1 ϕ2 ϕ :
    q' = q_or_1 q2 ->
    Eval γ1 ρ M (VClosRet W) ϕ1 ->
    Eval (q' .: γ2) (W .: ρ) N T ϕ2 ->
    γ = (q' Q* γ1) Q+ γ2 ->
    ϕ = ϕ1 E+ ϕ2 ->
    (* ========================================== *)
    Eval γ ρ (bind q2 M N) T ϕ

  | E_Box q V W γ' ϕ :
    Eval γ' ρ V W ϕ ->
    γ = q Q* γ' ->
    q <> Qzero ->
    (* ==================================== *)
    Eval γ ρ (box q V) (VClosBox q W) ϕ

  | E_Unbox q1 q2 q' M N W T γ1 γ2 ϕ1 ϕ2 ϕ :
    q' = q_or_1 q2 ->
    Eval γ1 ρ M (VClosBox q1 W) ϕ1 ->
    Eval (Qmult q1 q' .: γ2) (W .: ρ) N T ϕ2 ->
    γ = (q' Q* γ1) Q+ γ2 ->
    ϕ = ϕ1 E+ ϕ2 ->
    (* ========================================== *)
    Eval γ ρ (unbox q2 M N) T ϕ
           
  | E_CSub M T γ' ϕ :
    Eval γ' ρ M T ϕ ->
    γ Q<= γ' ->
    (* ================== *)
    Eval γ ρ M T ϕ
.

End CBV.
