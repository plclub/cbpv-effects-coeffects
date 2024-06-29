Require Import general.CBN.syntax.

Inductive VClos : Type :=
| VClosUnit
| VClosAbs m (γ : gradeVec m) (ρ : fin m -> VClos) (e : Tm (S m))
| VClosPair m (γ : gradeVec m) (ρ : fin m -> VClos) (W1 W2 : Tm m)
| VClosInl (W : VClos)
| VClosInr (W : VClos)
.


Definition env n := fin n -> VClos.


Inductive Eval {n} (γ : gradeVec n) (ρ : env n) : Tm n -> VClos -> Prop :=
| E_Var i v :
  v = ρ i ->
  (γ i) = Qone ->
  (forall (j : fin n), j <> i -> (γ j) = Qzero) ->
  (* ============================================== *)
  Eval γ ρ (var_Tm i) v
       
| E_Abs q' q e  :
  Qle q' q ->
  (* ========================================== *)
  Eval γ ρ (abs q e) (VClosAbs n γ ρ e)

| E_AppAbs m q e e' V T v γ' γ1 γ2 ρ':
  Eval γ1 ρ e (VClosAbs m γ' ρ' e') ->
  Eval γ2 ρ V v ->
  Eval (q .: γ') (v .: ρ') e' T ->
  γ = (γ1 Q+ (q Q* γ2)) ->
  (* ======================================== *)
  Eval γ ρ (app e V) T

| E_Unit :
  γ = (0s : gradeVec n) ->
  (* =========================== *)
  Eval γ ρ unit VClosUnit

| E_Seq V N T γ1 γ2 :
  Eval γ1 ρ V VClosUnit ->
  Eval γ2 ρ N T ->
  γ = (γ1 Q+ γ2) ->
  (* ======================= *)
  Eval γ ρ (seq V N) T

| E_VPair V1 V2 v1 v2 :
  (* ========================================= *)
  Eval γ ρ (prod V1 V2) (VClosPair n γ ρ v1 v2)
       
| E_Fst m e e1 e2 T γ' ρ' :
  Eval γ ρ e (VClosPair m γ' ρ' e1 e2) ->
  Eval γ' ρ' e1 T ->
  (* ========================================= *)
  Eval γ ρ (fst e) T

| E_Snd m e e1 e2 T γ' ρ' :
  Eval γ ρ e (VClosPair m γ' ρ' e1 e2) ->
  Eval γ' ρ' e2 T ->
  (* ========================================= *)
  Eval γ ρ (snd e) T

| E_Inl V v :
  Eval γ ρ V v ->
  (* =============================== *)
  Eval γ ρ (inl V) (VClosInl v)

| E_Inr V v :
  Eval γ ρ V v ->
  (* ================================ *)
  Eval γ ρ (inr V) (VClosInr v)

| E_Casel q V e1 e2 v T γ1 γ2 :
  Eval γ1 ρ V (VClosInl v) ->
  Eval (q .: γ2) (v .: ρ) e1 T ->
  γ = ((q Q* γ1) Q+ γ2) ->
  Qle q Qone ->
  (* ================================= *)
  Eval γ ρ (case q V e1 e2) T

| E_Caser q V e1 e2 v T γ1 γ2 :
  Eval γ1 ρ V (VClosInr v) ->
  Eval (q .: γ2) (v .: ρ) e2 T ->
  γ = ((q Q* γ1) Q+ γ2) ->
  Qle q Qone ->
  (* ================================= *)
  Eval γ ρ (case q V e1 e2) T

| E_Sub e T γ' :
  Eval γ' ρ e T ->
  γ Q<= γ' ->
  (* ========================================== *)
  Eval γ ρ e T
.
