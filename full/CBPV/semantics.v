Require Export full.CBPV.syntax.

Inductive VClos : Type :=
| VClosUnit
| VClosThunk m (γ : gradeVec m) (ρ : fin m -> VClos) (M : Comp m)
| VClosPair (W1 W2 : VClos)
| VClosInl (W : VClos)
| VClosInr (W : VClos)
| JUNK
.

Definition env n := fin n -> VClos.

Inductive CClos : Type :=
| CClosRet (q : Q) (W : VClos)
| CClosAbs m (q : Q) (γ : gradeVec m) (ρ : env m) (M : Comp (S m))
| CClosPair m (γ : gradeVec m) (ρ : env m) (M1 M2 : Comp m).

Inductive EvalVal {n} (γ : gradeVec n) (ρ : env n) : Val n -> VClos -> Prop :=
  | E_Var i W :
    W = ρ i ->
    γ i = Qone ->
    (forall (j : fin n), j <> i -> γ j = Qzero) ->
    (* ============================================== *)
    EvalVal γ ρ (var_Val i) W

  | E_Unit :
    γ = (0s : gradeVec n) ->
    (* =========================== *)
    EvalVal γ ρ (vUnit) VClosUnit

  | E_Thunk M γ' :
    γ = γ' ->
    (* ========================================== *)
    EvalVal γ ρ (vThunk M) (VClosThunk n γ' ρ M)

  | E_VPair V1 V2 W1 W2 γ1 γ2 :
    EvalVal γ1 ρ V1 W1 ->
    EvalVal γ2 ρ V2 W2 ->
    γ = γ1 Q+ γ2 ->
    (* ========================================= *)
    EvalVal γ ρ (vPair V1 V2) (VClosPair W1 W2)

  | E_Inl V W :
    EvalVal γ ρ V W ->
    (* =============================== *)
    EvalVal γ ρ (vInl V) (VClosInl W)

  | E_Inr V W :
    EvalVal γ ρ V W ->
    (* ================================ *)
    EvalVal γ ρ (vInr V) (VClosInr W)

  | E_VSub V W γ' :
    EvalVal γ' ρ V W ->
    γ Q<= γ' ->
    (* ================== *)
    EvalVal γ ρ V W.

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
  q <> Qzero ->
  ϕ = ϕ1 E+ ϕ2 ->
  (* ======================================== *)
  EvalComp γ ρ (cApp M V) T ϕ

| E_Split q V N W1 W2 T γ1 γ2 ϕ :
  EvalVal γ1 ρ V (VClosPair W1 W2) ->
  EvalComp (q .: (q .: γ2)) (W1 .: (W2 .: ρ)) N T ϕ ->
  γ = (q Q* γ1) Q+ γ2 ->
  q <> Qzero ->
  (* ================================================ *)
  EvalComp γ ρ (cSplit q V N) T ϕ

| E_Ret q V W γ' ϕ :
  EvalVal γ' ρ V W ->
  γ = q Q* γ' ->
  q <> Qzero ->
  ϕ = ϵ ->
  (* ==================================== *)
  EvalComp γ ρ (cRet q V) (CClosRet q W) ϕ

| E_LetRet q1 q2 q' M N W T γ1 γ2 ϕ1 ϕ2 ϕ :
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

| E_AppAbsZero m M M' V T ρ' γ1 ϕ1 ϕ2 ϕ :
  EvalComp γ ρ M (CClosAbs m Qzero γ1 ρ' M') ϕ1 ->
  EvalComp (Qzero .: γ1) (JUNK .: ρ') M' T ϕ2 ->
  ϕ = ϕ1 E+ ϕ2 ->
  (* ======================================== *)
  EvalComp γ ρ (cApp M V) T ϕ

| E_SplitZero V N T ϕ :
  EvalComp (Qzero .: (Qzero .: γ)) (JUNK .: (JUNK .: ρ)) N T ϕ ->
  (* ================================================ *)
  EvalComp γ ρ (cSplit Qzero V N) T ϕ

| E_RetZero V ϕ :
  γ = (0s : gradeVec n) ->
  ϕ = ϵ ->
  (* ==================================== *)
  EvalComp γ ρ (cRet Qzero V) (CClosRet Qzero JUNK) ϕ

| E_Tick ϕ :
  γ = (0s : gradeVec n) ->
  ϕ = tick ->
  EvalComp γ ρ cTick (CClosRet Qone VClosUnit) tick

| E_CSub M T γ' ϕ :
  EvalComp γ' ρ M T ϕ ->
  γ Q<= γ' ->
  (* ================== *)
  EvalComp γ ρ M T ϕ

 | E_LetRetZero M N T γ' ϕ : (*NEW*)
  EvalComp (Qzero .: γ') (JUNK .: ρ) N T ϕ ->
  γ = γ' ->
  (* ========================================== *)
  EvalComp γ ρ (cLet0 M N) T ϕ.

Hint Constructors EvalVal EvalComp : semantics.


#[export]Hint Resolve E_Var E_Unit E_Thunk E_VPair E_Inl E_Inr E_VSub E_Abs
  E_AppAbs E_ForceThunk E_Ret E_LetRet E_Split E_CPair E_Fst E_Snd E_Casel
  E_Caser E_AppAbsZero E_SplitZero E_RetZero E_CSub : semantics.

