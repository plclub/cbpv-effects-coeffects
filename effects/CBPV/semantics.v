Require Export effects.CBPV.syntax.

Inductive VClos : Type :=
| VClosUnit
| VClosThunk m (ρ : fin m -> VClos) (M : Comp m)
| VClosPair (W1 W2 : VClos)
| VClosInl (W : VClos)
| VClosInr (W : VClos)
.

Definition env n := fin n -> VClos.

Inductive CClos : Type :=
| CClosRet (W : VClos)
| CClosAbs m (ρ : env m) (M : Comp (S m))
| CClosPair m (ρ : env m) (M1 M2 : Comp m).

Inductive EvalVal {n} (ρ : env n) : Val n -> VClos -> Prop :=
  | E_Var i W :
    W = ρ i ->
    (* ============================================== *)
    EvalVal ρ (var_Val i) W

  | E_Unit :
    (* =========================== *)
    EvalVal ρ (vUnit) VClosUnit

  | E_Thunk M :
    (* ========================================== *)
    EvalVal ρ (vThunk M) (VClosThunk n ρ M)

  | E_VPair V1 V2 W1 W2 :
    EvalVal ρ V1 W1 ->
    EvalVal ρ V2 W2 ->
    (* ========================================= *)
    EvalVal ρ (vPair V1 V2) (VClosPair W1 W2)

  | E_Inl V W :
    EvalVal ρ V W ->
    (* =============================== *)
    EvalVal ρ (vInl V) (VClosInl W)

  | E_Inr V W :
    EvalVal ρ V W ->
    (* ================================ *)
    EvalVal ρ (vInr V) (VClosInr W).

Inductive EvalComp {n} (ρ : env n) : Comp n -> CClos -> E -> Prop :=
| E_Abs M ϕ :
  ϕ = ϵ ->
  (* ========================================== *)
  EvalComp ρ (cAbs M) (CClosAbs n ρ M) ϕ

| E_CPair M1 M2 ϕ :
  ϕ = ϵ ->
  (* ================================================= *)
  EvalComp ρ (cPair M1 M2) (CClosPair n ρ M1 M2) ϕ

| E_AppAbs m M M' V T W ρ' ϕ1 ϕ2 ϕ :
  EvalComp ρ M (CClosAbs m ρ' M') ϕ1 ->
  EvalVal ρ V W ->
  EvalComp (W .: ρ') M' T ϕ2 ->
  ϕ = ϕ1 E+ ϕ2 ->
  (* ======================================== *)
  EvalComp ρ (cApp M V) T ϕ

| E_Split V N W1 W2 T ϕ :
  EvalVal ρ V (VClosPair W1 W2) ->
  EvalComp (W1 .: (W2 .: ρ)) N T ϕ ->
  (* ================================================ *)
  EvalComp ρ (cSplit V N) T ϕ

| E_Ret V W ϕ :
  EvalVal ρ V W ->
  ϕ = ϵ ->
  (* ==================================== *)
  EvalComp ρ (cRet V) (CClosRet W) ϕ

| E_LetRet M N W T ϕ1 ϕ2 ϕ :
  EvalComp ρ M (CClosRet  W) ϕ1 ->
  EvalComp (W .: ρ) N T ϕ2 ->
  ϕ = ϕ1 E+ ϕ2 ->
  (* ========================================== *)
  EvalComp ρ (cLet M N) T ϕ

| E_ForceThunk m V M T  ρ' ϕ :
  EvalVal ρ V (VClosThunk m ρ' M) ->
  EvalComp ρ' M T ϕ ->
  (* ===================================== *)
  EvalComp ρ (cForce V) T ϕ

| E_Fst m M M1 M2 T ρ' ϕ1 ϕ2 ϕ :
  EvalComp ρ M (CClosPair m ρ' M1 M2) ϕ1 ->
  EvalComp ρ' M1 T ϕ2 ->
  ϕ = ϕ1 E+ ϕ2 ->
  (* ========================================= *)
  EvalComp ρ (cFst M) T ϕ

| E_Snd m M M1 M2 T ρ' ϕ1 ϕ2 ϕ :
  EvalComp ρ M (CClosPair m ρ' M1 M2) ϕ1 ->
  EvalComp ρ' M2 T ϕ2 ->
  ϕ = ϕ1 E+ ϕ2 ->
  (* ========================================= *)
  EvalComp ρ (cSnd M) T ϕ

| E_Seq V N T ϕ :
  EvalVal ρ V VClosUnit ->
  EvalComp ρ N T ϕ ->
  (* ======================= *)
  EvalComp ρ (cSeq V N) T ϕ

| E_Casel V M1 M2 W T ϕ :
  EvalVal ρ V (VClosInl W) ->
  EvalComp (W .: ρ) M1 T ϕ ->
  (* ================================= *)
  EvalComp ρ (cCase V M1 M2) T ϕ

| E_Caser V M1 M2 W T ϕ :
  EvalVal ρ V (VClosInr W) ->
  EvalComp (W .: ρ) M2 T ϕ ->
  (* ================================= *)
  EvalComp ρ (cCase V M1 M2) T ϕ

| E_Tick ϕ :
  ϕ = tick ->
  EvalComp ρ cTick (CClosRet VClosUnit) tick

| E_CSub M T ϕ :
  EvalComp ρ M T ϕ ->
  (* ================== *)
  EvalComp ρ M T ϕ
.

Hint Constructors EvalVal EvalComp : semantics.


#[export]Hint Resolve E_Var E_Unit E_Thunk E_VPair E_Inl E_Inr E_Abs
  E_AppAbs E_ForceThunk E_Ret E_LetRet E_Split E_CPair E_Fst E_Snd E_Casel
  E_Caser E_CSub : semantics.
