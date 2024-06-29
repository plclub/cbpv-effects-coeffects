Require Export general.syntax.

Inductive VClos : Type :=
| VClosUnit
| VClosThunk m (γ : gradeVec m) (ρ : fin m -> VClos) (M : Comp m)
| VClosPair (W1 W2 : VClos)
| VClosInl (W : VClos)
| VClosInr (W : VClos)
.

Definition env n := fin n -> VClos.

Inductive CClos : Type :=
| CClosRet (q : Q) (W : VClos)
| CClosAbs m (q : Q) (γ : gradeVec m) (ρ : env m) (M : Comp (S m))
| CClosPair m (γ : gradeVec m) (ρ : env m) (M1 M2 : Comp m).

Inductive EvalVal {n} (γ : gradeVec n) (ρ : env n) : Val n -> VClos -> Prop :=
  | E_Var i W :
    W = ρ i ->
    (γ i) = Qone ->
    (forall (j : fin n), j <> i -> (γ j) = Qzero) ->
    (* ============================================== *)
    EvalVal γ ρ (var_Val i) W

  | E_Unit :
    γ = (0s : gradeVec n) ->
    (* =========================== *)
    EvalVal γ ρ vUnit VClosUnit

  | E_Thunk M :
    (* ========================================== *)
    EvalVal γ ρ (vThunk M) (VClosThunk n γ ρ M)

  | E_VPair V1 V2 W1 W2 γ1 γ2 :
    EvalVal γ1 ρ V1 W1 ->
    EvalVal γ2 ρ V2 W2 ->
    γ = (γ1 Q+ γ2) ->
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

  | E_SubV V W γ' :
    EvalVal γ' ρ V W ->
    γ Q<= γ' ->
    (* ========================================== *)
    EvalVal γ ρ V W

.

Inductive EvalComp {n} (γ : gradeVec n) (ρ : env n) : Comp n -> CClos -> Prop :=
| E_Abs q' q M  :
  Qle q' q ->
  (* ========================================== *)
  EvalComp γ ρ (cAbs q M) (CClosAbs n q' γ ρ M)

| E_CPair M1 M2  :
  (* ================================================= *)
  EvalComp γ ρ (cPair M1 M2) (CClosPair n γ ρ M1 M2)

| E_AppAbs m q M M' V T W γ' γ1 γ2 ρ':
  EvalComp γ1 ρ M (CClosAbs m q γ' ρ' M') ->
  EvalVal γ2 ρ V W ->
  EvalComp (q .: γ') (W .: ρ') M' T ->
  γ = (γ1 Q+ (q Q* γ2)) ->
  (* ======================================== *)
  EvalComp γ ρ (cApp M V) T

| E_Split q V N W1 W2 T γ1 γ2 :
  EvalVal γ1 ρ V (VClosPair W1 W2) ->
  EvalComp (q .: (q .: γ2)) (W1 .: (W2 .: ρ)) N T ->
  γ = ((q Q* γ1) Q+ γ2) ->
  (* ================================================ *)
  EvalComp γ ρ (cSplit q V N) T

| E_Ret q V W γ' :
  EvalVal γ' ρ V W ->
  γ =( q Q* γ') ->
  (* ==================================== *)
  EvalComp γ ρ (cRet q V) (CClosRet q W)

| E_LetRet q1 q2 M N W T γ1 γ2 :
  EvalComp γ1 ρ M (CClosRet q1 W) ->
  EvalComp (Qmult q1 q2 .: γ2) (W .: ρ) N T ->
  γ = ((q2 Q* γ1) Q+ γ2) ->
  (* ========================================== *)
  EvalComp γ ρ (cLet q2 M N) T

| E_ForceThunk m V M T  γ' ρ' :
  EvalVal γ ρ V (VClosThunk m γ' ρ' M) ->
  EvalComp γ' ρ' M T ->
  (* ===================================== *)
  EvalComp γ ρ (cForce V) T

| E_Fst m M M1 M2 T γ' ρ' :
  EvalComp γ ρ M (CClosPair m γ' ρ' M1 M2) ->
  EvalComp γ' ρ' M1 T ->
  (* ========================================= *)
  EvalComp γ ρ (cFst M) T

| E_Snd m M M1 M2 T γ' ρ' :
  EvalComp γ ρ M (CClosPair m γ' ρ' M1 M2) ->
  EvalComp γ' ρ' M2 T ->
  (* ========================================= *)
  EvalComp γ ρ (cSnd M) T

| E_Seq V N T γ1 γ2 :
  EvalVal γ1 ρ V VClosUnit ->
  EvalComp γ2 ρ N T ->
  γ = (γ1 Q+ γ2) ->
  (* ======================= *)
  EvalComp γ ρ (cSeq V N) T

| E_Casel q V M1 M2 W T γ1 γ2 :
  EvalVal γ1 ρ V (VClosInl W) ->
  EvalComp (q .: γ2) (W .: ρ) M1 T ->
  γ = ((q Q* γ1) Q+ γ2) ->
  Qle q Qone ->
  (* ================================= *)
  EvalComp γ ρ (cCase q V M1 M2) T

| E_Caser q V M1 M2 W T γ1 γ2 :
  EvalVal γ1 ρ V (VClosInr W) ->
  EvalComp (q .: γ2) (W .: ρ) M2 T ->
  γ = ((q Q* γ1) Q+ γ2) ->
  Qle q Qone ->
  (* ================================= *)
  EvalComp γ ρ (cCase q V M1 M2) T

| E_SubM M T γ' :
  EvalComp γ' ρ M T ->
  γ Q<= γ' ->
  (* ========================================== *)
  EvalComp γ ρ M T
.

Hint Constructors EvalVal EvalComp : semantics.

#[export]Hint Resolve E_Var E_Unit E_Thunk E_VPair E_Inl E_Inr E_Abs
  E_AppAbs E_ForceThunk E_Ret E_LetRet E_Split E_CPair E_Fst E_Snd E_Casel
  E_Caser E_SubV E_SubM : semantics.
