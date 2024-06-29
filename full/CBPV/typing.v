Require Export full.CBPV.syntax common.resource_axioms.

Definition context n := fin n -> ValTy.

(*Syntactic typing judgements*)
Inductive VWt {n} (γ : gradeVec n) (Γ : context n) : Val n -> ValTy -> Prop :=
| T_Var i :
  γ i = Qone ->
  (forall (j : fin n), j <> i -> γ j = Qzero) ->
  (* ---------------------------------------------- *)
  VWt γ Γ (var_Val i) (Γ i)

| T_Thunk M B ϕ :
  CWt γ Γ M B ϕ ->
  (* --------------------------- *)
  VWt γ Γ (vThunk M) (VThunk ϕ B)

| T_Unit :
  γ = (0s : gradeVec n) ->
  (* --------------------- *)
  VWt γ Γ vUnit VUnit

| T_VPair V1 V2 A1 A2 γ1 γ2 :
  VWt γ1 Γ V1 A1 ->
  VWt γ2 Γ V2 A2 ->
  γ = γ1 Q+ γ2 ->
  (* --------------------------------- *)
  VWt γ Γ (vPair V1 V2) (VPair A1 A2)

| T_Inl V A1 A2 :
  VWt γ Γ V A1 ->
  (* --------------------------- *)
  VWt γ Γ (vInl V) (VSum A1 A2)

| T_Inr V A1 A2 :
  VWt γ Γ V A2 ->
  (* --------------------------- *)
  VWt γ Γ (vInr V) (VSum A1 A2)

| T_VSub V A γ' :
  VWt γ' Γ V A ->
  γ Q<= γ' ->
  (* --------------------- *)
  VWt γ Γ V A

with CWt {n} (γ : gradeVec n) (Γ : context n) : Comp n -> CompTy -> E -> Prop :=
 | T_Abs q q' M A B ϕ :
  CWt (q .: γ) (A .: Γ) M B ϕ ->
  Qle q' q ->
  (* ----------------------------- *)
  CWt γ Γ (cAbs q M) (CAbs q' A B) ϕ

| T_App q M V A B γ1 γ2 ϕ :
  CWt γ1 Γ M (CAbs q A B) ϕ ->
  VWt γ2 Γ V A ->
  γ = γ1 Q+ (q Q* γ2) ->
  (* ------------------------ *)
  CWt γ Γ (cApp M V) B ϕ

| T_Force V B ϕ :
  VWt γ Γ V (VThunk ϕ B) ->
  (* --------------------- *)
  CWt γ Γ (cForce V) B ϕ

| T_Split q V N A1 A2 B γ1 γ2 ϕ :
  VWt γ1 Γ V (VPair A1 A2) ->
  CWt (q .: (q .: γ2)) (A1 .: (A2 .: Γ)) N B ϕ ->
  γ = (q Q* γ1) Q+ γ2 ->
  (* ------------------------------------------- *)
  CWt γ Γ (cSplit q V N) B ϕ

| T_Ret q V A γ1 ϕ :
  VWt γ1 Γ V A ->
  γ = q Q* γ1 ->
  ϕ = ϵ ->
  (* ------------------------ *)
  CWt γ Γ (cRet q V) (CF q A) ϕ

| T_Let q1 q2 q' M N A B γ1 γ2 ϕ1 ϕ2 ϕ :
  q' = q_or_1 q2 ->
  CWt γ1 Γ M (CF q1 A) ϕ1 ->
  CWt ((Qmult q1 q') .: γ2) (A .: Γ) N B ϕ2 ->
  γ = (q' Q* γ1) Q+ γ2 ->
  ϕ = ϕ1 E+ ϕ2 ->
  (* --------------------------------------- *)
  CWt γ Γ (cLet q2 M N) B ϕ

| T_CPair M1 M2 B1 B2 ϕ :
  CWt γ Γ M1 B1 ϕ ->
  CWt γ Γ M2 B2 ϕ ->
  (* --------------------------------- *)
  CWt γ Γ (cPair M1 M2) (CPair B1 B2) ϕ

| T_Fst M B1 B2 ϕ :
  CWt γ Γ M (CPair B1 B2) ϕ ->
  (* ------------------------ *)
  CWt γ Γ (cFst M) B1 ϕ

| T_Snd M B1 B2 ϕ :
  CWt γ Γ M (CPair B1 B2) ϕ ->
  (* ------------------------ *)
  CWt γ Γ (cSnd M) B2 ϕ

| T_Seq V N B γ1 γ2 ϕ :
  VWt γ1 Γ V VUnit ->
  CWt γ2 Γ N B ϕ ->
  γ = γ1 Q+ γ2 ->
  (*------------------*)
  CWt γ Γ (cSeq V N) B ϕ

| T_Case q V M1 M2 A1 A2 B γ1 γ2 ϕ :
  VWt γ1 Γ V (VSum A1 A2) ->
  CWt (q .: γ2) (A1 .: Γ) M1 B ϕ ->
  CWt (q .: γ2) (A2 .: Γ) M2 B ϕ ->
  γ = (q Q* γ1) Q+ γ2 ->
  Qle q Qone ->
  (*------------------------------*)
  CWt γ Γ (cCase q V M1 M2) B ϕ

| T_Tick ϕ :
  γ = (0s : gradeVec n) ->
  ϕ = tick ->
  (* ----------------------- *)
  CWt γ Γ cTick (CF Qone VUnit) ϕ

| T_CSub M B γ' ϕ :
  CWt γ' Γ M B ϕ ->
  γ Q<= γ' ->
  (* --------------------- *)
  CWt γ Γ M B ϕ

| T_SubEff M B ϕ ϕ' :
  CWt γ Γ M B ϕ ->
  ϕ E<= ϕ' ->
  (* -------------------- *)
  CWt γ Γ M B ϕ'

| T_LetZero q1 M N A B γ1 γ2 ϕ2 ϕ :  (* NEW *)
  CWt γ1 Γ M (CF q1 A) ϵ ->
  CWt (Qzero .: γ2) (A .: Γ) N B ϕ2 ->
  γ = γ2 ->
  ϕ = ϕ2 ->
  (* --------------------------------------- *)
  CWt γ Γ (cLet0 M N) B ϕ

.

Hint Constructors VWt CWt : typing.
#[export] Hint Resolve T_Var T_Thunk T_Unit T_VPair T_Inl T_Inr T_VSub
  T_Abs T_App T_Force T_Split T_Ret T_Let T_CPair T_Fst T_Snd
  T_Seq T_Case T_CSub T_SubEff T_LetZero : typing.

Scheme VWt_ind' := Induction for VWt Sort Prop
    with CWt_ind' := Induction for CWt Sort Prop.

Combined Scheme Wt_mutual from VWt_ind', CWt_ind'.
