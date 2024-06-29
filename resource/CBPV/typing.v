Require Export resource.CBPV.syntax common.resource_axioms.

Definition context n := fin n -> ValTy.

(*Syntactic typing judgements*)
Inductive VWt {n} (γ : gradeVec n) (Γ : context n) : Val n -> ValTy -> Prop :=
| T_Var i :
  γ i = Qone ->
  (forall (j : fin n), j <> i -> γ j = Qzero) ->
  (* ---------------------------------------------- *)
  VWt γ Γ (var_Val i) (Γ i)

| T_Thunk M B :
  CWt γ Γ M B ->
  (* --------------------------- *)
  VWt γ Γ (vThunk M) (VThunk B)

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

with CWt {n} (γ : gradeVec n) (Γ : context n) : Comp n -> CompTy -> Prop :=
 | T_Abs q q' M A B :
  CWt (q .: γ) (A .: Γ) M B ->
  Qle q' q ->
  (* ----------------------------- *)
  CWt γ Γ (cAbs q M) (CAbs q' A B)

| T_App q M V A B γ1 γ2 :
  CWt γ1 Γ M (CAbs q A B) ->
  VWt γ2 Γ V A ->
  γ = γ1 Q+ (q Q* γ2) ->
  (* ------------------------ *)
  CWt γ Γ (cApp M V) B

| T_Force V B :
  VWt γ Γ V (VThunk B) ->
  (* --------------------- *)
  CWt γ Γ (cForce V) B

| T_Split q V N A1 A2 B γ1 γ2 :
  VWt γ1 Γ V (VPair A1 A2) ->
  CWt (q .: (q .: γ2)) (A1 .: (A2 .: Γ)) N B ->
  γ = (q Q* γ1) Q+ γ2 ->
  (* ------------------------------------------- *)
  CWt γ Γ (cSplit q V N) B

| T_Ret q V A γ1 :
  VWt γ1 Γ V A ->
  γ = q Q* γ1 ->
  (* ------------------------ *)
  CWt γ Γ (cRet q V) (CF q A)

| T_Let q1 q2 q' M N A B γ1 γ2 :
  q' = q_or_1 q2 -> (*NEW*)
  CWt γ1 Γ M (CF q1 A) ->
  CWt ((Qmult q1 q') .: γ2) (A .: Γ) N B ->
  γ = (q' Q* γ1) Q+ γ2 ->
  (* --------------------------------------- *)
  CWt γ Γ (cLet q2 M N) B

| T_CPair M1 M2 B1 B2 :
  CWt γ Γ M1 B1 ->
  CWt γ Γ M2 B2 ->
  (* --------------------------------- *)
  CWt γ Γ (cPair M1 M2) (CPair B1 B2)

| T_Fst M B1 B2 :
  CWt γ Γ M (CPair B1 B2) ->
  (* ------------------------ *)
  CWt γ Γ (cFst M) B1

| T_Snd M B1 B2 :
  CWt γ Γ M (CPair B1 B2) ->
  (* ------------------------ *)
  CWt γ Γ (cSnd M) B2

| T_Seq V N B γ1 γ2 :
  VWt γ1 Γ V VUnit ->
  CWt γ2 Γ N B ->
  γ = γ1 Q+ γ2 ->
  (*------------------*)
  CWt γ Γ (cSeq V N) B

| T_Case q V M1 M2 A1 A2 B γ1 γ2 :
  VWt γ1 Γ V (VSum A1 A2) ->
  CWt (q .: γ2) (A1 .: Γ) M1 B ->
  CWt (q .: γ2) (A2 .: Γ) M2 B ->
  γ = (q Q* γ1) Q+ γ2 ->
  Qle q Qone ->
  (*------------------------------*)
  CWt γ Γ (cCase q V M1 M2) B

| T_CSub M B γ' :
  CWt γ' Γ M B ->
  γ Q<= γ' ->
  (* --------------------- *)
  CWt γ Γ M B

.

Hint Constructors VWt CWt : typing.
#[export] Hint Resolve T_Var T_Thunk T_Unit T_VPair T_Inl T_Inr T_VSub
  T_Abs T_App T_Force T_Split T_Ret T_Let T_CPair T_Fst T_Snd
  T_Seq T_Case T_CSub : typing.

Scheme VWt_ind' := Induction for VWt Sort Prop
    with CWt_ind' := Induction for CWt Sort Prop.

Combined Scheme Wt_mutual from VWt_ind', CWt_ind'.
