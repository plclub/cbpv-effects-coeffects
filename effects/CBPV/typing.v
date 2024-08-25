Require Export effects.CBPV.syntax.

Definition context n := fin n -> ValTy.

(*Syntactic typing judgements*)
Inductive VWt {n} (Γ : context n) : Val n -> ValTy -> Prop :=
| T_Var i :
  (* ---------------------------------------------- *)
  VWt Γ (var_Val i) (Γ i)

| T_Thunk M B ϕ :
  CWt Γ M B ϕ ->
  (* --------------------------- *)
  VWt Γ (vThunk M) (VThunk ϕ B)

| T_Unit :
  (* --------------------- *)
  VWt Γ vUnit VUnit

| T_VPair V1 V2 A1 A2 :
  VWt Γ V1 A1 ->
  VWt Γ V2 A2 ->
  (* --------------------------------- *)
  VWt Γ (vPair V1 V2) (VPair A1 A2)

| T_Inl V A1 A2 :
  VWt Γ V A1 ->
  (* --------------------------- *)
  VWt Γ (vInl V) (VSum A1 A2)

| T_Inr V A1 A2 :
  VWt Γ V A2 ->
  (* --------------------------- *)
  VWt Γ (vInr V) (VSum A1 A2)

with CWt {n} (Γ : context n) : Comp n -> CompTy -> E -> Prop :=
 | T_Abs M A B ϕ :
  CWt (A .: Γ) M B ϕ ->
  (* ----------------------------- *)
  CWt Γ (cAbs M) (CAbs A B) ϕ

| T_App M V A B ϕ :
  CWt Γ M (CAbs A B) ϕ ->
  VWt Γ V A ->
  (* ------------------------ *)
  CWt Γ (cApp M V) B ϕ

| T_Force V B ϕ :
  VWt Γ V (VThunk ϕ B) ->
  (* --------------------- *)
  CWt Γ (cForce V) B ϕ

| T_Split V N A1 A2 B ϕ :
  VWt Γ V (VPair A1 A2) ->
  CWt (A1 .: (A2 .: Γ)) N B ϕ ->
  (* ------------------------------------------- *)
  CWt Γ (cSplit V N) B ϕ

| T_Ret V A :
  VWt Γ V A ->
  (* ------------------------ *)
  CWt Γ (cRet V) (CF A) ϵ

| T_Let M N A B ϕ1 ϕ2 :
  CWt Γ M (CF A) ϕ1 ->
  CWt (A .: Γ) N B ϕ2 ->
  (* --------------------------------------- *)
  CWt Γ (cLet M N) B (ϕ1 E+ ϕ2)

| T_CPair M1 M2 B1 B2 ϕ :
  CWt Γ M1 B1 ϕ ->
  CWt Γ M2 B2 ϕ ->
  (* --------------------------------- *)
  CWt Γ (cPair M1 M2) (CPair B1 B2) ϕ

| T_Fst M B1 B2 ϕ :
  CWt Γ M (CPair B1 B2) ϕ ->
  (* ------------------------ *)
  CWt Γ (cFst M) B1 ϕ

| T_Snd M B1 B2 ϕ :
  CWt Γ M (CPair B1 B2) ϕ ->
  (* ------------------------ *)
  CWt Γ (cSnd M) B2 ϕ

| T_Seq V N B ϕ :
  VWt Γ V VUnit ->
  CWt Γ N B ϕ ->
  (*------------------*)
  CWt Γ (cSeq V N) B ϕ

| T_Case V M1 M2 A1 A2 B ϕ :
  VWt Γ V (VSum A1 A2) ->
  CWt (A1 .: Γ) M1 B ϕ ->
  CWt (A2 .: Γ) M2 B ϕ ->
  (*------------------------------*)
  CWt Γ (cCase V M1 M2) B ϕ

| T_Tick :
  (* ----------------------- *)
  CWt Γ cTick (CF VUnit) tick

| T_SubEff M B ϕ ϕ' :
  CWt Γ M B ϕ ->
  ϕ E<= ϕ' ->
  (* -------------------- *)
  CWt Γ M B ϕ'.

Hint Constructors VWt CWt : typing.
#[export] Hint Resolve T_Var T_Thunk T_Unit T_VPair T_Inl T_Inr 
  T_Abs T_App T_Force T_Split T_Ret T_Let T_CPair T_Fst T_Snd
  T_Seq T_Case T_SubEff : typing.

Scheme VWt_ind' := Induction for VWt Sort Prop
    with CWt_ind' := Induction for CWt Sort Prop.

Combined Scheme Wt_mutual from VWt_ind', CWt_ind'.
