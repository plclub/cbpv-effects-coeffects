Require Export cbpv.common.effects cbpv.common.coeffects cbpv.autosubst2.fintype.




Section ValTyCompTy.
Inductive ValTy  : Type :=
  | VUnit : ValTy 
  | VThunk : E   -> CompTy   -> ValTy 
  | VPair : ValTy   -> ValTy   -> ValTy 
  | VSum : ValTy   -> ValTy   -> ValTy 
 with CompTy  : Type :=
  | CAbs : ValTy   -> CompTy   -> CompTy 
  | CF : ValTy   -> CompTy 
  | CPair : CompTy   -> CompTy   -> CompTy .

Lemma congr_VUnit  : VUnit  = VUnit  .
Proof. congruence. Qed.

Lemma congr_VThunk  { s0 : E   } { s1 : CompTy   } { t0 : E   } { t1 : CompTy   } (H1 : s0 = t0) (H2 : s1 = t1) : VThunk s0 s1 = VThunk t0 t1 .
Proof. congruence. Qed.

Lemma congr_VPair  { s0 : ValTy   } { s1 : ValTy   } { t0 : ValTy   } { t1 : ValTy   } (H1 : s0 = t0) (H2 : s1 = t1) : VPair s0 s1 = VPair t0 t1 .
Proof. congruence. Qed.

Lemma congr_VSum  { s0 : ValTy   } { s1 : ValTy   } { t0 : ValTy   } { t1 : ValTy   } (H1 : s0 = t0) (H2 : s1 = t1) : VSum s0 s1 = VSum t0 t1 .
Proof. congruence. Qed.

Lemma congr_CAbs  { s0 : ValTy   } { s1 : CompTy   } { t0 : ValTy   } { t1 : CompTy   } (H1 : s0 = t0) (H2 : s1 = t1) : CAbs s0 s1 = CAbs t0 t1 .
Proof. congruence. Qed.

Lemma congr_CF  { s0 : ValTy   } { t0 : ValTy   } (H1 : s0 = t0) : CF s0 = CF t0 .
Proof. congruence. Qed.

Lemma congr_CPair  { s0 : CompTy   } { s1 : CompTy   } { t0 : CompTy   } { t1 : CompTy   } (H1 : s0 = t0) (H2 : s1 = t1) : CPair s0 s1 = CPair t0 t1 .
Proof. congruence. Qed.

End ValTyCompTy.

Section ValComp.
Inductive Val (nVal : nat) : Type :=
  | var_Val : (fin) (nVal) -> Val (nVal)
  | vUnit : Val (nVal)
  | vThunk : Comp  (nVal) -> Val (nVal)
  | vPair : Val  (nVal) -> Val  (nVal) -> Val (nVal)
  | vInl : Val  (nVal) -> Val (nVal)
  | vInr : Val  (nVal) -> Val (nVal)
 with Comp (nVal : nat) : Type :=
  | cAbs : Comp  ((S) nVal) -> Comp (nVal)
  | cApp : Comp  (nVal) -> Val  (nVal) -> Comp (nVal)
  | cForce : Val  (nVal) -> Comp (nVal)
  | cSplit : Val  (nVal) -> Comp  ((S) ((S) nVal)) -> Comp (nVal)
  | cRet : Val  (nVal) -> Comp (nVal)
  | cLet : Comp  (nVal) -> Comp  ((S) nVal) -> Comp (nVal)
  | cPair : Comp  (nVal) -> Comp  (nVal) -> Comp (nVal)
  | cFst : Comp  (nVal) -> Comp (nVal)
  | cSnd : Comp  (nVal) -> Comp (nVal)
  | cSeq : Val  (nVal) -> Comp  (nVal) -> Comp (nVal)
  | cCase : Val  (nVal) -> Comp  ((S) nVal) -> Comp  ((S) nVal) -> Comp (nVal)
  | cTick : Comp (nVal).

Lemma congr_vUnit { mVal : nat } : vUnit (mVal) = vUnit (mVal) .
Proof. congruence. Qed.

Lemma congr_vThunk { mVal : nat } { s0 : Comp  (mVal) } { t0 : Comp  (mVal) } (H1 : s0 = t0) : vThunk (mVal) s0 = vThunk (mVal) t0 .
Proof. congruence. Qed.

Lemma congr_vPair { mVal : nat } { s0 : Val  (mVal) } { s1 : Val  (mVal) } { t0 : Val  (mVal) } { t1 : Val  (mVal) } (H1 : s0 = t0) (H2 : s1 = t1) : vPair (mVal) s0 s1 = vPair (mVal) t0 t1 .
Proof. congruence. Qed.

Lemma congr_vInl { mVal : nat } { s0 : Val  (mVal) } { t0 : Val  (mVal) } (H1 : s0 = t0) : vInl (mVal) s0 = vInl (mVal) t0 .
Proof. congruence. Qed.

Lemma congr_vInr { mVal : nat } { s0 : Val  (mVal) } { t0 : Val  (mVal) } (H1 : s0 = t0) : vInr (mVal) s0 = vInr (mVal) t0 .
Proof. congruence. Qed.

Lemma congr_cAbs { mVal : nat } { s0 : Comp  ((S) mVal) } { t0 : Comp  ((S) mVal) } (H1 : s0 = t0) : cAbs (mVal) s0 = cAbs (mVal) t0 .
Proof. congruence. Qed.

Lemma congr_cApp { mVal : nat } { s0 : Comp  (mVal) } { s1 : Val  (mVal) } { t0 : Comp  (mVal) } { t1 : Val  (mVal) } (H1 : s0 = t0) (H2 : s1 = t1) : cApp (mVal) s0 s1 = cApp (mVal) t0 t1 .
Proof. congruence. Qed.

Lemma congr_cForce { mVal : nat } { s0 : Val  (mVal) } { t0 : Val  (mVal) } (H1 : s0 = t0) : cForce (mVal) s0 = cForce (mVal) t0 .
Proof. congruence. Qed.

Lemma congr_cSplit { mVal : nat } { s0 : Val  (mVal) } { s1 : Comp  ((S) ((S) mVal)) } { t0 : Val  (mVal) } { t1 : Comp  ((S) ((S) mVal)) } (H1 : s0 = t0) (H2 : s1 = t1) : cSplit (mVal) s0 s1 = cSplit (mVal) t0 t1 .
Proof. congruence. Qed.

Lemma congr_cRet { mVal : nat } { s0 : Val  (mVal) } { t0 : Val  (mVal) } (H1 : s0 = t0) : cRet (mVal) s0 = cRet (mVal) t0 .
Proof. congruence. Qed.

Lemma congr_cLet { mVal : nat } { s0 : Comp  (mVal) } { s1 : Comp  ((S) mVal) } { t0 : Comp  (mVal) } { t1 : Comp  ((S) mVal) } (H1 : s0 = t0) (H2 : s1 = t1) : cLet (mVal) s0 s1 = cLet (mVal) t0 t1 .
Proof. congruence. Qed.

Lemma congr_cPair { mVal : nat } { s0 : Comp  (mVal) } { s1 : Comp  (mVal) } { t0 : Comp  (mVal) } { t1 : Comp  (mVal) } (H1 : s0 = t0) (H2 : s1 = t1) : cPair (mVal) s0 s1 = cPair (mVal) t0 t1 .
Proof. congruence. Qed.

Lemma congr_cFst { mVal : nat } { s0 : Comp  (mVal) } { t0 : Comp  (mVal) } (H1 : s0 = t0) : cFst (mVal) s0 = cFst (mVal) t0 .
Proof. congruence. Qed.

Lemma congr_cSnd { mVal : nat } { s0 : Comp  (mVal) } { t0 : Comp  (mVal) } (H1 : s0 = t0) : cSnd (mVal) s0 = cSnd (mVal) t0 .
Proof. congruence. Qed.

Lemma congr_cSeq { mVal : nat } { s0 : Val  (mVal) } { s1 : Comp  (mVal) } { t0 : Val  (mVal) } { t1 : Comp  (mVal) } (H1 : s0 = t0) (H2 : s1 = t1) : cSeq (mVal) s0 s1 = cSeq (mVal) t0 t1 .
Proof. congruence. Qed.

Lemma congr_cCase { mVal : nat } { s0 : Val  (mVal) } { s1 : Comp  ((S) mVal) } { s2 : Comp  ((S) mVal) } { t0 : Val  (mVal) } { t1 : Comp  ((S) mVal) } { t2 : Comp  ((S) mVal) } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : cCase (mVal) s0 s1 s2 = cCase (mVal) t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_cTick { mVal : nat } : cTick (mVal) = cTick (mVal) .
Proof. congruence. Qed.

Definition upRen_Val_Val { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) ((S) (m)) -> (fin) ((S) (n)) :=
  (up_ren) xi.

Fixpoint ren_Val { mVal : nat } { nVal : nat } (xiVal : (fin) (mVal) -> (fin) (nVal)) (s : Val (mVal)) : Val (nVal) :=
    match s return Val (nVal) with
    | var_Val (_) s => (var_Val (nVal)) (xiVal s)
    | vUnit (_)  => vUnit (nVal)
    | vThunk (_) s0 => vThunk (nVal) ((ren_Comp xiVal) s0)
    | vPair (_) s0 s1 => vPair (nVal) ((ren_Val xiVal) s0) ((ren_Val xiVal) s1)
    | vInl (_) s0 => vInl (nVal) ((ren_Val xiVal) s0)
    | vInr (_) s0 => vInr (nVal) ((ren_Val xiVal) s0)
    end
 with ren_Comp { mVal : nat } { nVal : nat } (xiVal : (fin) (mVal) -> (fin) (nVal)) (s : Comp (mVal)) : Comp (nVal) :=
    match s return Comp (nVal) with
    | cAbs (_) s0 => cAbs (nVal) ((ren_Comp (upRen_Val_Val xiVal)) s0)
    | cApp (_) s0 s1 => cApp (nVal) ((ren_Comp xiVal) s0) ((ren_Val xiVal) s1)
    | cForce (_) s0 => cForce (nVal) ((ren_Val xiVal) s0)
    | cSplit (_) s0 s1 => cSplit (nVal) ((ren_Val xiVal) s0) ((ren_Comp (upRen_Val_Val (upRen_Val_Val xiVal))) s1)
    | cRet (_) s0 => cRet (nVal) ((ren_Val xiVal) s0)
    | cLet (_) s0 s1 => cLet (nVal) ((ren_Comp xiVal) s0) ((ren_Comp (upRen_Val_Val xiVal)) s1)
    | cPair (_) s0 s1 => cPair (nVal) ((ren_Comp xiVal) s0) ((ren_Comp xiVal) s1)
    | cFst (_) s0 => cFst (nVal) ((ren_Comp xiVal) s0)
    | cSnd (_) s0 => cSnd (nVal) ((ren_Comp xiVal) s0)
    | cSeq (_) s0 s1 => cSeq (nVal) ((ren_Val xiVal) s0) ((ren_Comp xiVal) s1)
    | cCase (_) s0 s1 s2 => cCase (nVal) ((ren_Val xiVal) s0) ((ren_Comp (upRen_Val_Val xiVal)) s1) ((ren_Comp (upRen_Val_Val xiVal)) s2)
    | cTick (_)  => cTick (nVal)
    end.

Definition up_Val_Val { m : nat } { nVal : nat } (sigma : (fin) (m) -> Val (nVal)) : (fin) ((S) (m)) -> Val ((S) nVal) :=
  (scons) ((var_Val ((S) nVal)) (var_zero)) ((funcomp) (ren_Val (shift)) sigma).

Fixpoint subst_Val { mVal : nat } { nVal : nat } (sigmaVal : (fin) (mVal) -> Val (nVal)) (s : Val (mVal)) : Val (nVal) :=
    match s return Val (nVal) with
    | var_Val (_) s => sigmaVal s
    | vUnit (_)  => vUnit (nVal)
    | vThunk (_) s0 => vThunk (nVal) ((subst_Comp sigmaVal) s0)
    | vPair (_) s0 s1 => vPair (nVal) ((subst_Val sigmaVal) s0) ((subst_Val sigmaVal) s1)
    | vInl (_) s0 => vInl (nVal) ((subst_Val sigmaVal) s0)
    | vInr (_) s0 => vInr (nVal) ((subst_Val sigmaVal) s0)
    end
 with subst_Comp { mVal : nat } { nVal : nat } (sigmaVal : (fin) (mVal) -> Val (nVal)) (s : Comp (mVal)) : Comp (nVal) :=
    match s return Comp (nVal) with
    | cAbs (_) s0 => cAbs (nVal) ((subst_Comp (up_Val_Val sigmaVal)) s0)
    | cApp (_) s0 s1 => cApp (nVal) ((subst_Comp sigmaVal) s0) ((subst_Val sigmaVal) s1)
    | cForce (_) s0 => cForce (nVal) ((subst_Val sigmaVal) s0)
    | cSplit (_) s0 s1 => cSplit (nVal) ((subst_Val sigmaVal) s0) ((subst_Comp (up_Val_Val (up_Val_Val sigmaVal))) s1)
    | cRet (_) s0 => cRet (nVal) ((subst_Val sigmaVal) s0)
    | cLet (_) s0 s1 => cLet (nVal) ((subst_Comp sigmaVal) s0) ((subst_Comp (up_Val_Val sigmaVal)) s1)
    | cPair (_) s0 s1 => cPair (nVal) ((subst_Comp sigmaVal) s0) ((subst_Comp sigmaVal) s1)
    | cFst (_) s0 => cFst (nVal) ((subst_Comp sigmaVal) s0)
    | cSnd (_) s0 => cSnd (nVal) ((subst_Comp sigmaVal) s0)
    | cSeq (_) s0 s1 => cSeq (nVal) ((subst_Val sigmaVal) s0) ((subst_Comp sigmaVal) s1)
    | cCase (_) s0 s1 s2 => cCase (nVal) ((subst_Val sigmaVal) s0) ((subst_Comp (up_Val_Val sigmaVal)) s1) ((subst_Comp (up_Val_Val sigmaVal)) s2)
    | cTick (_)  => cTick (nVal)
    end.

Definition upId_Val_Val { mVal : nat } (sigma : (fin) (mVal) -> Val (mVal)) (Eq : forall x, sigma x = (var_Val (mVal)) x) : forall x, (up_Val_Val sigma) x = (var_Val ((S) mVal)) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_Val (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint idSubst_Val { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (mVal)) (EqVal : forall x, sigmaVal x = (var_Val (mVal)) x) (s : Val (mVal)) : subst_Val sigmaVal s = s :=
    match s return subst_Val sigmaVal s = s with
    | var_Val (_) s => EqVal s
    | vUnit (_)  => congr_vUnit 
    | vThunk (_) s0 => congr_vThunk ((idSubst_Comp sigmaVal EqVal) s0)
    | vPair (_) s0 s1 => congr_vPair ((idSubst_Val sigmaVal EqVal) s0) ((idSubst_Val sigmaVal EqVal) s1)
    | vInl (_) s0 => congr_vInl ((idSubst_Val sigmaVal EqVal) s0)
    | vInr (_) s0 => congr_vInr ((idSubst_Val sigmaVal EqVal) s0)
    end
 with idSubst_Comp { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (mVal)) (EqVal : forall x, sigmaVal x = (var_Val (mVal)) x) (s : Comp (mVal)) : subst_Comp sigmaVal s = s :=
    match s return subst_Comp sigmaVal s = s with
    | cAbs (_) s0 => congr_cAbs ((idSubst_Comp (up_Val_Val sigmaVal) (upId_Val_Val (_) EqVal)) s0)
    | cApp (_) s0 s1 => congr_cApp ((idSubst_Comp sigmaVal EqVal) s0) ((idSubst_Val sigmaVal EqVal) s1)
    | cForce (_) s0 => congr_cForce ((idSubst_Val sigmaVal EqVal) s0)
    | cSplit (_) s0 s1 => congr_cSplit ((idSubst_Val sigmaVal EqVal) s0) ((idSubst_Comp (up_Val_Val (up_Val_Val sigmaVal)) (upId_Val_Val (_) (upId_Val_Val (_) EqVal))) s1)
    | cRet (_) s0 => congr_cRet ((idSubst_Val sigmaVal EqVal) s0)
    | cLet (_) s0 s1 => congr_cLet ((idSubst_Comp sigmaVal EqVal) s0) ((idSubst_Comp (up_Val_Val sigmaVal) (upId_Val_Val (_) EqVal)) s1)
    | cPair (_) s0 s1 => congr_cPair ((idSubst_Comp sigmaVal EqVal) s0) ((idSubst_Comp sigmaVal EqVal) s1)
    | cFst (_) s0 => congr_cFst ((idSubst_Comp sigmaVal EqVal) s0)
    | cSnd (_) s0 => congr_cSnd ((idSubst_Comp sigmaVal EqVal) s0)
    | cSeq (_) s0 s1 => congr_cSeq ((idSubst_Val sigmaVal EqVal) s0) ((idSubst_Comp sigmaVal EqVal) s1)
    | cCase (_) s0 s1 s2 => congr_cCase ((idSubst_Val sigmaVal EqVal) s0) ((idSubst_Comp (up_Val_Val sigmaVal) (upId_Val_Val (_) EqVal)) s1) ((idSubst_Comp (up_Val_Val sigmaVal) (upId_Val_Val (_) EqVal)) s2)
    | cTick (_)  => congr_cTick 
    end.

Definition upExtRen_Val_Val { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_Val_Val xi) x = (upRen_Val_Val zeta) x :=
  fun n => match n with
  | Some fin_n => (ap) (shift) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint extRen_Val { mVal : nat } { nVal : nat } (xiVal : (fin) (mVal) -> (fin) (nVal)) (zetaVal : (fin) (mVal) -> (fin) (nVal)) (EqVal : forall x, xiVal x = zetaVal x) (s : Val (mVal)) : ren_Val xiVal s = ren_Val zetaVal s :=
    match s return ren_Val xiVal s = ren_Val zetaVal s with
    | var_Val (_) s => (ap) (var_Val (nVal)) (EqVal s)
    | vUnit (_)  => congr_vUnit 
    | vThunk (_) s0 => congr_vThunk ((extRen_Comp xiVal zetaVal EqVal) s0)
    | vPair (_) s0 s1 => congr_vPair ((extRen_Val xiVal zetaVal EqVal) s0) ((extRen_Val xiVal zetaVal EqVal) s1)
    | vInl (_) s0 => congr_vInl ((extRen_Val xiVal zetaVal EqVal) s0)
    | vInr (_) s0 => congr_vInr ((extRen_Val xiVal zetaVal EqVal) s0)
    end
 with extRen_Comp { mVal : nat } { nVal : nat } (xiVal : (fin) (mVal) -> (fin) (nVal)) (zetaVal : (fin) (mVal) -> (fin) (nVal)) (EqVal : forall x, xiVal x = zetaVal x) (s : Comp (mVal)) : ren_Comp xiVal s = ren_Comp zetaVal s :=
    match s return ren_Comp xiVal s = ren_Comp zetaVal s with
    | cAbs (_) s0 => congr_cAbs ((extRen_Comp (upRen_Val_Val xiVal) (upRen_Val_Val zetaVal) (upExtRen_Val_Val (_) (_) EqVal)) s0)
    | cApp (_) s0 s1 => congr_cApp ((extRen_Comp xiVal zetaVal EqVal) s0) ((extRen_Val xiVal zetaVal EqVal) s1)
    | cForce (_) s0 => congr_cForce ((extRen_Val xiVal zetaVal EqVal) s0)
    | cSplit (_) s0 s1 => congr_cSplit ((extRen_Val xiVal zetaVal EqVal) s0) ((extRen_Comp (upRen_Val_Val (upRen_Val_Val xiVal)) (upRen_Val_Val (upRen_Val_Val zetaVal)) (upExtRen_Val_Val (_) (_) (upExtRen_Val_Val (_) (_) EqVal))) s1)
    | cRet (_) s0 => congr_cRet ((extRen_Val xiVal zetaVal EqVal) s0)
    | cLet (_) s0 s1 => congr_cLet ((extRen_Comp xiVal zetaVal EqVal) s0) ((extRen_Comp (upRen_Val_Val xiVal) (upRen_Val_Val zetaVal) (upExtRen_Val_Val (_) (_) EqVal)) s1)
    | cPair (_) s0 s1 => congr_cPair ((extRen_Comp xiVal zetaVal EqVal) s0) ((extRen_Comp xiVal zetaVal EqVal) s1)
    | cFst (_) s0 => congr_cFst ((extRen_Comp xiVal zetaVal EqVal) s0)
    | cSnd (_) s0 => congr_cSnd ((extRen_Comp xiVal zetaVal EqVal) s0)
    | cSeq (_) s0 s1 => congr_cSeq ((extRen_Val xiVal zetaVal EqVal) s0) ((extRen_Comp xiVal zetaVal EqVal) s1)
    | cCase (_) s0 s1 s2 => congr_cCase ((extRen_Val xiVal zetaVal EqVal) s0) ((extRen_Comp (upRen_Val_Val xiVal) (upRen_Val_Val zetaVal) (upExtRen_Val_Val (_) (_) EqVal)) s1) ((extRen_Comp (upRen_Val_Val xiVal) (upRen_Val_Val zetaVal) (upExtRen_Val_Val (_) (_) EqVal)) s2)
    | cTick (_)  => congr_cTick 
    end.

Definition upExt_Val_Val { m : nat } { nVal : nat } (sigma : (fin) (m) -> Val (nVal)) (tau : (fin) (m) -> Val (nVal)) (Eq : forall x, sigma x = tau x) : forall x, (up_Val_Val sigma) x = (up_Val_Val tau) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_Val (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint ext_Val { mVal : nat } { nVal : nat } (sigmaVal : (fin) (mVal) -> Val (nVal)) (tauVal : (fin) (mVal) -> Val (nVal)) (EqVal : forall x, sigmaVal x = tauVal x) (s : Val (mVal)) : subst_Val sigmaVal s = subst_Val tauVal s :=
    match s return subst_Val sigmaVal s = subst_Val tauVal s with
    | var_Val (_) s => EqVal s
    | vUnit (_)  => congr_vUnit 
    | vThunk (_) s0 => congr_vThunk ((ext_Comp sigmaVal tauVal EqVal) s0)
    | vPair (_) s0 s1 => congr_vPair ((ext_Val sigmaVal tauVal EqVal) s0) ((ext_Val sigmaVal tauVal EqVal) s1)
    | vInl (_) s0 => congr_vInl ((ext_Val sigmaVal tauVal EqVal) s0)
    | vInr (_) s0 => congr_vInr ((ext_Val sigmaVal tauVal EqVal) s0)
    end
 with ext_Comp { mVal : nat } { nVal : nat } (sigmaVal : (fin) (mVal) -> Val (nVal)) (tauVal : (fin) (mVal) -> Val (nVal)) (EqVal : forall x, sigmaVal x = tauVal x) (s : Comp (mVal)) : subst_Comp sigmaVal s = subst_Comp tauVal s :=
    match s return subst_Comp sigmaVal s = subst_Comp tauVal s with
    | cAbs (_) s0 => congr_cAbs ((ext_Comp (up_Val_Val sigmaVal) (up_Val_Val tauVal) (upExt_Val_Val (_) (_) EqVal)) s0)
    | cApp (_) s0 s1 => congr_cApp ((ext_Comp sigmaVal tauVal EqVal) s0) ((ext_Val sigmaVal tauVal EqVal) s1)
    | cForce (_) s0 => congr_cForce ((ext_Val sigmaVal tauVal EqVal) s0)
    | cSplit (_) s0 s1 => congr_cSplit ((ext_Val sigmaVal tauVal EqVal) s0) ((ext_Comp (up_Val_Val (up_Val_Val sigmaVal)) (up_Val_Val (up_Val_Val tauVal)) (upExt_Val_Val (_) (_) (upExt_Val_Val (_) (_) EqVal))) s1)
    | cRet (_) s0 => congr_cRet ((ext_Val sigmaVal tauVal EqVal) s0)
    | cLet (_) s0 s1 => congr_cLet ((ext_Comp sigmaVal tauVal EqVal) s0) ((ext_Comp (up_Val_Val sigmaVal) (up_Val_Val tauVal) (upExt_Val_Val (_) (_) EqVal)) s1)
    | cPair (_) s0 s1 => congr_cPair ((ext_Comp sigmaVal tauVal EqVal) s0) ((ext_Comp sigmaVal tauVal EqVal) s1)
    | cFst (_) s0 => congr_cFst ((ext_Comp sigmaVal tauVal EqVal) s0)
    | cSnd (_) s0 => congr_cSnd ((ext_Comp sigmaVal tauVal EqVal) s0)
    | cSeq (_) s0 s1 => congr_cSeq ((ext_Val sigmaVal tauVal EqVal) s0) ((ext_Comp sigmaVal tauVal EqVal) s1)
    | cCase (_) s0 s1 s2 => congr_cCase ((ext_Val sigmaVal tauVal EqVal) s0) ((ext_Comp (up_Val_Val sigmaVal) (up_Val_Val tauVal) (upExt_Val_Val (_) (_) EqVal)) s1) ((ext_Comp (up_Val_Val sigmaVal) (up_Val_Val tauVal) (upExt_Val_Val (_) (_) EqVal)) s2)
    | cTick (_)  => congr_cTick 
    end.

Definition up_ren_ren_Val_Val { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_Val_Val tau) (upRen_Val_Val xi)) x = (upRen_Val_Val theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_Val { kVal : nat } { lVal : nat } { mVal : nat } (xiVal : (fin) (mVal) -> (fin) (kVal)) (zetaVal : (fin) (kVal) -> (fin) (lVal)) (rhoVal : (fin) (mVal) -> (fin) (lVal)) (EqVal : forall x, ((funcomp) zetaVal xiVal) x = rhoVal x) (s : Val (mVal)) : ren_Val zetaVal (ren_Val xiVal s) = ren_Val rhoVal s :=
    match s return ren_Val zetaVal (ren_Val xiVal s) = ren_Val rhoVal s with
    | var_Val (_) s => (ap) (var_Val (lVal)) (EqVal s)
    | vUnit (_)  => congr_vUnit 
    | vThunk (_) s0 => congr_vThunk ((compRenRen_Comp xiVal zetaVal rhoVal EqVal) s0)
    | vPair (_) s0 s1 => congr_vPair ((compRenRen_Val xiVal zetaVal rhoVal EqVal) s0) ((compRenRen_Val xiVal zetaVal rhoVal EqVal) s1)
    | vInl (_) s0 => congr_vInl ((compRenRen_Val xiVal zetaVal rhoVal EqVal) s0)
    | vInr (_) s0 => congr_vInr ((compRenRen_Val xiVal zetaVal rhoVal EqVal) s0)
    end
 with compRenRen_Comp { kVal : nat } { lVal : nat } { mVal : nat } (xiVal : (fin) (mVal) -> (fin) (kVal)) (zetaVal : (fin) (kVal) -> (fin) (lVal)) (rhoVal : (fin) (mVal) -> (fin) (lVal)) (EqVal : forall x, ((funcomp) zetaVal xiVal) x = rhoVal x) (s : Comp (mVal)) : ren_Comp zetaVal (ren_Comp xiVal s) = ren_Comp rhoVal s :=
    match s return ren_Comp zetaVal (ren_Comp xiVal s) = ren_Comp rhoVal s with
    | cAbs (_) s0 => congr_cAbs ((compRenRen_Comp (upRen_Val_Val xiVal) (upRen_Val_Val zetaVal) (upRen_Val_Val rhoVal) (up_ren_ren (_) (_) (_) EqVal)) s0)
    | cApp (_) s0 s1 => congr_cApp ((compRenRen_Comp xiVal zetaVal rhoVal EqVal) s0) ((compRenRen_Val xiVal zetaVal rhoVal EqVal) s1)
    | cForce (_) s0 => congr_cForce ((compRenRen_Val xiVal zetaVal rhoVal EqVal) s0)
    | cSplit (_) s0 s1 => congr_cSplit ((compRenRen_Val xiVal zetaVal rhoVal EqVal) s0) ((compRenRen_Comp (upRen_Val_Val (upRen_Val_Val xiVal)) (upRen_Val_Val (upRen_Val_Val zetaVal)) (upRen_Val_Val (upRen_Val_Val rhoVal)) (up_ren_ren (_) (_) (_) (up_ren_ren (_) (_) (_) EqVal))) s1)
    | cRet (_) s0 => congr_cRet ((compRenRen_Val xiVal zetaVal rhoVal EqVal) s0)
    | cLet (_) s0 s1 => congr_cLet ((compRenRen_Comp xiVal zetaVal rhoVal EqVal) s0) ((compRenRen_Comp (upRen_Val_Val xiVal) (upRen_Val_Val zetaVal) (upRen_Val_Val rhoVal) (up_ren_ren (_) (_) (_) EqVal)) s1)
    | cPair (_) s0 s1 => congr_cPair ((compRenRen_Comp xiVal zetaVal rhoVal EqVal) s0) ((compRenRen_Comp xiVal zetaVal rhoVal EqVal) s1)
    | cFst (_) s0 => congr_cFst ((compRenRen_Comp xiVal zetaVal rhoVal EqVal) s0)
    | cSnd (_) s0 => congr_cSnd ((compRenRen_Comp xiVal zetaVal rhoVal EqVal) s0)
    | cSeq (_) s0 s1 => congr_cSeq ((compRenRen_Val xiVal zetaVal rhoVal EqVal) s0) ((compRenRen_Comp xiVal zetaVal rhoVal EqVal) s1)
    | cCase (_) s0 s1 s2 => congr_cCase ((compRenRen_Val xiVal zetaVal rhoVal EqVal) s0) ((compRenRen_Comp (upRen_Val_Val xiVal) (upRen_Val_Val zetaVal) (upRen_Val_Val rhoVal) (up_ren_ren (_) (_) (_) EqVal)) s1) ((compRenRen_Comp (upRen_Val_Val xiVal) (upRen_Val_Val zetaVal) (upRen_Val_Val rhoVal) (up_ren_ren (_) (_) (_) EqVal)) s2)
    | cTick (_)  => congr_cTick 
    end.

Definition up_ren_subst_Val_Val { k : nat } { l : nat } { mVal : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> Val (mVal)) (theta : (fin) (k) -> Val (mVal)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_Val_Val tau) (upRen_Val_Val xi)) x = (up_Val_Val theta) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_Val (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint compRenSubst_Val { kVal : nat } { lVal : nat } { mVal : nat } (xiVal : (fin) (mVal) -> (fin) (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) (thetaVal : (fin) (mVal) -> Val (lVal)) (EqVal : forall x, ((funcomp) tauVal xiVal) x = thetaVal x) (s : Val (mVal)) : subst_Val tauVal (ren_Val xiVal s) = subst_Val thetaVal s :=
    match s return subst_Val tauVal (ren_Val xiVal s) = subst_Val thetaVal s with
    | var_Val (_) s => EqVal s
    | vUnit (_)  => congr_vUnit 
    | vThunk (_) s0 => congr_vThunk ((compRenSubst_Comp xiVal tauVal thetaVal EqVal) s0)
    | vPair (_) s0 s1 => congr_vPair ((compRenSubst_Val xiVal tauVal thetaVal EqVal) s0) ((compRenSubst_Val xiVal tauVal thetaVal EqVal) s1)
    | vInl (_) s0 => congr_vInl ((compRenSubst_Val xiVal tauVal thetaVal EqVal) s0)
    | vInr (_) s0 => congr_vInr ((compRenSubst_Val xiVal tauVal thetaVal EqVal) s0)
    end
 with compRenSubst_Comp { kVal : nat } { lVal : nat } { mVal : nat } (xiVal : (fin) (mVal) -> (fin) (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) (thetaVal : (fin) (mVal) -> Val (lVal)) (EqVal : forall x, ((funcomp) tauVal xiVal) x = thetaVal x) (s : Comp (mVal)) : subst_Comp tauVal (ren_Comp xiVal s) = subst_Comp thetaVal s :=
    match s return subst_Comp tauVal (ren_Comp xiVal s) = subst_Comp thetaVal s with
    | cAbs (_) s0 => congr_cAbs ((compRenSubst_Comp (upRen_Val_Val xiVal) (up_Val_Val tauVal) (up_Val_Val thetaVal) (up_ren_subst_Val_Val (_) (_) (_) EqVal)) s0)
    | cApp (_) s0 s1 => congr_cApp ((compRenSubst_Comp xiVal tauVal thetaVal EqVal) s0) ((compRenSubst_Val xiVal tauVal thetaVal EqVal) s1)
    | cForce (_) s0 => congr_cForce ((compRenSubst_Val xiVal tauVal thetaVal EqVal) s0)
    | cSplit (_) s0 s1 => congr_cSplit ((compRenSubst_Val xiVal tauVal thetaVal EqVal) s0) ((compRenSubst_Comp (upRen_Val_Val (upRen_Val_Val xiVal)) (up_Val_Val (up_Val_Val tauVal)) (up_Val_Val (up_Val_Val thetaVal)) (up_ren_subst_Val_Val (_) (_) (_) (up_ren_subst_Val_Val (_) (_) (_) EqVal))) s1)
    | cRet (_) s0 => congr_cRet ((compRenSubst_Val xiVal tauVal thetaVal EqVal) s0)
    | cLet (_) s0 s1 => congr_cLet ((compRenSubst_Comp xiVal tauVal thetaVal EqVal) s0) ((compRenSubst_Comp (upRen_Val_Val xiVal) (up_Val_Val tauVal) (up_Val_Val thetaVal) (up_ren_subst_Val_Val (_) (_) (_) EqVal)) s1)
    | cPair (_) s0 s1 => congr_cPair ((compRenSubst_Comp xiVal tauVal thetaVal EqVal) s0) ((compRenSubst_Comp xiVal tauVal thetaVal EqVal) s1)
    | cFst (_) s0 => congr_cFst ((compRenSubst_Comp xiVal tauVal thetaVal EqVal) s0)
    | cSnd (_) s0 => congr_cSnd ((compRenSubst_Comp xiVal tauVal thetaVal EqVal) s0)
    | cSeq (_) s0 s1 => congr_cSeq ((compRenSubst_Val xiVal tauVal thetaVal EqVal) s0) ((compRenSubst_Comp xiVal tauVal thetaVal EqVal) s1)
    | cCase (_) s0 s1 s2 => congr_cCase ((compRenSubst_Val xiVal tauVal thetaVal EqVal) s0) ((compRenSubst_Comp (upRen_Val_Val xiVal) (up_Val_Val tauVal) (up_Val_Val thetaVal) (up_ren_subst_Val_Val (_) (_) (_) EqVal)) s1) ((compRenSubst_Comp (upRen_Val_Val xiVal) (up_Val_Val tauVal) (up_Val_Val thetaVal) (up_ren_subst_Val_Val (_) (_) (_) EqVal)) s2)
    | cTick (_)  => congr_cTick 
    end.

Definition up_subst_ren_Val_Val { k : nat } { lVal : nat } { mVal : nat } (sigma : (fin) (k) -> Val (lVal)) (zetaVal : (fin) (lVal) -> (fin) (mVal)) (theta : (fin) (k) -> Val (mVal)) (Eq : forall x, ((funcomp) (ren_Val zetaVal) sigma) x = theta x) : forall x, ((funcomp) (ren_Val (upRen_Val_Val zetaVal)) (up_Val_Val sigma)) x = (up_Val_Val theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenRen_Val (shift) (upRen_Val_Val zetaVal) ((funcomp) (shift) zetaVal) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_Val zetaVal (shift) ((funcomp) (shift) zetaVal) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_Val (shift)) (Eq fin_n)))
  | None  => eq_refl
  end.

Fixpoint compSubstRen_Val { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (zetaVal : (fin) (kVal) -> (fin) (lVal)) (thetaVal : (fin) (mVal) -> Val (lVal)) (EqVal : forall x, ((funcomp) (ren_Val zetaVal) sigmaVal) x = thetaVal x) (s : Val (mVal)) : ren_Val zetaVal (subst_Val sigmaVal s) = subst_Val thetaVal s :=
    match s return ren_Val zetaVal (subst_Val sigmaVal s) = subst_Val thetaVal s with
    | var_Val (_) s => EqVal s
    | vUnit (_)  => congr_vUnit 
    | vThunk (_) s0 => congr_vThunk ((compSubstRen_Comp sigmaVal zetaVal thetaVal EqVal) s0)
    | vPair (_) s0 s1 => congr_vPair ((compSubstRen_Val sigmaVal zetaVal thetaVal EqVal) s0) ((compSubstRen_Val sigmaVal zetaVal thetaVal EqVal) s1)
    | vInl (_) s0 => congr_vInl ((compSubstRen_Val sigmaVal zetaVal thetaVal EqVal) s0)
    | vInr (_) s0 => congr_vInr ((compSubstRen_Val sigmaVal zetaVal thetaVal EqVal) s0)
    end
 with compSubstRen_Comp { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (zetaVal : (fin) (kVal) -> (fin) (lVal)) (thetaVal : (fin) (mVal) -> Val (lVal)) (EqVal : forall x, ((funcomp) (ren_Val zetaVal) sigmaVal) x = thetaVal x) (s : Comp (mVal)) : ren_Comp zetaVal (subst_Comp sigmaVal s) = subst_Comp thetaVal s :=
    match s return ren_Comp zetaVal (subst_Comp sigmaVal s) = subst_Comp thetaVal s with
    | cAbs (_) s0 => congr_cAbs ((compSubstRen_Comp (up_Val_Val sigmaVal) (upRen_Val_Val zetaVal) (up_Val_Val thetaVal) (up_subst_ren_Val_Val (_) (_) (_) EqVal)) s0)
    | cApp (_) s0 s1 => congr_cApp ((compSubstRen_Comp sigmaVal zetaVal thetaVal EqVal) s0) ((compSubstRen_Val sigmaVal zetaVal thetaVal EqVal) s1)
    | cForce (_) s0 => congr_cForce ((compSubstRen_Val sigmaVal zetaVal thetaVal EqVal) s0)
    | cSplit (_) s0 s1 => congr_cSplit ((compSubstRen_Val sigmaVal zetaVal thetaVal EqVal) s0) ((compSubstRen_Comp (up_Val_Val (up_Val_Val sigmaVal)) (upRen_Val_Val (upRen_Val_Val zetaVal)) (up_Val_Val (up_Val_Val thetaVal)) (up_subst_ren_Val_Val (_) (_) (_) (up_subst_ren_Val_Val (_) (_) (_) EqVal))) s1)
    | cRet (_) s0 => congr_cRet ((compSubstRen_Val sigmaVal zetaVal thetaVal EqVal) s0)
    | cLet (_) s0 s1 => congr_cLet ((compSubstRen_Comp sigmaVal zetaVal thetaVal EqVal) s0) ((compSubstRen_Comp (up_Val_Val sigmaVal) (upRen_Val_Val zetaVal) (up_Val_Val thetaVal) (up_subst_ren_Val_Val (_) (_) (_) EqVal)) s1)
    | cPair (_) s0 s1 => congr_cPair ((compSubstRen_Comp sigmaVal zetaVal thetaVal EqVal) s0) ((compSubstRen_Comp sigmaVal zetaVal thetaVal EqVal) s1)
    | cFst (_) s0 => congr_cFst ((compSubstRen_Comp sigmaVal zetaVal thetaVal EqVal) s0)
    | cSnd (_) s0 => congr_cSnd ((compSubstRen_Comp sigmaVal zetaVal thetaVal EqVal) s0)
    | cSeq (_) s0 s1 => congr_cSeq ((compSubstRen_Val sigmaVal zetaVal thetaVal EqVal) s0) ((compSubstRen_Comp sigmaVal zetaVal thetaVal EqVal) s1)
    | cCase (_) s0 s1 s2 => congr_cCase ((compSubstRen_Val sigmaVal zetaVal thetaVal EqVal) s0) ((compSubstRen_Comp (up_Val_Val sigmaVal) (upRen_Val_Val zetaVal) (up_Val_Val thetaVal) (up_subst_ren_Val_Val (_) (_) (_) EqVal)) s1) ((compSubstRen_Comp (up_Val_Val sigmaVal) (upRen_Val_Val zetaVal) (up_Val_Val thetaVal) (up_subst_ren_Val_Val (_) (_) (_) EqVal)) s2)
    | cTick (_)  => congr_cTick 
    end.

Definition up_subst_subst_Val_Val { k : nat } { lVal : nat } { mVal : nat } (sigma : (fin) (k) -> Val (lVal)) (tauVal : (fin) (lVal) -> Val (mVal)) (theta : (fin) (k) -> Val (mVal)) (Eq : forall x, ((funcomp) (subst_Val tauVal) sigma) x = theta x) : forall x, ((funcomp) (subst_Val (up_Val_Val tauVal)) (up_Val_Val sigma)) x = (up_Val_Val theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenSubst_Val (shift) (up_Val_Val tauVal) ((funcomp) (up_Val_Val tauVal) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_Val tauVal (shift) ((funcomp) (ren_Val (shift)) tauVal) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_Val (shift)) (Eq fin_n)))
  | None  => eq_refl
  end.

Fixpoint compSubstSubst_Val { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) (thetaVal : (fin) (mVal) -> Val (lVal)) (EqVal : forall x, ((funcomp) (subst_Val tauVal) sigmaVal) x = thetaVal x) (s : Val (mVal)) : subst_Val tauVal (subst_Val sigmaVal s) = subst_Val thetaVal s :=
    match s return subst_Val tauVal (subst_Val sigmaVal s) = subst_Val thetaVal s with
    | var_Val (_) s => EqVal s
    | vUnit (_)  => congr_vUnit 
    | vThunk (_) s0 => congr_vThunk ((compSubstSubst_Comp sigmaVal tauVal thetaVal EqVal) s0)
    | vPair (_) s0 s1 => congr_vPair ((compSubstSubst_Val sigmaVal tauVal thetaVal EqVal) s0) ((compSubstSubst_Val sigmaVal tauVal thetaVal EqVal) s1)
    | vInl (_) s0 => congr_vInl ((compSubstSubst_Val sigmaVal tauVal thetaVal EqVal) s0)
    | vInr (_) s0 => congr_vInr ((compSubstSubst_Val sigmaVal tauVal thetaVal EqVal) s0)
    end
 with compSubstSubst_Comp { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) (thetaVal : (fin) (mVal) -> Val (lVal)) (EqVal : forall x, ((funcomp) (subst_Val tauVal) sigmaVal) x = thetaVal x) (s : Comp (mVal)) : subst_Comp tauVal (subst_Comp sigmaVal s) = subst_Comp thetaVal s :=
    match s return subst_Comp tauVal (subst_Comp sigmaVal s) = subst_Comp thetaVal s with
    | cAbs (_) s0 => congr_cAbs ((compSubstSubst_Comp (up_Val_Val sigmaVal) (up_Val_Val tauVal) (up_Val_Val thetaVal) (up_subst_subst_Val_Val (_) (_) (_) EqVal)) s0)
    | cApp (_) s0 s1 => congr_cApp ((compSubstSubst_Comp sigmaVal tauVal thetaVal EqVal) s0) ((compSubstSubst_Val sigmaVal tauVal thetaVal EqVal) s1)
    | cForce (_) s0 => congr_cForce ((compSubstSubst_Val sigmaVal tauVal thetaVal EqVal) s0)
    | cSplit (_) s0 s1 => congr_cSplit ((compSubstSubst_Val sigmaVal tauVal thetaVal EqVal) s0) ((compSubstSubst_Comp (up_Val_Val (up_Val_Val sigmaVal)) (up_Val_Val (up_Val_Val tauVal)) (up_Val_Val (up_Val_Val thetaVal)) (up_subst_subst_Val_Val (_) (_) (_) (up_subst_subst_Val_Val (_) (_) (_) EqVal))) s1)
    | cRet (_) s0 => congr_cRet ((compSubstSubst_Val sigmaVal tauVal thetaVal EqVal) s0)
    | cLet (_) s0 s1 => congr_cLet ((compSubstSubst_Comp sigmaVal tauVal thetaVal EqVal) s0) ((compSubstSubst_Comp (up_Val_Val sigmaVal) (up_Val_Val tauVal) (up_Val_Val thetaVal) (up_subst_subst_Val_Val (_) (_) (_) EqVal)) s1)
    | cPair (_) s0 s1 => congr_cPair ((compSubstSubst_Comp sigmaVal tauVal thetaVal EqVal) s0) ((compSubstSubst_Comp sigmaVal tauVal thetaVal EqVal) s1)
    | cFst (_) s0 => congr_cFst ((compSubstSubst_Comp sigmaVal tauVal thetaVal EqVal) s0)
    | cSnd (_) s0 => congr_cSnd ((compSubstSubst_Comp sigmaVal tauVal thetaVal EqVal) s0)
    | cSeq (_) s0 s1 => congr_cSeq ((compSubstSubst_Val sigmaVal tauVal thetaVal EqVal) s0) ((compSubstSubst_Comp sigmaVal tauVal thetaVal EqVal) s1)
    | cCase (_) s0 s1 s2 => congr_cCase ((compSubstSubst_Val sigmaVal tauVal thetaVal EqVal) s0) ((compSubstSubst_Comp (up_Val_Val sigmaVal) (up_Val_Val tauVal) (up_Val_Val thetaVal) (up_subst_subst_Val_Val (_) (_) (_) EqVal)) s1) ((compSubstSubst_Comp (up_Val_Val sigmaVal) (up_Val_Val tauVal) (up_Val_Val thetaVal) (up_subst_subst_Val_Val (_) (_) (_) EqVal)) s2)
    | cTick (_)  => congr_cTick 
    end.

Definition rinstInst_up_Val_Val { m : nat } { nVal : nat } (xi : (fin) (m) -> (fin) (nVal)) (sigma : (fin) (m) -> Val (nVal)) (Eq : forall x, ((funcomp) (var_Val (nVal)) xi) x = sigma x) : forall x, ((funcomp) (var_Val ((S) nVal)) (upRen_Val_Val xi)) x = (up_Val_Val sigma) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_Val (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint rinst_inst_Val { mVal : nat } { nVal : nat } (xiVal : (fin) (mVal) -> (fin) (nVal)) (sigmaVal : (fin) (mVal) -> Val (nVal)) (EqVal : forall x, ((funcomp) (var_Val (nVal)) xiVal) x = sigmaVal x) (s : Val (mVal)) : ren_Val xiVal s = subst_Val sigmaVal s :=
    match s return ren_Val xiVal s = subst_Val sigmaVal s with
    | var_Val (_) s => EqVal s
    | vUnit (_)  => congr_vUnit 
    | vThunk (_) s0 => congr_vThunk ((rinst_inst_Comp xiVal sigmaVal EqVal) s0)
    | vPair (_) s0 s1 => congr_vPair ((rinst_inst_Val xiVal sigmaVal EqVal) s0) ((rinst_inst_Val xiVal sigmaVal EqVal) s1)
    | vInl (_) s0 => congr_vInl ((rinst_inst_Val xiVal sigmaVal EqVal) s0)
    | vInr (_) s0 => congr_vInr ((rinst_inst_Val xiVal sigmaVal EqVal) s0)
    end
 with rinst_inst_Comp { mVal : nat } { nVal : nat } (xiVal : (fin) (mVal) -> (fin) (nVal)) (sigmaVal : (fin) (mVal) -> Val (nVal)) (EqVal : forall x, ((funcomp) (var_Val (nVal)) xiVal) x = sigmaVal x) (s : Comp (mVal)) : ren_Comp xiVal s = subst_Comp sigmaVal s :=
    match s return ren_Comp xiVal s = subst_Comp sigmaVal s with
    | cAbs (_) s0 => congr_cAbs ((rinst_inst_Comp (upRen_Val_Val xiVal) (up_Val_Val sigmaVal) (rinstInst_up_Val_Val (_) (_) EqVal)) s0)
    | cApp (_) s0 s1 => congr_cApp ((rinst_inst_Comp xiVal sigmaVal EqVal) s0) ((rinst_inst_Val xiVal sigmaVal EqVal) s1)
    | cForce (_) s0 => congr_cForce ((rinst_inst_Val xiVal sigmaVal EqVal) s0)
    | cSplit (_) s0 s1 => congr_cSplit ((rinst_inst_Val xiVal sigmaVal EqVal) s0) ((rinst_inst_Comp (upRen_Val_Val (upRen_Val_Val xiVal)) (up_Val_Val (up_Val_Val sigmaVal)) (rinstInst_up_Val_Val (_) (_) (rinstInst_up_Val_Val (_) (_) EqVal))) s1)
    | cRet (_) s0 => congr_cRet ((rinst_inst_Val xiVal sigmaVal EqVal) s0)
    | cLet (_) s0 s1 => congr_cLet ((rinst_inst_Comp xiVal sigmaVal EqVal) s0) ((rinst_inst_Comp (upRen_Val_Val xiVal) (up_Val_Val sigmaVal) (rinstInst_up_Val_Val (_) (_) EqVal)) s1)
    | cPair (_) s0 s1 => congr_cPair ((rinst_inst_Comp xiVal sigmaVal EqVal) s0) ((rinst_inst_Comp xiVal sigmaVal EqVal) s1)
    | cFst (_) s0 => congr_cFst ((rinst_inst_Comp xiVal sigmaVal EqVal) s0)
    | cSnd (_) s0 => congr_cSnd ((rinst_inst_Comp xiVal sigmaVal EqVal) s0)
    | cSeq (_) s0 s1 => congr_cSeq ((rinst_inst_Val xiVal sigmaVal EqVal) s0) ((rinst_inst_Comp xiVal sigmaVal EqVal) s1)
    | cCase (_) s0 s1 s2 => congr_cCase ((rinst_inst_Val xiVal sigmaVal EqVal) s0) ((rinst_inst_Comp (upRen_Val_Val xiVal) (up_Val_Val sigmaVal) (rinstInst_up_Val_Val (_) (_) EqVal)) s1) ((rinst_inst_Comp (upRen_Val_Val xiVal) (up_Val_Val sigmaVal) (rinstInst_up_Val_Val (_) (_) EqVal)) s2)
    | cTick (_)  => congr_cTick 
    end.

Lemma rinstInst_Val { mVal : nat } { nVal : nat } (xiVal : (fin) (mVal) -> (fin) (nVal)) : ren_Val xiVal = subst_Val ((funcomp) (var_Val (nVal)) xiVal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_Val xiVal (_) (fun n => eq_refl) x)). Qed.

Lemma rinstInst_Comp { mVal : nat } { nVal : nat } (xiVal : (fin) (mVal) -> (fin) (nVal)) : ren_Comp xiVal = subst_Comp ((funcomp) (var_Val (nVal)) xiVal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_Comp xiVal (_) (fun n => eq_refl) x)). Qed.

Lemma instId_Val { mVal : nat } : subst_Val (var_Val (mVal)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_Val (var_Val (mVal)) (fun n => eq_refl) ((id) x))). Qed.

Lemma instId_Comp { mVal : nat } : subst_Comp (var_Val (mVal)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_Comp (var_Val (mVal)) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_Val { mVal : nat } : @ren_Val (mVal) (mVal) (id) = id .
Proof. exact ((eq_trans) (rinstInst_Val ((id) (_))) instId_Val). Qed.

Lemma rinstId_Comp { mVal : nat } : @ren_Comp (mVal) (mVal) (id) = id .
Proof. exact ((eq_trans) (rinstInst_Comp ((id) (_))) instId_Comp). Qed.

Lemma varL_Val { mVal : nat } { nVal : nat } (sigmaVal : (fin) (mVal) -> Val (nVal)) : (funcomp) (subst_Val sigmaVal) (var_Val (mVal)) = sigmaVal .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_Val { mVal : nat } { nVal : nat } (xiVal : (fin) (mVal) -> (fin) (nVal)) : (funcomp) (ren_Val xiVal) (var_Val (mVal)) = (funcomp) (var_Val (nVal)) xiVal .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_Val { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) (s : Val (mVal)) : subst_Val tauVal (subst_Val sigmaVal s) = subst_Val ((funcomp) (subst_Val tauVal) sigmaVal) s .
Proof. exact (compSubstSubst_Val sigmaVal tauVal (_) (fun n => eq_refl) s). Qed.

Lemma compComp_Comp { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) (s : Comp (mVal)) : subst_Comp tauVal (subst_Comp sigmaVal s) = subst_Comp ((funcomp) (subst_Val tauVal) sigmaVal) s .
Proof. exact (compSubstSubst_Comp sigmaVal tauVal (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_Val { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) : (funcomp) (subst_Val tauVal) (subst_Val sigmaVal) = subst_Val ((funcomp) (subst_Val tauVal) sigmaVal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_Val sigmaVal tauVal n)). Qed.

Lemma compComp'_Comp { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) : (funcomp) (subst_Comp tauVal) (subst_Comp sigmaVal) = subst_Comp ((funcomp) (subst_Val tauVal) sigmaVal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_Comp sigmaVal tauVal n)). Qed.

Lemma compRen_Val { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (zetaVal : (fin) (kVal) -> (fin) (lVal)) (s : Val (mVal)) : ren_Val zetaVal (subst_Val sigmaVal s) = subst_Val ((funcomp) (ren_Val zetaVal) sigmaVal) s .
Proof. exact (compSubstRen_Val sigmaVal zetaVal (_) (fun n => eq_refl) s). Qed.

Lemma compRen_Comp { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (zetaVal : (fin) (kVal) -> (fin) (lVal)) (s : Comp (mVal)) : ren_Comp zetaVal (subst_Comp sigmaVal s) = subst_Comp ((funcomp) (ren_Val zetaVal) sigmaVal) s .
Proof. exact (compSubstRen_Comp sigmaVal zetaVal (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_Val { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (zetaVal : (fin) (kVal) -> (fin) (lVal)) : (funcomp) (ren_Val zetaVal) (subst_Val sigmaVal) = subst_Val ((funcomp) (ren_Val zetaVal) sigmaVal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_Val sigmaVal zetaVal n)). Qed.

Lemma compRen'_Comp { kVal : nat } { lVal : nat } { mVal : nat } (sigmaVal : (fin) (mVal) -> Val (kVal)) (zetaVal : (fin) (kVal) -> (fin) (lVal)) : (funcomp) (ren_Comp zetaVal) (subst_Comp sigmaVal) = subst_Comp ((funcomp) (ren_Val zetaVal) sigmaVal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_Comp sigmaVal zetaVal n)). Qed.

Lemma renComp_Val { kVal : nat } { lVal : nat } { mVal : nat } (xiVal : (fin) (mVal) -> (fin) (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) (s : Val (mVal)) : subst_Val tauVal (ren_Val xiVal s) = subst_Val ((funcomp) tauVal xiVal) s .
Proof. exact (compRenSubst_Val xiVal tauVal (_) (fun n => eq_refl) s). Qed.

Lemma renComp_Comp { kVal : nat } { lVal : nat } { mVal : nat } (xiVal : (fin) (mVal) -> (fin) (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) (s : Comp (mVal)) : subst_Comp tauVal (ren_Comp xiVal s) = subst_Comp ((funcomp) tauVal xiVal) s .
Proof. exact (compRenSubst_Comp xiVal tauVal (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_Val { kVal : nat } { lVal : nat } { mVal : nat } (xiVal : (fin) (mVal) -> (fin) (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) : (funcomp) (subst_Val tauVal) (ren_Val xiVal) = subst_Val ((funcomp) tauVal xiVal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_Val xiVal tauVal n)). Qed.

Lemma renComp'_Comp { kVal : nat } { lVal : nat } { mVal : nat } (xiVal : (fin) (mVal) -> (fin) (kVal)) (tauVal : (fin) (kVal) -> Val (lVal)) : (funcomp) (subst_Comp tauVal) (ren_Comp xiVal) = subst_Comp ((funcomp) tauVal xiVal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_Comp xiVal tauVal n)). Qed.

Lemma renRen_Val { kVal : nat } { lVal : nat } { mVal : nat } (xiVal : (fin) (mVal) -> (fin) (kVal)) (zetaVal : (fin) (kVal) -> (fin) (lVal)) (s : Val (mVal)) : ren_Val zetaVal (ren_Val xiVal s) = ren_Val ((funcomp) zetaVal xiVal) s .
Proof. exact (compRenRen_Val xiVal zetaVal (_) (fun n => eq_refl) s). Qed.

Lemma renRen_Comp { kVal : nat } { lVal : nat } { mVal : nat } (xiVal : (fin) (mVal) -> (fin) (kVal)) (zetaVal : (fin) (kVal) -> (fin) (lVal)) (s : Comp (mVal)) : ren_Comp zetaVal (ren_Comp xiVal s) = ren_Comp ((funcomp) zetaVal xiVal) s .
Proof. exact (compRenRen_Comp xiVal zetaVal (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_Val { kVal : nat } { lVal : nat } { mVal : nat } (xiVal : (fin) (mVal) -> (fin) (kVal)) (zetaVal : (fin) (kVal) -> (fin) (lVal)) : (funcomp) (ren_Val zetaVal) (ren_Val xiVal) = ren_Val ((funcomp) zetaVal xiVal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_Val xiVal zetaVal n)). Qed.

Lemma renRen'_Comp { kVal : nat } { lVal : nat } { mVal : nat } (xiVal : (fin) (mVal) -> (fin) (kVal)) (zetaVal : (fin) (kVal) -> (fin) (lVal)) : (funcomp) (ren_Comp zetaVal) (ren_Comp xiVal) = ren_Comp ((funcomp) zetaVal xiVal) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_Comp xiVal zetaVal n)). Qed.

End ValComp.

Arguments var_Val {nVal}.

Arguments vUnit {nVal}.

Arguments vThunk {nVal}.

Arguments vPair {nVal}.

Arguments vInl {nVal}.

Arguments vInr {nVal}.

Arguments cAbs {nVal}.

Arguments cApp {nVal}.

Arguments cForce {nVal}.

Arguments cSplit {nVal}.

Arguments cRet {nVal}.

Arguments cLet {nVal}.

Arguments cPair {nVal}.

Arguments cFst {nVal}.

Arguments cSnd {nVal}.

Arguments cSeq {nVal}.

Arguments cCase {nVal}.

Arguments cTick {nVal}.

Global Instance Subst_Val { mVal : nat } { nVal : nat } : Subst1 ((fin) (mVal) -> Val (nVal)) (Val (mVal)) (Val (nVal)) := @subst_Val (mVal) (nVal) .

Global Instance Subst_Comp { mVal : nat } { nVal : nat } : Subst1 ((fin) (mVal) -> Val (nVal)) (Comp (mVal)) (Comp (nVal)) := @subst_Comp (mVal) (nVal) .

Global Instance Ren_Val { mVal : nat } { nVal : nat } : Ren1 ((fin) (mVal) -> (fin) (nVal)) (Val (mVal)) (Val (nVal)) := @ren_Val (mVal) (nVal) .

Global Instance Ren_Comp { mVal : nat } { nVal : nat } : Ren1 ((fin) (mVal) -> (fin) (nVal)) (Comp (mVal)) (Comp (nVal)) := @ren_Comp (mVal) (nVal) .

Global Instance VarInstance_Val { mVal : nat } : Var ((fin) (mVal)) (Val (mVal)) := @var_Val (mVal) .

Notation "x '__Val'" := (var_Val x) (at level 5, format "x __Val") : subst_scope.

Notation "x '__Val'" := (@ids (_) (_) VarInstance_Val x) (at level 5, only printing, format "x __Val") : subst_scope.

Notation "'var'" := (var_Val) (only printing, at level 1) : subst_scope.

Class Up_Val X Y := up_Val : X -> Y.

Notation "↑__Val" := (up_Val) (only printing) : subst_scope.

Notation "↑__Val" := (up_Val_Val) (only printing) : subst_scope.

Global Instance Up_Val_Val { m : nat } { nVal : nat } : Up_Val (_) (_) := @up_Val_Val (m) (nVal) .

Notation "s [ sigmaVal ]" := (subst_Val sigmaVal s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaVal ]" := (subst_Val sigmaVal) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xiVal ⟩" := (ren_Val xiVal s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xiVal ⟩" := (ren_Val xiVal) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmaVal ]" := (subst_Comp sigmaVal s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaVal ]" := (subst_Comp sigmaVal) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xiVal ⟩" := (ren_Comp xiVal s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xiVal ⟩" := (ren_Comp xiVal) (at level 1, left associativity, only printing) : fscope.

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_Val,  Subst_Comp,  Ren_Val,  Ren_Comp,  VarInstance_Val.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_Val,  Subst_Comp,  Ren_Val,  Ren_Comp,  VarInstance_Val in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_Val| progress rewrite ?compComp_Val| progress rewrite ?compComp'_Val| progress rewrite ?instId_Comp| progress rewrite ?compComp_Comp| progress rewrite ?compComp'_Comp| progress rewrite ?rinstId_Val| progress rewrite ?compRen_Val| progress rewrite ?compRen'_Val| progress rewrite ?renComp_Val| progress rewrite ?renComp'_Val| progress rewrite ?renRen_Val| progress rewrite ?renRen'_Val| progress rewrite ?rinstId_Comp| progress rewrite ?compRen_Comp| progress rewrite ?compRen'_Comp| progress rewrite ?renComp_Comp| progress rewrite ?renComp'_Comp| progress rewrite ?renRen_Comp| progress rewrite ?renRen'_Comp| progress rewrite ?varL_Val| progress rewrite ?varLRen_Val| progress (unfold up_ren, upRen_Val_Val, up_Val_Val)| progress (cbn [subst_Val subst_Comp ren_Val ren_Comp])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_Val in *| progress rewrite ?compComp_Val in *| progress rewrite ?compComp'_Val in *| progress rewrite ?instId_Comp in *| progress rewrite ?compComp_Comp in *| progress rewrite ?compComp'_Comp in *| progress rewrite ?rinstId_Val in *| progress rewrite ?compRen_Val in *| progress rewrite ?compRen'_Val in *| progress rewrite ?renComp_Val in *| progress rewrite ?renComp'_Val in *| progress rewrite ?renRen_Val in *| progress rewrite ?renRen'_Val in *| progress rewrite ?rinstId_Comp in *| progress rewrite ?compRen_Comp in *| progress rewrite ?compRen'_Comp in *| progress rewrite ?renComp_Comp in *| progress rewrite ?renComp'_Comp in *| progress rewrite ?renRen_Comp in *| progress rewrite ?renRen'_Comp in *| progress rewrite ?varL_Val in *| progress rewrite ?varLRen_Val in *| progress (unfold up_ren, upRen_Val_Val, up_Val_Val in *)| progress (cbn [subst_Val subst_Comp ren_Val ren_Comp] in *)| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_Val); try repeat (erewrite rinstInst_Comp).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_Val); try repeat (erewrite <- rinstInst_Comp).

