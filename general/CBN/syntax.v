Require Export cbpv.common.effects cbpv.common.coeffects cbpv.autosubst2.fintype.




Section Tm.
Inductive Tm (nTm : nat) : Type :=
  | var_Tm : (fin) (nTm) -> Tm (nTm)
  | abs : Q   -> Tm  ((S) nTm) -> Tm (nTm)
  | app : Tm  (nTm) -> Tm  (nTm) -> Tm (nTm)
  | unit : Tm (nTm)
  | seq : Tm  (nTm) -> Tm  (nTm) -> Tm (nTm)
  | inl : Tm  (nTm) -> Tm (nTm)
  | inr : Tm  (nTm) -> Tm (nTm)
  | prod : Tm  (nTm) -> Tm  (nTm) -> Tm (nTm)
  | fst : Tm  (nTm) -> Tm (nTm)
  | snd : Tm  (nTm) -> Tm (nTm)
  | case : Q   -> Tm  (nTm) -> Tm  ((S) nTm) -> Tm  ((S) nTm) -> Tm (nTm)
  | box : Q   -> Tm  (nTm) -> Tm (nTm)
  | unbox : Q   -> Tm  (nTm) -> Tm  ((S) nTm) -> Tm (nTm).

Lemma congr_abs { mTm : nat } { s0 : Q   } { s1 : Tm  ((S) mTm) } { t0 : Q   } { t1 : Tm  ((S) mTm) } (H1 : s0 = t0) (H2 : s1 = t1) : abs (mTm) s0 s1 = abs (mTm) t0 t1 .
Proof. congruence. Qed.

Lemma congr_app { mTm : nat } { s0 : Tm  (mTm) } { s1 : Tm  (mTm) } { t0 : Tm  (mTm) } { t1 : Tm  (mTm) } (H1 : s0 = t0) (H2 : s1 = t1) : app (mTm) s0 s1 = app (mTm) t0 t1 .
Proof. congruence. Qed.

Lemma congr_unit { mTm : nat } : unit (mTm) = unit (mTm) .
Proof. congruence. Qed.

Lemma congr_seq { mTm : nat } { s0 : Tm  (mTm) } { s1 : Tm  (mTm) } { t0 : Tm  (mTm) } { t1 : Tm  (mTm) } (H1 : s0 = t0) (H2 : s1 = t1) : seq (mTm) s0 s1 = seq (mTm) t0 t1 .
Proof. congruence. Qed.

Lemma congr_inl { mTm : nat } { s0 : Tm  (mTm) } { t0 : Tm  (mTm) } (H1 : s0 = t0) : inl (mTm) s0 = inl (mTm) t0 .
Proof. congruence. Qed.

Lemma congr_inr { mTm : nat } { s0 : Tm  (mTm) } { t0 : Tm  (mTm) } (H1 : s0 = t0) : inr (mTm) s0 = inr (mTm) t0 .
Proof. congruence. Qed.

Lemma congr_prod { mTm : nat } { s0 : Tm  (mTm) } { s1 : Tm  (mTm) } { t0 : Tm  (mTm) } { t1 : Tm  (mTm) } (H1 : s0 = t0) (H2 : s1 = t1) : prod (mTm) s0 s1 = prod (mTm) t0 t1 .
Proof. congruence. Qed.

Lemma congr_fst { mTm : nat } { s0 : Tm  (mTm) } { t0 : Tm  (mTm) } (H1 : s0 = t0) : fst (mTm) s0 = fst (mTm) t0 .
Proof. congruence. Qed.

Lemma congr_snd { mTm : nat } { s0 : Tm  (mTm) } { t0 : Tm  (mTm) } (H1 : s0 = t0) : snd (mTm) s0 = snd (mTm) t0 .
Proof. congruence. Qed.

Lemma congr_case { mTm : nat } { s0 : Q   } { s1 : Tm  (mTm) } { s2 : Tm  ((S) mTm) } { s3 : Tm  ((S) mTm) } { t0 : Q   } { t1 : Tm  (mTm) } { t2 : Tm  ((S) mTm) } { t3 : Tm  ((S) mTm) } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) (H4 : s3 = t3) : case (mTm) s0 s1 s2 s3 = case (mTm) t0 t1 t2 t3 .
Proof. congruence. Qed.

Lemma congr_box { mTm : nat } { s0 : Q   } { s1 : Tm  (mTm) } { t0 : Q   } { t1 : Tm  (mTm) } (H1 : s0 = t0) (H2 : s1 = t1) : box (mTm) s0 s1 = box (mTm) t0 t1 .
Proof. congruence. Qed.

Lemma congr_unbox { mTm : nat } { s0 : Q   } { s1 : Tm  (mTm) } { s2 : Tm  ((S) mTm) } { t0 : Q   } { t1 : Tm  (mTm) } { t2 : Tm  ((S) mTm) } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : unbox (mTm) s0 s1 s2 = unbox (mTm) t0 t1 t2 .
Proof. congruence. Qed.

Definition upRen_Tm_Tm { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) ((S) (m)) -> (fin) ((S) (n)) :=
  (up_ren) xi.

Fixpoint ren_Tm { mTm : nat } { nTm : nat } (xiTm : (fin) (mTm) -> (fin) (nTm)) (s : Tm (mTm)) : Tm (nTm) :=
    match s return Tm (nTm) with
    | var_Tm (_) s => (var_Tm (nTm)) (xiTm s)
    | abs (_) s0 s1 => abs (nTm) ((fun x => x) s0) ((ren_Tm (upRen_Tm_Tm xiTm)) s1)
    | app (_) s0 s1 => app (nTm) ((ren_Tm xiTm) s0) ((ren_Tm xiTm) s1)
    | unit (_)  => unit (nTm)
    | seq (_) s0 s1 => seq (nTm) ((ren_Tm xiTm) s0) ((ren_Tm xiTm) s1)
    | inl (_) s0 => inl (nTm) ((ren_Tm xiTm) s0)
    | inr (_) s0 => inr (nTm) ((ren_Tm xiTm) s0)
    | prod (_) s0 s1 => prod (nTm) ((ren_Tm xiTm) s0) ((ren_Tm xiTm) s1)
    | fst (_) s0 => fst (nTm) ((ren_Tm xiTm) s0)
    | snd (_) s0 => snd (nTm) ((ren_Tm xiTm) s0)
    | case (_) s0 s1 s2 s3 => case (nTm) ((fun x => x) s0) ((ren_Tm xiTm) s1) ((ren_Tm (upRen_Tm_Tm xiTm)) s2) ((ren_Tm (upRen_Tm_Tm xiTm)) s3)
    | box (_) s0 s1 => box (nTm) ((fun x => x) s0) ((ren_Tm xiTm) s1)
    | unbox (_) s0 s1 s2 => unbox (nTm) ((fun x => x) s0) ((ren_Tm xiTm) s1) ((ren_Tm (upRen_Tm_Tm xiTm)) s2)
    end.

Definition up_Tm_Tm { m : nat } { nTm : nat } (sigma : (fin) (m) -> Tm (nTm)) : (fin) ((S) (m)) -> Tm ((S) nTm) :=
  (scons) ((var_Tm ((S) nTm)) (var_zero)) ((funcomp) (ren_Tm (shift)) sigma).

Fixpoint subst_Tm { mTm : nat } { nTm : nat } (sigmaTm : (fin) (mTm) -> Tm (nTm)) (s : Tm (mTm)) : Tm (nTm) :=
    match s return Tm (nTm) with
    | var_Tm (_) s => sigmaTm s
    | abs (_) s0 s1 => abs (nTm) ((fun x => x) s0) ((subst_Tm (up_Tm_Tm sigmaTm)) s1)
    | app (_) s0 s1 => app (nTm) ((subst_Tm sigmaTm) s0) ((subst_Tm sigmaTm) s1)
    | unit (_)  => unit (nTm)
    | seq (_) s0 s1 => seq (nTm) ((subst_Tm sigmaTm) s0) ((subst_Tm sigmaTm) s1)
    | inl (_) s0 => inl (nTm) ((subst_Tm sigmaTm) s0)
    | inr (_) s0 => inr (nTm) ((subst_Tm sigmaTm) s0)
    | prod (_) s0 s1 => prod (nTm) ((subst_Tm sigmaTm) s0) ((subst_Tm sigmaTm) s1)
    | fst (_) s0 => fst (nTm) ((subst_Tm sigmaTm) s0)
    | snd (_) s0 => snd (nTm) ((subst_Tm sigmaTm) s0)
    | case (_) s0 s1 s2 s3 => case (nTm) ((fun x => x) s0) ((subst_Tm sigmaTm) s1) ((subst_Tm (up_Tm_Tm sigmaTm)) s2) ((subst_Tm (up_Tm_Tm sigmaTm)) s3)
    | box (_) s0 s1 => box (nTm) ((fun x => x) s0) ((subst_Tm sigmaTm) s1)
    | unbox (_) s0 s1 s2 => unbox (nTm) ((fun x => x) s0) ((subst_Tm sigmaTm) s1) ((subst_Tm (up_Tm_Tm sigmaTm)) s2)
    end.

Definition upId_Tm_Tm { mTm : nat } (sigma : (fin) (mTm) -> Tm (mTm)) (Eq : forall x, sigma x = (var_Tm (mTm)) x) : forall x, (up_Tm_Tm sigma) x = (var_Tm ((S) mTm)) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_Tm (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint idSubst_Tm { mTm : nat } (sigmaTm : (fin) (mTm) -> Tm (mTm)) (EqTm : forall x, sigmaTm x = (var_Tm (mTm)) x) (s : Tm (mTm)) : subst_Tm sigmaTm s = s :=
    match s return subst_Tm sigmaTm s = s with
    | var_Tm (_) s => EqTm s
    | abs (_) s0 s1 => congr_abs ((fun x => (eq_refl) x) s0) ((idSubst_Tm (up_Tm_Tm sigmaTm) (upId_Tm_Tm (_) EqTm)) s1)
    | app (_) s0 s1 => congr_app ((idSubst_Tm sigmaTm EqTm) s0) ((idSubst_Tm sigmaTm EqTm) s1)
    | unit (_)  => congr_unit 
    | seq (_) s0 s1 => congr_seq ((idSubst_Tm sigmaTm EqTm) s0) ((idSubst_Tm sigmaTm EqTm) s1)
    | inl (_) s0 => congr_inl ((idSubst_Tm sigmaTm EqTm) s0)
    | inr (_) s0 => congr_inr ((idSubst_Tm sigmaTm EqTm) s0)
    | prod (_) s0 s1 => congr_prod ((idSubst_Tm sigmaTm EqTm) s0) ((idSubst_Tm sigmaTm EqTm) s1)
    | fst (_) s0 => congr_fst ((idSubst_Tm sigmaTm EqTm) s0)
    | snd (_) s0 => congr_snd ((idSubst_Tm sigmaTm EqTm) s0)
    | case (_) s0 s1 s2 s3 => congr_case ((fun x => (eq_refl) x) s0) ((idSubst_Tm sigmaTm EqTm) s1) ((idSubst_Tm (up_Tm_Tm sigmaTm) (upId_Tm_Tm (_) EqTm)) s2) ((idSubst_Tm (up_Tm_Tm sigmaTm) (upId_Tm_Tm (_) EqTm)) s3)
    | box (_) s0 s1 => congr_box ((fun x => (eq_refl) x) s0) ((idSubst_Tm sigmaTm EqTm) s1)
    | unbox (_) s0 s1 s2 => congr_unbox ((fun x => (eq_refl) x) s0) ((idSubst_Tm sigmaTm EqTm) s1) ((idSubst_Tm (up_Tm_Tm sigmaTm) (upId_Tm_Tm (_) EqTm)) s2)
    end.

Definition upExtRen_Tm_Tm { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_Tm_Tm xi) x = (upRen_Tm_Tm zeta) x :=
  fun n => match n with
  | Some fin_n => (ap) (shift) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint extRen_Tm { mTm : nat } { nTm : nat } (xiTm : (fin) (mTm) -> (fin) (nTm)) (zetaTm : (fin) (mTm) -> (fin) (nTm)) (EqTm : forall x, xiTm x = zetaTm x) (s : Tm (mTm)) : ren_Tm xiTm s = ren_Tm zetaTm s :=
    match s return ren_Tm xiTm s = ren_Tm zetaTm s with
    | var_Tm (_) s => (ap) (var_Tm (nTm)) (EqTm s)
    | abs (_) s0 s1 => congr_abs ((fun x => (eq_refl) x) s0) ((extRen_Tm (upRen_Tm_Tm xiTm) (upRen_Tm_Tm zetaTm) (upExtRen_Tm_Tm (_) (_) EqTm)) s1)
    | app (_) s0 s1 => congr_app ((extRen_Tm xiTm zetaTm EqTm) s0) ((extRen_Tm xiTm zetaTm EqTm) s1)
    | unit (_)  => congr_unit 
    | seq (_) s0 s1 => congr_seq ((extRen_Tm xiTm zetaTm EqTm) s0) ((extRen_Tm xiTm zetaTm EqTm) s1)
    | inl (_) s0 => congr_inl ((extRen_Tm xiTm zetaTm EqTm) s0)
    | inr (_) s0 => congr_inr ((extRen_Tm xiTm zetaTm EqTm) s0)
    | prod (_) s0 s1 => congr_prod ((extRen_Tm xiTm zetaTm EqTm) s0) ((extRen_Tm xiTm zetaTm EqTm) s1)
    | fst (_) s0 => congr_fst ((extRen_Tm xiTm zetaTm EqTm) s0)
    | snd (_) s0 => congr_snd ((extRen_Tm xiTm zetaTm EqTm) s0)
    | case (_) s0 s1 s2 s3 => congr_case ((fun x => (eq_refl) x) s0) ((extRen_Tm xiTm zetaTm EqTm) s1) ((extRen_Tm (upRen_Tm_Tm xiTm) (upRen_Tm_Tm zetaTm) (upExtRen_Tm_Tm (_) (_) EqTm)) s2) ((extRen_Tm (upRen_Tm_Tm xiTm) (upRen_Tm_Tm zetaTm) (upExtRen_Tm_Tm (_) (_) EqTm)) s3)
    | box (_) s0 s1 => congr_box ((fun x => (eq_refl) x) s0) ((extRen_Tm xiTm zetaTm EqTm) s1)
    | unbox (_) s0 s1 s2 => congr_unbox ((fun x => (eq_refl) x) s0) ((extRen_Tm xiTm zetaTm EqTm) s1) ((extRen_Tm (upRen_Tm_Tm xiTm) (upRen_Tm_Tm zetaTm) (upExtRen_Tm_Tm (_) (_) EqTm)) s2)
    end.

Definition upExt_Tm_Tm { m : nat } { nTm : nat } (sigma : (fin) (m) -> Tm (nTm)) (tau : (fin) (m) -> Tm (nTm)) (Eq : forall x, sigma x = tau x) : forall x, (up_Tm_Tm sigma) x = (up_Tm_Tm tau) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_Tm (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint ext_Tm { mTm : nat } { nTm : nat } (sigmaTm : (fin) (mTm) -> Tm (nTm)) (tauTm : (fin) (mTm) -> Tm (nTm)) (EqTm : forall x, sigmaTm x = tauTm x) (s : Tm (mTm)) : subst_Tm sigmaTm s = subst_Tm tauTm s :=
    match s return subst_Tm sigmaTm s = subst_Tm tauTm s with
    | var_Tm (_) s => EqTm s
    | abs (_) s0 s1 => congr_abs ((fun x => (eq_refl) x) s0) ((ext_Tm (up_Tm_Tm sigmaTm) (up_Tm_Tm tauTm) (upExt_Tm_Tm (_) (_) EqTm)) s1)
    | app (_) s0 s1 => congr_app ((ext_Tm sigmaTm tauTm EqTm) s0) ((ext_Tm sigmaTm tauTm EqTm) s1)
    | unit (_)  => congr_unit 
    | seq (_) s0 s1 => congr_seq ((ext_Tm sigmaTm tauTm EqTm) s0) ((ext_Tm sigmaTm tauTm EqTm) s1)
    | inl (_) s0 => congr_inl ((ext_Tm sigmaTm tauTm EqTm) s0)
    | inr (_) s0 => congr_inr ((ext_Tm sigmaTm tauTm EqTm) s0)
    | prod (_) s0 s1 => congr_prod ((ext_Tm sigmaTm tauTm EqTm) s0) ((ext_Tm sigmaTm tauTm EqTm) s1)
    | fst (_) s0 => congr_fst ((ext_Tm sigmaTm tauTm EqTm) s0)
    | snd (_) s0 => congr_snd ((ext_Tm sigmaTm tauTm EqTm) s0)
    | case (_) s0 s1 s2 s3 => congr_case ((fun x => (eq_refl) x) s0) ((ext_Tm sigmaTm tauTm EqTm) s1) ((ext_Tm (up_Tm_Tm sigmaTm) (up_Tm_Tm tauTm) (upExt_Tm_Tm (_) (_) EqTm)) s2) ((ext_Tm (up_Tm_Tm sigmaTm) (up_Tm_Tm tauTm) (upExt_Tm_Tm (_) (_) EqTm)) s3)
    | box (_) s0 s1 => congr_box ((fun x => (eq_refl) x) s0) ((ext_Tm sigmaTm tauTm EqTm) s1)
    | unbox (_) s0 s1 s2 => congr_unbox ((fun x => (eq_refl) x) s0) ((ext_Tm sigmaTm tauTm EqTm) s1) ((ext_Tm (up_Tm_Tm sigmaTm) (up_Tm_Tm tauTm) (upExt_Tm_Tm (_) (_) EqTm)) s2)
    end.

Definition up_ren_ren_Tm_Tm { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_Tm_Tm tau) (upRen_Tm_Tm xi)) x = (upRen_Tm_Tm theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_Tm { kTm : nat } { lTm : nat } { mTm : nat } (xiTm : (fin) (mTm) -> (fin) (kTm)) (zetaTm : (fin) (kTm) -> (fin) (lTm)) (rhoTm : (fin) (mTm) -> (fin) (lTm)) (EqTm : forall x, ((funcomp) zetaTm xiTm) x = rhoTm x) (s : Tm (mTm)) : ren_Tm zetaTm (ren_Tm xiTm s) = ren_Tm rhoTm s :=
    match s return ren_Tm zetaTm (ren_Tm xiTm s) = ren_Tm rhoTm s with
    | var_Tm (_) s => (ap) (var_Tm (lTm)) (EqTm s)
    | abs (_) s0 s1 => congr_abs ((fun x => (eq_refl) x) s0) ((compRenRen_Tm (upRen_Tm_Tm xiTm) (upRen_Tm_Tm zetaTm) (upRen_Tm_Tm rhoTm) (up_ren_ren (_) (_) (_) EqTm)) s1)
    | app (_) s0 s1 => congr_app ((compRenRen_Tm xiTm zetaTm rhoTm EqTm) s0) ((compRenRen_Tm xiTm zetaTm rhoTm EqTm) s1)
    | unit (_)  => congr_unit 
    | seq (_) s0 s1 => congr_seq ((compRenRen_Tm xiTm zetaTm rhoTm EqTm) s0) ((compRenRen_Tm xiTm zetaTm rhoTm EqTm) s1)
    | inl (_) s0 => congr_inl ((compRenRen_Tm xiTm zetaTm rhoTm EqTm) s0)
    | inr (_) s0 => congr_inr ((compRenRen_Tm xiTm zetaTm rhoTm EqTm) s0)
    | prod (_) s0 s1 => congr_prod ((compRenRen_Tm xiTm zetaTm rhoTm EqTm) s0) ((compRenRen_Tm xiTm zetaTm rhoTm EqTm) s1)
    | fst (_) s0 => congr_fst ((compRenRen_Tm xiTm zetaTm rhoTm EqTm) s0)
    | snd (_) s0 => congr_snd ((compRenRen_Tm xiTm zetaTm rhoTm EqTm) s0)
    | case (_) s0 s1 s2 s3 => congr_case ((fun x => (eq_refl) x) s0) ((compRenRen_Tm xiTm zetaTm rhoTm EqTm) s1) ((compRenRen_Tm (upRen_Tm_Tm xiTm) (upRen_Tm_Tm zetaTm) (upRen_Tm_Tm rhoTm) (up_ren_ren (_) (_) (_) EqTm)) s2) ((compRenRen_Tm (upRen_Tm_Tm xiTm) (upRen_Tm_Tm zetaTm) (upRen_Tm_Tm rhoTm) (up_ren_ren (_) (_) (_) EqTm)) s3)
    | box (_) s0 s1 => congr_box ((fun x => (eq_refl) x) s0) ((compRenRen_Tm xiTm zetaTm rhoTm EqTm) s1)
    | unbox (_) s0 s1 s2 => congr_unbox ((fun x => (eq_refl) x) s0) ((compRenRen_Tm xiTm zetaTm rhoTm EqTm) s1) ((compRenRen_Tm (upRen_Tm_Tm xiTm) (upRen_Tm_Tm zetaTm) (upRen_Tm_Tm rhoTm) (up_ren_ren (_) (_) (_) EqTm)) s2)
    end.

Definition up_ren_subst_Tm_Tm { k : nat } { l : nat } { mTm : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> Tm (mTm)) (theta : (fin) (k) -> Tm (mTm)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_Tm_Tm tau) (upRen_Tm_Tm xi)) x = (up_Tm_Tm theta) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_Tm (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint compRenSubst_Tm { kTm : nat } { lTm : nat } { mTm : nat } (xiTm : (fin) (mTm) -> (fin) (kTm)) (tauTm : (fin) (kTm) -> Tm (lTm)) (thetaTm : (fin) (mTm) -> Tm (lTm)) (EqTm : forall x, ((funcomp) tauTm xiTm) x = thetaTm x) (s : Tm (mTm)) : subst_Tm tauTm (ren_Tm xiTm s) = subst_Tm thetaTm s :=
    match s return subst_Tm tauTm (ren_Tm xiTm s) = subst_Tm thetaTm s with
    | var_Tm (_) s => EqTm s
    | abs (_) s0 s1 => congr_abs ((fun x => (eq_refl) x) s0) ((compRenSubst_Tm (upRen_Tm_Tm xiTm) (up_Tm_Tm tauTm) (up_Tm_Tm thetaTm) (up_ren_subst_Tm_Tm (_) (_) (_) EqTm)) s1)
    | app (_) s0 s1 => congr_app ((compRenSubst_Tm xiTm tauTm thetaTm EqTm) s0) ((compRenSubst_Tm xiTm tauTm thetaTm EqTm) s1)
    | unit (_)  => congr_unit 
    | seq (_) s0 s1 => congr_seq ((compRenSubst_Tm xiTm tauTm thetaTm EqTm) s0) ((compRenSubst_Tm xiTm tauTm thetaTm EqTm) s1)
    | inl (_) s0 => congr_inl ((compRenSubst_Tm xiTm tauTm thetaTm EqTm) s0)
    | inr (_) s0 => congr_inr ((compRenSubst_Tm xiTm tauTm thetaTm EqTm) s0)
    | prod (_) s0 s1 => congr_prod ((compRenSubst_Tm xiTm tauTm thetaTm EqTm) s0) ((compRenSubst_Tm xiTm tauTm thetaTm EqTm) s1)
    | fst (_) s0 => congr_fst ((compRenSubst_Tm xiTm tauTm thetaTm EqTm) s0)
    | snd (_) s0 => congr_snd ((compRenSubst_Tm xiTm tauTm thetaTm EqTm) s0)
    | case (_) s0 s1 s2 s3 => congr_case ((fun x => (eq_refl) x) s0) ((compRenSubst_Tm xiTm tauTm thetaTm EqTm) s1) ((compRenSubst_Tm (upRen_Tm_Tm xiTm) (up_Tm_Tm tauTm) (up_Tm_Tm thetaTm) (up_ren_subst_Tm_Tm (_) (_) (_) EqTm)) s2) ((compRenSubst_Tm (upRen_Tm_Tm xiTm) (up_Tm_Tm tauTm) (up_Tm_Tm thetaTm) (up_ren_subst_Tm_Tm (_) (_) (_) EqTm)) s3)
    | box (_) s0 s1 => congr_box ((fun x => (eq_refl) x) s0) ((compRenSubst_Tm xiTm tauTm thetaTm EqTm) s1)
    | unbox (_) s0 s1 s2 => congr_unbox ((fun x => (eq_refl) x) s0) ((compRenSubst_Tm xiTm tauTm thetaTm EqTm) s1) ((compRenSubst_Tm (upRen_Tm_Tm xiTm) (up_Tm_Tm tauTm) (up_Tm_Tm thetaTm) (up_ren_subst_Tm_Tm (_) (_) (_) EqTm)) s2)
    end.

Definition up_subst_ren_Tm_Tm { k : nat } { lTm : nat } { mTm : nat } (sigma : (fin) (k) -> Tm (lTm)) (zetaTm : (fin) (lTm) -> (fin) (mTm)) (theta : (fin) (k) -> Tm (mTm)) (Eq : forall x, ((funcomp) (ren_Tm zetaTm) sigma) x = theta x) : forall x, ((funcomp) (ren_Tm (upRen_Tm_Tm zetaTm)) (up_Tm_Tm sigma)) x = (up_Tm_Tm theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenRen_Tm (shift) (upRen_Tm_Tm zetaTm) ((funcomp) (shift) zetaTm) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_Tm zetaTm (shift) ((funcomp) (shift) zetaTm) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_Tm (shift)) (Eq fin_n)))
  | None  => eq_refl
  end.

Fixpoint compSubstRen_Tm { kTm : nat } { lTm : nat } { mTm : nat } (sigmaTm : (fin) (mTm) -> Tm (kTm)) (zetaTm : (fin) (kTm) -> (fin) (lTm)) (thetaTm : (fin) (mTm) -> Tm (lTm)) (EqTm : forall x, ((funcomp) (ren_Tm zetaTm) sigmaTm) x = thetaTm x) (s : Tm (mTm)) : ren_Tm zetaTm (subst_Tm sigmaTm s) = subst_Tm thetaTm s :=
    match s return ren_Tm zetaTm (subst_Tm sigmaTm s) = subst_Tm thetaTm s with
    | var_Tm (_) s => EqTm s
    | abs (_) s0 s1 => congr_abs ((fun x => (eq_refl) x) s0) ((compSubstRen_Tm (up_Tm_Tm sigmaTm) (upRen_Tm_Tm zetaTm) (up_Tm_Tm thetaTm) (up_subst_ren_Tm_Tm (_) (_) (_) EqTm)) s1)
    | app (_) s0 s1 => congr_app ((compSubstRen_Tm sigmaTm zetaTm thetaTm EqTm) s0) ((compSubstRen_Tm sigmaTm zetaTm thetaTm EqTm) s1)
    | unit (_)  => congr_unit 
    | seq (_) s0 s1 => congr_seq ((compSubstRen_Tm sigmaTm zetaTm thetaTm EqTm) s0) ((compSubstRen_Tm sigmaTm zetaTm thetaTm EqTm) s1)
    | inl (_) s0 => congr_inl ((compSubstRen_Tm sigmaTm zetaTm thetaTm EqTm) s0)
    | inr (_) s0 => congr_inr ((compSubstRen_Tm sigmaTm zetaTm thetaTm EqTm) s0)
    | prod (_) s0 s1 => congr_prod ((compSubstRen_Tm sigmaTm zetaTm thetaTm EqTm) s0) ((compSubstRen_Tm sigmaTm zetaTm thetaTm EqTm) s1)
    | fst (_) s0 => congr_fst ((compSubstRen_Tm sigmaTm zetaTm thetaTm EqTm) s0)
    | snd (_) s0 => congr_snd ((compSubstRen_Tm sigmaTm zetaTm thetaTm EqTm) s0)
    | case (_) s0 s1 s2 s3 => congr_case ((fun x => (eq_refl) x) s0) ((compSubstRen_Tm sigmaTm zetaTm thetaTm EqTm) s1) ((compSubstRen_Tm (up_Tm_Tm sigmaTm) (upRen_Tm_Tm zetaTm) (up_Tm_Tm thetaTm) (up_subst_ren_Tm_Tm (_) (_) (_) EqTm)) s2) ((compSubstRen_Tm (up_Tm_Tm sigmaTm) (upRen_Tm_Tm zetaTm) (up_Tm_Tm thetaTm) (up_subst_ren_Tm_Tm (_) (_) (_) EqTm)) s3)
    | box (_) s0 s1 => congr_box ((fun x => (eq_refl) x) s0) ((compSubstRen_Tm sigmaTm zetaTm thetaTm EqTm) s1)
    | unbox (_) s0 s1 s2 => congr_unbox ((fun x => (eq_refl) x) s0) ((compSubstRen_Tm sigmaTm zetaTm thetaTm EqTm) s1) ((compSubstRen_Tm (up_Tm_Tm sigmaTm) (upRen_Tm_Tm zetaTm) (up_Tm_Tm thetaTm) (up_subst_ren_Tm_Tm (_) (_) (_) EqTm)) s2)
    end.

Definition up_subst_subst_Tm_Tm { k : nat } { lTm : nat } { mTm : nat } (sigma : (fin) (k) -> Tm (lTm)) (tauTm : (fin) (lTm) -> Tm (mTm)) (theta : (fin) (k) -> Tm (mTm)) (Eq : forall x, ((funcomp) (subst_Tm tauTm) sigma) x = theta x) : forall x, ((funcomp) (subst_Tm (up_Tm_Tm tauTm)) (up_Tm_Tm sigma)) x = (up_Tm_Tm theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenSubst_Tm (shift) (up_Tm_Tm tauTm) ((funcomp) (up_Tm_Tm tauTm) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_Tm tauTm (shift) ((funcomp) (ren_Tm (shift)) tauTm) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_Tm (shift)) (Eq fin_n)))
  | None  => eq_refl
  end.

Fixpoint compSubstSubst_Tm { kTm : nat } { lTm : nat } { mTm : nat } (sigmaTm : (fin) (mTm) -> Tm (kTm)) (tauTm : (fin) (kTm) -> Tm (lTm)) (thetaTm : (fin) (mTm) -> Tm (lTm)) (EqTm : forall x, ((funcomp) (subst_Tm tauTm) sigmaTm) x = thetaTm x) (s : Tm (mTm)) : subst_Tm tauTm (subst_Tm sigmaTm s) = subst_Tm thetaTm s :=
    match s return subst_Tm tauTm (subst_Tm sigmaTm s) = subst_Tm thetaTm s with
    | var_Tm (_) s => EqTm s
    | abs (_) s0 s1 => congr_abs ((fun x => (eq_refl) x) s0) ((compSubstSubst_Tm (up_Tm_Tm sigmaTm) (up_Tm_Tm tauTm) (up_Tm_Tm thetaTm) (up_subst_subst_Tm_Tm (_) (_) (_) EqTm)) s1)
    | app (_) s0 s1 => congr_app ((compSubstSubst_Tm sigmaTm tauTm thetaTm EqTm) s0) ((compSubstSubst_Tm sigmaTm tauTm thetaTm EqTm) s1)
    | unit (_)  => congr_unit 
    | seq (_) s0 s1 => congr_seq ((compSubstSubst_Tm sigmaTm tauTm thetaTm EqTm) s0) ((compSubstSubst_Tm sigmaTm tauTm thetaTm EqTm) s1)
    | inl (_) s0 => congr_inl ((compSubstSubst_Tm sigmaTm tauTm thetaTm EqTm) s0)
    | inr (_) s0 => congr_inr ((compSubstSubst_Tm sigmaTm tauTm thetaTm EqTm) s0)
    | prod (_) s0 s1 => congr_prod ((compSubstSubst_Tm sigmaTm tauTm thetaTm EqTm) s0) ((compSubstSubst_Tm sigmaTm tauTm thetaTm EqTm) s1)
    | fst (_) s0 => congr_fst ((compSubstSubst_Tm sigmaTm tauTm thetaTm EqTm) s0)
    | snd (_) s0 => congr_snd ((compSubstSubst_Tm sigmaTm tauTm thetaTm EqTm) s0)
    | case (_) s0 s1 s2 s3 => congr_case ((fun x => (eq_refl) x) s0) ((compSubstSubst_Tm sigmaTm tauTm thetaTm EqTm) s1) ((compSubstSubst_Tm (up_Tm_Tm sigmaTm) (up_Tm_Tm tauTm) (up_Tm_Tm thetaTm) (up_subst_subst_Tm_Tm (_) (_) (_) EqTm)) s2) ((compSubstSubst_Tm (up_Tm_Tm sigmaTm) (up_Tm_Tm tauTm) (up_Tm_Tm thetaTm) (up_subst_subst_Tm_Tm (_) (_) (_) EqTm)) s3)
    | box (_) s0 s1 => congr_box ((fun x => (eq_refl) x) s0) ((compSubstSubst_Tm sigmaTm tauTm thetaTm EqTm) s1)
    | unbox (_) s0 s1 s2 => congr_unbox ((fun x => (eq_refl) x) s0) ((compSubstSubst_Tm sigmaTm tauTm thetaTm EqTm) s1) ((compSubstSubst_Tm (up_Tm_Tm sigmaTm) (up_Tm_Tm tauTm) (up_Tm_Tm thetaTm) (up_subst_subst_Tm_Tm (_) (_) (_) EqTm)) s2)
    end.

Definition rinstInst_up_Tm_Tm { m : nat } { nTm : nat } (xi : (fin) (m) -> (fin) (nTm)) (sigma : (fin) (m) -> Tm (nTm)) (Eq : forall x, ((funcomp) (var_Tm (nTm)) xi) x = sigma x) : forall x, ((funcomp) (var_Tm ((S) nTm)) (upRen_Tm_Tm xi)) x = (up_Tm_Tm sigma) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_Tm (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint rinst_inst_Tm { mTm : nat } { nTm : nat } (xiTm : (fin) (mTm) -> (fin) (nTm)) (sigmaTm : (fin) (mTm) -> Tm (nTm)) (EqTm : forall x, ((funcomp) (var_Tm (nTm)) xiTm) x = sigmaTm x) (s : Tm (mTm)) : ren_Tm xiTm s = subst_Tm sigmaTm s :=
    match s return ren_Tm xiTm s = subst_Tm sigmaTm s with
    | var_Tm (_) s => EqTm s
    | abs (_) s0 s1 => congr_abs ((fun x => (eq_refl) x) s0) ((rinst_inst_Tm (upRen_Tm_Tm xiTm) (up_Tm_Tm sigmaTm) (rinstInst_up_Tm_Tm (_) (_) EqTm)) s1)
    | app (_) s0 s1 => congr_app ((rinst_inst_Tm xiTm sigmaTm EqTm) s0) ((rinst_inst_Tm xiTm sigmaTm EqTm) s1)
    | unit (_)  => congr_unit 
    | seq (_) s0 s1 => congr_seq ((rinst_inst_Tm xiTm sigmaTm EqTm) s0) ((rinst_inst_Tm xiTm sigmaTm EqTm) s1)
    | inl (_) s0 => congr_inl ((rinst_inst_Tm xiTm sigmaTm EqTm) s0)
    | inr (_) s0 => congr_inr ((rinst_inst_Tm xiTm sigmaTm EqTm) s0)
    | prod (_) s0 s1 => congr_prod ((rinst_inst_Tm xiTm sigmaTm EqTm) s0) ((rinst_inst_Tm xiTm sigmaTm EqTm) s1)
    | fst (_) s0 => congr_fst ((rinst_inst_Tm xiTm sigmaTm EqTm) s0)
    | snd (_) s0 => congr_snd ((rinst_inst_Tm xiTm sigmaTm EqTm) s0)
    | case (_) s0 s1 s2 s3 => congr_case ((fun x => (eq_refl) x) s0) ((rinst_inst_Tm xiTm sigmaTm EqTm) s1) ((rinst_inst_Tm (upRen_Tm_Tm xiTm) (up_Tm_Tm sigmaTm) (rinstInst_up_Tm_Tm (_) (_) EqTm)) s2) ((rinst_inst_Tm (upRen_Tm_Tm xiTm) (up_Tm_Tm sigmaTm) (rinstInst_up_Tm_Tm (_) (_) EqTm)) s3)
    | box (_) s0 s1 => congr_box ((fun x => (eq_refl) x) s0) ((rinst_inst_Tm xiTm sigmaTm EqTm) s1)
    | unbox (_) s0 s1 s2 => congr_unbox ((fun x => (eq_refl) x) s0) ((rinst_inst_Tm xiTm sigmaTm EqTm) s1) ((rinst_inst_Tm (upRen_Tm_Tm xiTm) (up_Tm_Tm sigmaTm) (rinstInst_up_Tm_Tm (_) (_) EqTm)) s2)
    end.

Lemma rinstInst_Tm { mTm : nat } { nTm : nat } (xiTm : (fin) (mTm) -> (fin) (nTm)) : ren_Tm xiTm = subst_Tm ((funcomp) (var_Tm (nTm)) xiTm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_Tm xiTm (_) (fun n => eq_refl) x)). Qed.

Lemma instId_Tm { mTm : nat } : subst_Tm (var_Tm (mTm)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_Tm (var_Tm (mTm)) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_Tm { mTm : nat } : @ren_Tm (mTm) (mTm) (id) = id .
Proof. exact ((eq_trans) (rinstInst_Tm ((id) (_))) instId_Tm). Qed.

Lemma varL_Tm { mTm : nat } { nTm : nat } (sigmaTm : (fin) (mTm) -> Tm (nTm)) : (funcomp) (subst_Tm sigmaTm) (var_Tm (mTm)) = sigmaTm .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_Tm { mTm : nat } { nTm : nat } (xiTm : (fin) (mTm) -> (fin) (nTm)) : (funcomp) (ren_Tm xiTm) (var_Tm (mTm)) = (funcomp) (var_Tm (nTm)) xiTm .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_Tm { kTm : nat } { lTm : nat } { mTm : nat } (sigmaTm : (fin) (mTm) -> Tm (kTm)) (tauTm : (fin) (kTm) -> Tm (lTm)) (s : Tm (mTm)) : subst_Tm tauTm (subst_Tm sigmaTm s) = subst_Tm ((funcomp) (subst_Tm tauTm) sigmaTm) s .
Proof. exact (compSubstSubst_Tm sigmaTm tauTm (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_Tm { kTm : nat } { lTm : nat } { mTm : nat } (sigmaTm : (fin) (mTm) -> Tm (kTm)) (tauTm : (fin) (kTm) -> Tm (lTm)) : (funcomp) (subst_Tm tauTm) (subst_Tm sigmaTm) = subst_Tm ((funcomp) (subst_Tm tauTm) sigmaTm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_Tm sigmaTm tauTm n)). Qed.

Lemma compRen_Tm { kTm : nat } { lTm : nat } { mTm : nat } (sigmaTm : (fin) (mTm) -> Tm (kTm)) (zetaTm : (fin) (kTm) -> (fin) (lTm)) (s : Tm (mTm)) : ren_Tm zetaTm (subst_Tm sigmaTm s) = subst_Tm ((funcomp) (ren_Tm zetaTm) sigmaTm) s .
Proof. exact (compSubstRen_Tm sigmaTm zetaTm (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_Tm { kTm : nat } { lTm : nat } { mTm : nat } (sigmaTm : (fin) (mTm) -> Tm (kTm)) (zetaTm : (fin) (kTm) -> (fin) (lTm)) : (funcomp) (ren_Tm zetaTm) (subst_Tm sigmaTm) = subst_Tm ((funcomp) (ren_Tm zetaTm) sigmaTm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_Tm sigmaTm zetaTm n)). Qed.

Lemma renComp_Tm { kTm : nat } { lTm : nat } { mTm : nat } (xiTm : (fin) (mTm) -> (fin) (kTm)) (tauTm : (fin) (kTm) -> Tm (lTm)) (s : Tm (mTm)) : subst_Tm tauTm (ren_Tm xiTm s) = subst_Tm ((funcomp) tauTm xiTm) s .
Proof. exact (compRenSubst_Tm xiTm tauTm (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_Tm { kTm : nat } { lTm : nat } { mTm : nat } (xiTm : (fin) (mTm) -> (fin) (kTm)) (tauTm : (fin) (kTm) -> Tm (lTm)) : (funcomp) (subst_Tm tauTm) (ren_Tm xiTm) = subst_Tm ((funcomp) tauTm xiTm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_Tm xiTm tauTm n)). Qed.

Lemma renRen_Tm { kTm : nat } { lTm : nat } { mTm : nat } (xiTm : (fin) (mTm) -> (fin) (kTm)) (zetaTm : (fin) (kTm) -> (fin) (lTm)) (s : Tm (mTm)) : ren_Tm zetaTm (ren_Tm xiTm s) = ren_Tm ((funcomp) zetaTm xiTm) s .
Proof. exact (compRenRen_Tm xiTm zetaTm (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_Tm { kTm : nat } { lTm : nat } { mTm : nat } (xiTm : (fin) (mTm) -> (fin) (kTm)) (zetaTm : (fin) (kTm) -> (fin) (lTm)) : (funcomp) (ren_Tm zetaTm) (ren_Tm xiTm) = ren_Tm ((funcomp) zetaTm xiTm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_Tm xiTm zetaTm n)). Qed.

End Tm.

Section Ty.
Inductive Ty  : Type :=
  | Unit : Ty 
  | Sum : Ty   -> Ty   -> Ty 
  | With : Ty   -> Ty   -> Ty 
  | Abs : Q   -> Ty   -> Ty   -> Ty 
  | Box : Q   -> Ty   -> Ty .

Lemma congr_Unit  : Unit  = Unit  .
Proof. congruence. Qed.

Lemma congr_Sum  { s0 : Ty   } { s1 : Ty   } { t0 : Ty   } { t1 : Ty   } (H1 : s0 = t0) (H2 : s1 = t1) : Sum s0 s1 = Sum t0 t1 .
Proof. congruence. Qed.

Lemma congr_With  { s0 : Ty   } { s1 : Ty   } { t0 : Ty   } { t1 : Ty   } (H1 : s0 = t0) (H2 : s1 = t1) : With s0 s1 = With t0 t1 .
Proof. congruence. Qed.

Lemma congr_Abs  { s0 : Q   } { s1 : Ty   } { s2 : Ty   } { t0 : Q   } { t1 : Ty   } { t2 : Ty   } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : Abs s0 s1 s2 = Abs t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_Box  { s0 : Q   } { s1 : Ty   } { t0 : Q   } { t1 : Ty   } (H1 : s0 = t0) (H2 : s1 = t1) : Box s0 s1 = Box t0 t1 .
Proof. congruence. Qed.

End Ty.

Arguments var_Tm {nTm}.

Arguments abs {nTm}.

Arguments app {nTm}.

Arguments unit {nTm}.

Arguments seq {nTm}.

Arguments inl {nTm}.

Arguments inr {nTm}.

Arguments prod {nTm}.

Arguments fst {nTm}.

Arguments snd {nTm}.

Arguments case {nTm}.

Arguments box {nTm}.

Arguments unbox {nTm}.

Global Instance Subst_Tm { mTm : nat } { nTm : nat } : Subst1 ((fin) (mTm) -> Tm (nTm)) (Tm (mTm)) (Tm (nTm)) := @subst_Tm (mTm) (nTm) .

Global Instance Ren_Tm { mTm : nat } { nTm : nat } : Ren1 ((fin) (mTm) -> (fin) (nTm)) (Tm (mTm)) (Tm (nTm)) := @ren_Tm (mTm) (nTm) .

Global Instance VarInstance_Tm { mTm : nat } : Var ((fin) (mTm)) (Tm (mTm)) := @var_Tm (mTm) .

Notation "x '__Tm'" := (var_Tm x) (at level 5, format "x __Tm") : subst_scope.

Notation "x '__Tm'" := (@ids (_) (_) VarInstance_Tm x) (at level 5, only printing, format "x __Tm") : subst_scope.

Notation "'var'" := (var_Tm) (only printing, at level 1) : subst_scope.

Class Up_Tm X Y := up_Tm : X -> Y.

Notation "↑__Tm" := (up_Tm) (only printing) : subst_scope.

Notation "↑__Tm" := (up_Tm_Tm) (only printing) : subst_scope.

Global Instance Up_Tm_Tm { m : nat } { nTm : nat } : Up_Tm (_) (_) := @up_Tm_Tm (m) (nTm) .

Notation "s [ sigmaTm ]" := (subst_Tm sigmaTm s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaTm ]" := (subst_Tm sigmaTm) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xiTm ⟩" := (ren_Tm xiTm s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xiTm ⟩" := (ren_Tm xiTm) (at level 1, left associativity, only printing) : fscope.

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_Tm,  Ren_Tm,  VarInstance_Tm.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_Tm,  Ren_Tm,  VarInstance_Tm in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_Tm| progress rewrite ?compComp_Tm| progress rewrite ?compComp'_Tm| progress rewrite ?rinstId_Tm| progress rewrite ?compRen_Tm| progress rewrite ?compRen'_Tm| progress rewrite ?renComp_Tm| progress rewrite ?renComp'_Tm| progress rewrite ?renRen_Tm| progress rewrite ?renRen'_Tm| progress rewrite ?varL_Tm| progress rewrite ?varLRen_Tm| progress (unfold up_ren, upRen_Tm_Tm, up_Tm_Tm)| progress (cbn [subst_Tm ren_Tm])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_Tm in *| progress rewrite ?compComp_Tm in *| progress rewrite ?compComp'_Tm in *| progress rewrite ?rinstId_Tm in *| progress rewrite ?compRen_Tm in *| progress rewrite ?compRen'_Tm in *| progress rewrite ?renComp_Tm in *| progress rewrite ?renComp'_Tm in *| progress rewrite ?renRen_Tm in *| progress rewrite ?renRen'_Tm in *| progress rewrite ?varL_Tm in *| progress rewrite ?varLRen_Tm in *| progress (unfold up_ren, upRen_Tm_Tm, up_Tm_Tm in *)| progress (cbn [subst_Tm ren_Tm] in *)| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_Tm).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_Tm).

