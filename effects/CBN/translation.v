Require Export effects.CBN.typing effects.CBPV.typing effects.CBPV.renaming.
From Coq Require Import FunctionalExtensionality.

Fixpoint translateType (T : Ty) : CompTy :=
    match T with
    | Unit => CF VUnit
    | Sum T1 T2 =>
        CF (VSum
                (VThunk ϵ (translateType T1))
                (VThunk ϵ (translateType T2)))
    | Abs T1 T2 =>
        CAbs
            (VThunk ϵ (translateType T1))
            (translateType T2)
    | With T1 T2 =>
        CPair (translateType T1) (translateType T2)
    | Mon ϕ T => CF (VThunk ϕ (CF (VThunk ϵ (translateType T))))
    end.

Definition translateContext {n} (Γ : contextL n) : context n :=
    fun (i : fin n) => VThunk ϵ (translateType (Γ i)).

Lemma contextTransReverse : forall n (Γ : contextL n) (i : fin n),
    VThunk ϵ (translateType (Γ i)) = (translateContext Γ) i.
Proof. auto. Qed.

Lemma contextTranslationHom : forall n (Γ : contextL n) T,
    translateContext (T .: Γ) = VThunk ϵ (translateType T) .: translateContext Γ.
Proof.
    induction n;
    intros Γ T; apply functional_extensionality;
        intros i; unfold translateContext;
        destruct i; auto.
Qed.

Fixpoint translateTerm {n} (e0 : Tm n) : Comp n :=
    match e0 with
    | var_Tm i => cForce (var_Val i)
    | abs e => cAbs (translateTerm e)
    | syntax.app e1 e2 =>
        cApp (translateTerm e1) (vThunk (translateTerm e2))
    | unit => cRet vUnit
    | syntax.seq e1 e2 =>
        cLet
            (translateTerm e1)
            (cSeq (var_Val var_zero) ((ren_Comp shift) (translateTerm e2)))
    | prod e1 e2 =>
        cPair (translateTerm e1) (translateTerm e2)
    | fst e => cFst (translateTerm e)
    | snd e => cSnd (translateTerm e)
    | inl e => cRet (vInl (vThunk (translateTerm e)))
    | inr e => cRet (vInr (vThunk (translateTerm e)))
    | case e e1 e2 =>
        cLet (translateTerm e)
            (cCase (var_Val var_zero)
                ((ren_Comp up_ren') (translateTerm e1))
                ((ren_Comp up_ren') (translateTerm e2)))
    | ret e => cRet (vThunk (cRet (vThunk (translateTerm e))))
    | bind e1 e2 =>
        cRet (vThunk
        (cLet
            (cLet (translateTerm e1) (cForce (var_Val var_zero)))
            (cLet (translateTerm e2) (cForce (var_Val var_zero)))))
    | coerce e =>
        cRet (vThunk (cLet (translateTerm e) (cForce (var_Val var_zero))))
    | tickT => cRet (vThunk (cLet cTick (cRet (vThunk (cRet (var_Val var_zero))))))
    end.

Create HintDb trans.
#[export] Hint Resolve translateType
    translateTerm contextTransReverse
    contextTranslationHom : trans.
#[export] Hint Rewrite contextTransReverse
    contextTranslationHom : trans.
