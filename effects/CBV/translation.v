Require Export effects.CBV.typing effects.CBPV.typing effects.CBPV.renaming.
From Coq Require Import FunctionalExtensionality.

Fixpoint translateType (T : Ty) : ValTy :=
    match T with
    | Unit => VUnit
    | Pair T1 T2 => VPair (translateType T1) (translateType T2)
    | Sum T1 T2 => VSum (translateType T1) (translateType T2)
    | Abs T1 T2 =>
        VThunk ϵ (CAbs (translateType T1) (CF (translateType T2)))
    | Mon ϕ T => VThunk ϕ (CF (translateType T))
    end.

Definition translateContext {n} (Γ : contextL n) : context n :=
    fun (i : fin n) => translateType (Γ i).

Lemma contextTransReverse : forall n (Γ : contextL n) (i : fin n),
    translateType (Γ i) = (translateContext Γ) i.
Proof. auto. Qed.

Lemma contextTranslationHom : forall n (Γ : contextL n) T,
    translateContext (T .: Γ) = translateType T .: translateContext Γ.
Proof.
    induction n;
    intros Γ T; apply functional_extensionality;
        intros i; unfold translateContext;
        destruct i; auto.
Qed.

Fixpoint translateTerm {n} (e0 : Tm n) : Comp n :=
     match e0 with
    | var_Tm i => cRet (var_Val i)
    | abs e => cRet (vThunk (cAbs (translateTerm e)))
    | syntax.app e1 e2 =>
        cLet
            (translateTerm e1)
            (cLet
                ((ren_Comp shift) (translateTerm e2))
                (cApp
                    (cForce (var_Val (shift var_zero)))
                    (var_Val var_zero)))
    | unit => cRet vUnit
    | syntax.seq e1 e2 =>
        cLet
            (translateTerm e1)
            (cSeq (var_Val var_zero) ((ren_Comp shift) (translateTerm e2)))
    | pair e1 e2 =>
        cLet
            (translateTerm e1)
            (cLet
                ((ren_Comp shift) (translateTerm e2))
                (cRet (vPair (var_Val (shift var_zero)) (var_Val var_zero))))
    | syntax.split e1 e2 =>
        cLet
            (translateTerm e1)
            (cSplit (var_Val var_zero) ((ren_Comp up2_ren') (translateTerm e2)))
    | inl e => cLet (translateTerm e) (cRet (vInl (var_Val var_zero)))
    | inr e => cLet (translateTerm e) (cRet (vInr (var_Val var_zero)))
    | case e e1 e2 =>
        cLet
            (translateTerm e)
            (cCase (var_Val var_zero)
                ((ren_Comp up_ren') (translateTerm e1))
                ((ren_Comp up_ren') (translateTerm e2)))
    | ret e => cRet (vThunk (translateTerm e))
    | bind e1 e2 =>
        cRet (vThunk
            (cLet (cLet (translateTerm e1) (cForce (var_Val var_zero)))
            (cLet (translateTerm e2)
            (cForce (var_Val var_zero)))))
    | coerce e =>
        cRet (vThunk (cLet (translateTerm e) (cForce (var_Val var_zero))))
    | tickT => cRet (vThunk (cLet cTick (cRet (var_Val var_zero))))
    end.

Create HintDb trans.
Hint Resolve translateType
    translateTerm contextTransReverse
    contextTranslationHom : trans.
#[export] Hint Rewrite contextTransReverse
    contextTranslationHom : trans.
