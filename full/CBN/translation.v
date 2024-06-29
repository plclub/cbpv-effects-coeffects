Require Export full.CBPV.renaming.
Require Export full.CBN.typing.
From Coq Require Import FunctionalExtensionality.

Fixpoint translateType (T : Ty) : CompTy :=
    match T with
    | Unit => CF Qone VUnit
    | Sum T1 T2 =>
        CF Qone
            (VSum
                (VThunk ϵ (translateType T1))
                (VThunk ϵ (translateType T2)))
    | Abs q T1 T2 =>
        CAbs q
            (VThunk ϵ (translateType T1))
            (translateType T2)
    | Box q T =>
        CF q (VThunk ϵ (translateType T))
    | With T1 T2 =>
        CPair (translateType T1) (translateType T2)
    | Mon ϕ T => CF Qone (VThunk ϕ (CF Qone (VThunk ϵ (translateType T))))
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
    | abs q e => cAbs q (translateTerm e)
    | app e1 e2 =>
        cApp (translateTerm e1) (vThunk (translateTerm e2))
    | unit => cRet Qone vUnit
    | seq e1 e2 =>
        cLet Qone
            (translateTerm e1)
            (cSeq (var_Val var_zero) ((ren_Comp shift) (translateTerm e2)))
    | prod e1 e2 =>
        cPair (translateTerm e1) (translateTerm e2)
    | fst e => cFst (translateTerm e)
    | snd e => cSnd (translateTerm e)
    | inl e => cRet Qone (vInl (vThunk (translateTerm e)))
    | inr e => cRet Qone (vInr (vThunk (translateTerm e)))
    | case q e e1 e2 =>
        cLet q (translateTerm e)
            (cCase q (var_Val var_zero)
                ((ren_Comp up_ren') (translateTerm e1))
                ((ren_Comp up_ren') (translateTerm e2)))
    | box q e => cRet q (vThunk (translateTerm e))
    | unbox q e1 e2 =>
        cLet q (translateTerm e1) (translateTerm e2)
    | ret e => cRet Qone (vThunk (cRet Qone (vThunk (translateTerm e))))
    | bind q' e1 e2 =>
        let q := q_or_1 q' in (* RESOURCE-SPECIFIC*)
        cRet Qone (vThunk
        (cLet q
            (cLet Qone (translateTerm e1) (cForce (var_Val var_zero)))
            (cLet Qone (translateTerm e2) (cForce (var_Val var_zero)))))
    | coerce e =>
        cRet Qone (vThunk (cLet Qone (translateTerm e) (cForce (var_Val var_zero))))
    | tickT => cRet Qone (vThunk (cLet Qone cTick (cRet Qone (vThunk (cRet Qone (var_Val var_zero))))))
    end.

Create HintDb trans.
#[export] Hint Resolve translateType
    translateTerm contextTransReverse
    contextTranslationHom : trans.
#[export] Hint Rewrite contextTransReverse
    contextTranslationHom : trans.
