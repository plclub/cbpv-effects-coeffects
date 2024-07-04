Require Export full.CBPV.renaming.
Require Export full.CBV.typing.
From Coq Require Import FunctionalExtensionality.

Fixpoint translateType (T : Ty) : ValTy :=
    match T with
    | Unit => VUnit
    | Pair T1 T2 => VPair (translateType T1) (translateType T2)
    | Sum T1 T2 => VSum (translateType T1) (translateType T2)
    | Abs q T1 T2 =>
        VThunk ϵ (CAbs q (translateType T1) (CF Qone (translateType T2)))
    | Box q T => VThunk ϵ (CF q (translateType T))
    | Mon ϕ T => VThunk ϕ (CF Qone (translateType T))
    end.

Definition translateContext {n} (Γ : contextL n) : context n :=
    fun (i : fin n) => translateType (Γ i).

(* translation commutes with getting type from context *)
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
    | var_Tm i => cRet Qone (var_Val i)
    | abs q e => cRet Qone (vThunk (cAbs q (translateTerm e)))
    | app q e1 e2 => 
        cLet Qone
            (translateTerm e1)
            (cLet q
                ((ren_Comp shift) (translateTerm e2))
                (cApp
                    (cForce (var_Val (shift var_zero)))
                    (var_Val var_zero)))
    | unit => cRet Qone vUnit
    | seq e1 e2 =>
        cLet Qone
            (translateTerm e1)
            (cSeq (var_Val var_zero) ((ren_Comp shift) (translateTerm e2)))
    | pair e1 e2 =>
        cLet Qone
            (translateTerm e1)
            (cLet Qone
                ((ren_Comp shift) (translateTerm e2))
                (cRet Qone (vPair (var_Val (shift var_zero)) (var_Val var_zero))))
    | split q' e1 e2 => let q := q_or_1 q' in (*RESOURCE-SPECIFIC*)
        cLet q
            (translateTerm e1)
            (cSplit q (var_Val var_zero) ((ren_Comp up2_ren') (translateTerm e2)))
    | inl e => cLet Qone (translateTerm e) (cRet Qone (vInl (var_Val var_zero)))
    | inr e => cLet Qone (translateTerm e) (cRet Qone (vInr (var_Val var_zero)))
    | case q e e1 e2 =>
        cLet q
            (translateTerm e)
            (cCase q (var_Val var_zero)
                ((ren_Comp up_ren') (translateTerm e1))
                ((ren_Comp up_ren') (translateTerm e2)))
    | box q e =>
        let q' := q_or_1 q in (*RESOURCE-SPECIFIC*)
        cLet q (translateTerm e)
             (cRet Qone (vThunk (cRet q' (var_Val var_zero))))
    | unbox q e1 e2 => 
        cLet q
            (translateTerm e1)
            (cLet q
                    (cForce (var_Val var_zero))
                    ((ren_Comp up_ren') (translateTerm e2)))
    | ret e => cRet Qone (vThunk (translateTerm e))
    | bind q e1 e2 =>
        cRet Qone (vThunk
            (cLet q (cLet Qone (translateTerm e1) (cForce (var_Val var_zero)))
            (cLet Qone (translateTerm e2)
            (cForce (var_Val var_zero)))))
    | coerce e =>
        cRet Qone (vThunk (cLet Qone (translateTerm e) (cForce (var_Val var_zero))))
    | tickT => cRet Qone (vThunk (cLet Qone cTick (cRet Qone (var_Val var_zero))))
    end.

Create HintDb trans.
Hint Resolve translateType
    translateTerm contextTransReverse
    contextTranslationHom : trans.
#[export] Hint Rewrite contextTransReverse
    contextTranslationHom : trans.
