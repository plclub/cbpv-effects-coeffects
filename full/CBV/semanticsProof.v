Require Import full.CBPV.semrenaming.
Require Import full.CBPV.semantics.
Require Import full.CBV.translation.
Require Export full.CBV.semantics.

(* This file shows that the translations are also semantics preserving *)

Fixpoint translateVClos (v : CBV.VClos) : VClos :=
    let translateEnv {n} (ρ : CBV.env n) : (env n) := 
      fun x => translateVClos (ρ x) 
    in
    match v with 
    | CBV.VClosUnit => VClosUnit
    | CBV.VClosPair W1 W2 => VClosPair (translateVClos W1) (translateVClos W2)
    | CBV.VClosInl W => VClosInl (translateVClos W)
    | CBV.VClosInr W => VClosInr (translateVClos W)
    | CBV.VClosBox q W => VClosUnit
    | CBV.VClosRet W => VClosUnit
    | CBV.VClosAbs m γ q ρ e => VClosThunk m γ (translateEnv ρ) (cAbs q (translateTerm e))
  end.

Definition translateEnv {n} (ρ : CBV.env n) : (env n) := 
      fun x => translateVClos (ρ x) .

Definition translateCClos (v : CBV.VClos) : CClos :=
  match v with 
  | CBV.VClosAbs m γ q ρ e => CClosAbs m q γ (translateEnv ρ) (translateTerm e)
  | _ => CClosRet Qone (translateVClos v)
  end.


Lemma fw_simulation : 
  forall {n} ρ γ (e : Tm n) v ϕ, CBV.Eval γ ρ e v ϕ -> 
       EvalComp γ (translateEnv ρ) (translateTerm e) (CClosRet Qone (translateVClos v)) ϕ.
Proof.
  induction 1; subst.
  - eapply E_Ret; eauto using Qnontrivial.
    eapply E_Var; eauto. autorewrite with coeffects. auto.
  - eapply E_Ret; eauto using Qnontrivial.
    eapply E_Unit; eauto. autorewrite with coeffects. auto.
  - simpl.
    eapply E_LetRet; eauto; autorewrite with coeffects; eauto. 
    eapply E_Seq with (γ1 := Qone .: 0s) (γ2 := Qzero .: γ2); eauto.
    eapply E_Var; eauto. solve_js0.
Admitted.
    
(*         
Lemma bw_simulation : 
  (forall ρ V W, EvalVal ρ V W -> exists V1 ρ1 W1,  V = (translateTerm V) /\ ρ = trans
            Eval (translateEnv ρ 
*)
