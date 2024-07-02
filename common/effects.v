Set Implicit Arguments.
Require Import Psatz Logic List Classes.Morphisms.
Import List Notations.

Parameter E : Type.

Parameter ϵ : E. (* effect identity (no effect) *)
Parameter tick : E. (* specific effect discussed in this paper *)
Parameter add : E -> E -> E.

Notation "ϕ1 'E+' ϕ2" := (add ϕ1 ϕ2) (at level 60).

(* Monoid laws *)

Parameter eff_idL : forall {ϕ}, ϵ E+ ϕ = ϕ.
Parameter eff_idR : forall {ϕ}, ϕ E+ ϵ = ϕ.
Parameter eff_assoc : forall {ϕ1 ϕ2 ϕ3}, (ϕ1 E+ ϕ2) E+ ϕ3 = ϕ1 E+ (ϕ2 E+ ϕ3).

Create HintDb effects.
#[export] Hint Resolve eff_idL eff_idR eff_assoc : effects.
#[export] Hint Rewrite @eff_idL @eff_idR @eff_assoc : effects.

(* Preordered monoid: preorder compatible with add *)

Inductive subeff : E -> E -> Prop :=
  | subeff_refl ϕ : subeff ϕ ϕ
  | subeff_trans ϕ1 ϕ2 ϕ3 :
    subeff ϕ1 ϕ2 -> subeff ϕ2 ϕ3 -> subeff ϕ1 ϕ3
  | subeff_add_right_compatible ϕ1 ϕ2 ϕ :
    subeff ϕ1 ϕ2 -> subeff (ϕ1 E+ ϕ) (ϕ2 E+ ϕ)
  | subeff_add_left_compatible ϕ1 ϕ2 ϕ :
    subeff ϕ1 ϕ2 -> subeff (ϕ E+ ϕ1) (ϕ E+ ϕ2).

Notation "ϕ1 'E<=' ϕ2" := (subeff ϕ1 ϕ2) (at level 70).

#[export] Hint Constructors subeff : effects.


Theorem subeff_addright : forall {ϕ1 ϕ2}, ϵ E<= ϕ2 -> ϕ1 E<= ϕ1 E+ ϕ2.
Proof.
  intros. rewrite <- eff_idR at 1. eauto with effects.
Qed.

Theorem subeff_addleft : forall {ϕ1 ϕ2}, ϵ E<= ϕ2 -> ϕ1 E<= ϕ2 E+ ϕ1.
Proof.
  intros. rewrite <- eff_idL at 1. eauto with effects.
Qed.

Theorem subeff_addright_invert : forall {ϕ ϕ1 ϕ2},
    ϕ1 E+ ϕ E<= ϕ2 -> ϵ E<= ϕ -> ϕ1 E<= ϕ2.
Proof.
  intros. rewrite <- eff_idR. eauto with effects.
Qed.


#[export] Hint Resolve subeff_addright subeff_addleft subeff_addright_invert : effects.

