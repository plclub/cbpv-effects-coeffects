Require Import common.effects.

(* We need two axioms about effects: that ϵ is the unique minimal
   effect. *)

Axiom pure_bot : forall ϕ,  ϵ E<= ϕ.
Axiom pure_bot2 : forall ϕ,  ϕ E<= ϵ -> ϕ = ϵ.

#[export] Hint Resolve pure_bot : effects.
