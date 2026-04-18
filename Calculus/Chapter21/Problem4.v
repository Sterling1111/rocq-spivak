From Calculus.Chapter21 Require Import Prelude.

(* Problem 4: Let α = 0.110001..., 1s at n! place. Prove α is transcendental. *)

Definition liouville_number (α : R) : Prop :=
  forall n : nat, exists p q : Z, (q > 1)%Z /\ 0 < |α - IZR p / IZR q| < 1 / (IZR q) ^ n.

Lemma lemma_21_4 : exists α : R, liouville_number α /\ transcendental α.
Abort.
