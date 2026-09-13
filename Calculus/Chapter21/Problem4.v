From Calculus.Chapter21 Require Import Prelude.

Definition liouville_number (α : R) : Prop :=
  ∀ n : nat, ∃ p q : Z, (q > 1)%Z /\ 0 < |α - p / q| < 1 / (q) ^ n.

Lemma lemma_21_4 : ∃ α : R, liouville_number α /\ transcendental α.
Abort.
