From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_5_a : forall a,
  0 < a < 2 -> a < sqrt (2 * a) < 2.
Admitted.

Lemma lemma_22_5_b : exists L,
  ⟦ lim ⟧ (fun n => 2 - (1/2)^n) = L. (* dummy sequence formulation *)
Admitted.

Lemma lemma_22_5_c : exists L,
  L = 2.
Admitted.
