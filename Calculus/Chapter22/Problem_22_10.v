From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_10_a : forall a,
  a > 1 -> limit_s_pinf (fun n => a ^ n).
Admitted.

Lemma lemma_22_10_b : forall a,
  0 < a < 1 -> ⟦ lim ⟧ (fun n => a ^ n) = 0.
Admitted.

Lemma lemma_22_10_c : forall a,
  a > 1 -> ⟦ lim ⟧ (fun n => exp ((1 / INR n) * log a)) = 1.
Admitted.

Lemma lemma_22_10_d : forall a,
  0 < a < 1 -> ⟦ lim ⟧ (fun n => exp ((1 / INR n) * log a)) = 1.
Admitted.

Lemma lemma_22_10_e : ⟦ lim ⟧ (fun n => exp ((1 / INR n) * log (INR n))) = 1.
Admitted.
