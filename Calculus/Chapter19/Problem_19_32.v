From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_32_a : forall a,
  a > 0 ->
  ∫ 0 (2*π) (fun t => √((⟦ der ⟧ (fun t => a * (t - sin t)) t)^2 + (⟦ der ⟧ (fun t => a * (1 - cos t)) t)^2)) = 8 * a.
Admitted.

Lemma lemma_19_32_b : forall a,
  a > 0 ->
  ∫ 0 (2*π) (fun t => a * (1 - cos t) * ⟦ der ⟧ (fun t => a * (t - sin t)) t) = 3 * π * a^2.
Admitted.
