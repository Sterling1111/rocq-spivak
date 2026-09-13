From Calculus.Chapter15 Require Import Prelude.

Lemma lemma_15_28_a : ∀ x,
  -1 < x < 1 ->
  let F := λ x, ∫ x 1 (λ t, 1 / √(1 - t^2)) in
  F x = ∫ x 1 (λ t, √(1 + ((⟦ Der t ⟧ (λ x, √(1 - x^2)))^2))).
Abort.

Lemma lemma_15_28_b : ∀ x,
  -1 < x < 1 ->
  let F := λ x, ∫ x 1 (λ t, 1 / √(1 - t^2)) in
  ⟦ der x ⟧ F = (λ x, -1 / √(1 - x^2)).
Abort.

Lemma lemma_15_28_c :
  ⟦ der ⟧ cos = (λ x, - sin x) /\
  ⟦ der ⟧ sin = cos.
Proof.
  split; auto_diff.
Qed.
