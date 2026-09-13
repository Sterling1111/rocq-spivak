From Calculus.Chapter3 Require Export Prelude.

Lemma lemma_3_19_a_i : 
  ~ ∃ f g : R -> R, ∀ x y, f x + g y = x * y.
Proof.
  intros [f [g H1]]. pose proof (H1 0 0). pose proof (H1 1 0).
  pose proof (H1 0 1). pose proof (H1 1 1). nra.
Qed.

Lemma lemma_3_19_a_ii : 
  ~ ∃ f g : R -> R, ∀ x y, f x * g y = x + y.
Proof.
  intros [f [g H1]]. pose proof (H1 0 0). pose proof (H1 1 0).
  pose proof (H1 0 1).
  assert (H5 : f 0 = 0 \/ g 0 = 0) by (apply Rmult_integral; nra). destruct H5; nra.
Qed.

Lemma lemma_3_19_b : ∃ f g : R -> R,
  ∀ x y, f (x + y) = g (x * y).
Proof.
  exists (λ _, 0), (λ _, 0). reflexivity.
Qed.
