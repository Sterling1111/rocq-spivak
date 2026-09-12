From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_2_a : ∀ f f',
  (∀ x, f x > 0) ->
  ⟦ der ⟧ f = f' ->
  ⟦ der ⟧ (log ∘ f) = (f' / f).
Proof.
  auto_diff.
Qed.

Lemma lemma_18_2_b_i : ⟦ der ⟧ (λ x, (1 + x) * (1 + e^^(x^2))) (0, ∞) = (λ x, ((1 + x) * (1 + e^^(x^2))) * (1 / (1 + x) + (e^^(x^2) * (2 * x)) / (1 + e^^(x^2)))).
Proof.
  auto_diff.
Qed.

Lemma lemma_18_2_b_ii : ⟦ der ⟧ (λ x, ((3 - x)^^(1/3) * x^2) / ((1 - x) * (3 + x)^^(2/3))) (0, 1) = (λ x, (((3 - x)^^(1/3) * x^2) / ((1 - x) * (3 + x)^^(2/3))) * ((1 / 3) * (-1 / (3 - x)) + 2 * (1 / x) - (-1 / (1 - x)) - (2 / 3) * (1 / (3 + x)))).
Proof.
  auto_diff.
  admit.
  admit.
Abort.

Lemma lemma_18_2_b_iii : ⟦ der ⟧ (λ x, (sin x)^^(cos x) + (cos x)^^(sin x)) (0, π/2) = (λ x, (sin x)^^(cos x) * (- sin x * log (sin x) + cos x * (cos x / sin x)) + (cos x)^^(sin x) * (cos x * log (cos x) + sin x * (- sin x / cos x))).
Proof.
  pose proof π_pos.
  auto_diff.
Qed.

Lemma lemma_18_2_b_iv : ⟦ der ⟧ (λ x, (e^^x - e^^(-x)) / (e^^(2*x) * (1 + x^3))) (0, ∞) = (λ x, ((e^^x - e^^(-x)) / (e^^(2*x) * (1 + x^3))) * ((e^^x - (e^^(-x) * -1)) / (e^^x - e^^(-x)) - (e^^(2*x) * 2) / e^^(2*x) - (3 * x^2) / (1 + x^3))).
Proof.
  auto_diff.
  admit.
Abort.