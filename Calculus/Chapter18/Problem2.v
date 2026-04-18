From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_1_a : forall f f',
  (forall x, f x > 0) ->
  ⟦ der ⟧ f = f' ->
  ⟦ der ⟧ (log ∘ f) = (f' / f).
Proof.
  auto_diff.
Qed.

Lemma lemma_18_2_b_i : ⟦ der ⟧ (fun x => (1 + x) * (1 + e^^(x^2))) (0, ∞) = (fun x => ((1 + x) * (1 + e^^(x^2))) * (1 / (1 + x) + (e^^(x^2) * (2 * x)) / (1 + e^^(x^2)))).
Proof.
  auto_diff.
Qed.

Lemma lemma_18_2_b_ii : ⟦ der ⟧ (fun x => ((3 - x)^^(1/3) * x^2) / ((1 - x) * (3 + x)^^(2/3))) (0, 1) = (fun x => (((3 - x)^^(1/3) * x^2) / ((1 - x) * (3 + x)^^(2/3))) * ((1 / 3) * (-1 / (3 - x)) + 2 * (1 / x) - (-1 / (1 - x)) - (2 / 3) * (1 / (3 + x)))).
Proof.
  auto_diff.
  admit.
  admit.
Abort.

Lemma lemma_18_2_b_iii : ⟦ der ⟧ (fun x => (sin x)^^(cos x) + (cos x)^^(sin x)) (0, π/2) = (fun x => (sin x)^^(cos x) * (- sin x * log (sin x) + cos x * (cos x / sin x)) + (cos x)^^(sin x) * (cos x * log (cos x) + sin x * (- sin x / cos x))).
Proof.
  pose proof π_pos.
  auto_diff.
  admit.
Abort.

Lemma lemma_18_2_b_iv : ⟦ der ⟧ (fun x => (e^^x - e^^(-x)) / (e^^(2*x) * (1 + x^3))) (0, ∞) = (fun x => ((e^^x - e^^(-x)) / (e^^(2*x) * (1 + x^3))) * ((e^^x - (e^^(-x) * -1)) / (e^^x - e^^(-x)) - (e^^(2*x) * 2) / e^^(2*x) - (3 * x^2) / (1 + x^3))).
Proof.
  auto_diff.
  admit.
Abort.