From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_17_a : ∀ g g' a n M δ,
  δ > 0 -> M >= 0 -> ⟦ der ⟧ g (a-δ,a+δ) = g' ->
  (∀ x, |x-a| < δ -> |g' x| <= M * |x-a|^n) ->
  ∀ x, |x-a| < δ -> |g x - g a| <= M * |x-a|^(S n) / (S n).
Abort.
Lemma lemma_20_17_b : ∀ g g' a n δ,
  δ > 0 -> ⟦ der ⟧ g (a-δ,a+δ) = g' ->
  (⟦ lim a ⟧ (λ x, g' x / (x-a)^n) = 0) ->
  ⟦ lim a ⟧ (λ x, (g x - g a) / (x-a)^(S n)) = 0.
Abort.
Lemma lemma_20_17_c : ∀ f f' a n,
  (0 < n)%nat -> nth_differentiable n f -> ⟦ der ⟧ f = f' ->
  ⟦ der ⟧ (λ x, f x - P(n,a,f) x) = (λ x, f' x - P(n-1,a,f') x).
Abort.
Lemma lemma_20_17_d : ∀ n a f,
  (0 < n)%nat -> nth_differentiable_at n f a ->
  ⟦ lim a ⟧ (λ x, R(n,a,f) x / (x-a)^n) = 0.
Abort.
