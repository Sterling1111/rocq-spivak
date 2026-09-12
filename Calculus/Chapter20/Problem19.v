From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_19_term : ∀ f k x,
  nth_differentiable (S k) f ->
  ⟦ der ⟧ (λ t, ⟦ Der ^ k t ⟧ f / (fact k) * (x-t)^k) =
    (λ t, - (⟦ Der ^ k t ⟧ f / (fact k)) * k * (x-t)^(k-1) +
      ⟦ Der ^ (S k) t ⟧ f / (fact k) * (x-t)^k).
Abort.
Lemma lemma_20_19_a_derivative : ∀ f n x,
  nth_differentiable (S n) f ->
  ⟦ der ⟧ (λ t, R(n,t,f) x) =
    (λ t, - (⟦ Der ^ (S n) t ⟧ f / (fact n)) * (x-t)^n).
Abort.
Lemma lemma_20_19_a : ∀ f n a x δ,
  a < x -> δ > 0 -> nth_differentiable_on (S n) f (a-δ,x+δ) ->
  ∃ t, a < t < x /\ R(n,a,f) x = ⟦ Der ^ (S n) t ⟧ f / (fact (S n)) * (x-a)^(S n).
Abort.
Lemma lemma_20_19_b : ∀ f n a x δ,
  a < x -> δ > 0 -> nth_differentiable_on (S n) f (a-δ,x+δ) ->
  ∃ t, a < t < x /\ R(n,a,f) x = ⟦ Der ^ (S n) t ⟧ f / (fact n) * (x-t)^n * (x-a).
Abort.
