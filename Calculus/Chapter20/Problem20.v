From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_20 : ∀ f n a x δ,
  a < x -> δ > 0 -> nth_differentiable_on (S n) f (a-δ,x+δ) ->
  continuous_on (λ t, ⟦ Der ^ (S n) t ⟧ f) [a,x] ->
  R(n,a,f) x = ∫ a x (λ t, ⟦ Der ^ (S n) t ⟧ f / (fact n) * (x-t)^n) /\
  (∃ t, a < t < x /\ R(n,a,f) x = ⟦ Der ^ (S n) t ⟧ f / (fact n) * (x-t)^n * (x-a)) /\
  (∃ t, a < t < x /\ R(n,a,f) x = ⟦ Der ^ (S n) t ⟧ f / (fact (S n)) * (x-a)^(S n)).
Abort.
