From Calculus.Chapter7 Require Import Prelude.

Lemma lemma_7_6 : ∀ f,
  continuous_on f [-1, 1] ->
  (∀ x, x ∈ [-1, 1] -> x^2 + (f x)^2 = 1) ->
  (∀ x, x ∈ [-1, 1] -> f x = √(1 - x^2)) \/
  (∀ x, x ∈ [-1, 1] -> f x = -√(1 - x^2)).
Proof.
  intros f H1 H2. 
Admitted.