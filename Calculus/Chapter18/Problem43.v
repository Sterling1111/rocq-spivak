From Calculus.Chapter18 Require Import Prelude.

Section Uniqueness.
Variables f f' : R -> R.
Hypothesis Hder : ⟦ der ⟧ f = f'.
Hypothesis Hder2 : ⟦ der ⟧ f' = f.
Hypothesis Hzero : f 0 = 0.
Hypothesis Hzero' : f' 0 = 0.

Lemma lemma_18_43_a : ∀ x, (f x)^2 - (f' x)^2 = 0.
Abort.

Lemma lemma_18_43_b : ∀ a b, a < b ->
  (∀ x, a < x < b -> f x <> 0) ->
  (∃ c, ∀ x, a < x < b -> f x = c * exp x) \/
  (∃ c, ∀ x, a < x < b -> f x = c * exp (-x)).
Abort.

Lemma lemma_18_43_c_endpoint : ∀ x0, x0 > 0 -> f x0 <> 0 ->
  ∃ a, 0 <= a < x0 /\ f a = 0 /\ ∀ x, a < x < x0 -> f x <> 0.
Abort.

Lemma lemma_18_43_c : f = (λ _, 0).
Abort.

End Uniqueness.
