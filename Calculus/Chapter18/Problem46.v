From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_46_a : ∀ f,
  f <> (λ _, 0) -> ⟦ der ⟧ f = f -> ∀ x, f x <> 0.
Abort.

Lemma lemma_18_46_b :
  (∃ f, f <> (λ _, 0) /\ ⟦ der ⟧ f = f) ->
  ∃ f, ⟦ der ⟧ f = f /\ f 0 = 1.
Abort.

Lemma lemma_18_46_c : ∀ f,
  ⟦ der ⟧ f = f -> f 0 = 1 -> ∀ x y, f (x+y) = f x * f y.
Abort.

Lemma lemma_18_46_d : ∀ f,
  ⟦ der ⟧ f = f -> f 0 = 1 ->
  injective f /\ ∃ g, inverse_on f g ℝ (0, ∞) /\
  ⟦ der ⟧ g (0, ∞) = (λ x, 1/x).
Abort.
