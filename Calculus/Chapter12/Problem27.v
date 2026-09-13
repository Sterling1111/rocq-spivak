From Calculus.Chapter12 Require Import Prelude.

Lemma lemma_12_27_a : ∀ f,
  (∀ x, f x > 0) ->
  decreasing f ->
  ∃ g, continuous g /\ decreasing g /\ ∀ x, 0 < g x <= f x.
Abort.

Lemma lemma_12_27_b : ∀ f,
  (∀ x, f x > 0) ->
  decreasing f ->
  ∃ g, continuous g /\ decreasing g /\ (∀ x, 0 < g x <= f x) /\ ⟦ lim ∞ ⟧ (λ x, g x / f x) = 0.
Abort.
