From Calculus.Chapter22 Require Import Prelude.

From Calculus.Chapter21 Require Import Prelude.

Lemma lemma_22_33_a : ∀ f ε,
  (∀ a, a ∈ [0, 1] -> ∃ L, ⟦ lim a ⟧ f [0, 1] = L) ->
  ε > 0 ->
  Finite_set (λ a, a ∈ [0, 1] /\
    ∃ L, ⟦ lim a ⟧ f [0, 1] = L /\ |L - f a| > ε).
Abort.

Lemma lemma_22_33_b : ∀ f,
  (∀ a, a ∈ [0, 1] -> ∃ L, ⟦ lim a ⟧ f [0, 1] = L) ->
  countable (λ a, a ∈ [0, 1] /\ ~ (⟦ lim a ⟧ f [0, 1] = f a)).
Abort.
