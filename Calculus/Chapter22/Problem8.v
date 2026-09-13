From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_8 : ∀ x,
  ∃ g : sequence,
    (∀ n, ⟦ lim ⟧ (λ k, cos (n! * π * x) ^ (2 * k)) = g n) /\
    (rational x -> ⟦ lim ⟧ g = 1) /\
    (irrational x -> ⟦ lim ⟧ g = 0).
Abort.
