From Calculus.Chapter23 Require Import Prelude.

Lemma problem_23_18 :
  ∃ f,
    continuous f /\ (∀ x, f x >= 0) /\
    improper_integrable_pinf 0 f /\
    ~ (∃ L, ⟦ lim ∞ ⟧ f = L).
Abort.
