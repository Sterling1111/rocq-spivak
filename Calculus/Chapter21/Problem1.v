From Calculus.Chapter21 Require Import Prelude.

Lemma lemma_21_1_a : ∀ α,
  α > 0 -> algebraic α -> algebraic (√α).
Abort.

Lemma lemma_21_1_b : ∀ α r,
  algebraic α -> (∃ q : Q, r = (q : ℝ)) ->
  algebraic (α + r) /\ algebraic (α * r).
Abort.
