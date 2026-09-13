From Calculus.Chapter4 Require Import Prelude.

Lemma lemma_4_7_a :
  ∀ A B C : ℝ, A <> 0 \/ B <> 0 -> straight_line (line_equation A B C).
Abort.

Lemma lemma_4_7_b :
  ∀ L, straight_line L -> ∃ A B C : ℝ, (A <> 0 \/ B <> 0) /\ L = line_equation A B C.
Abort.
