From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_6_a_i : π/4 = arctan (1/2) + arctan (1/3).
Proof.
  apply problem_6_a.
Qed.

Lemma lemma_20_6_a_ii : π/4 = 4 * arctan (1/5) - arctan (1/239).
Proof.
  apply problem_6_b.
Qed.

Lemma lemma_20_6_b : 3.14159 < π < 3.14160.
Proof.
  pose proof π_bounds as H1. lra.
Qed.
