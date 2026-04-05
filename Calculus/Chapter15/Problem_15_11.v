From Calculus.Chapter15 Require Import Prelude.

(* Problem 11: Product-to-sum formulas *)

Lemma lemma_15_11_a : forall m n x,
  sin (m * x) * sin (n * x) = 1/2 * (cos ((m - n) * x) - cos ((m + n) * x)).
Admitted.

Lemma lemma_15_11_b : forall m n x,
  sin (m * x) * cos (n * x) = 1/2 * (sin ((m + n) * x) + sin ((m - n) * x)).
Admitted.

Lemma lemma_15_11_c : forall m n x,
  cos (m * x) * cos (n * x) = 1/2 * (cos ((m + n) * x) + cos ((m - n) * x)).
Admitted.
