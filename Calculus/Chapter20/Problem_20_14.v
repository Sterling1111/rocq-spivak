From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_14 : forall n x,
  P(2*n + 1, 0, arctan) x = sum_f_R0 (fun k => (-1)^k / (2 * INR k + 1) * x^(2 * k + 1)) n.
Proof.
  intros n x.
Admitted.
