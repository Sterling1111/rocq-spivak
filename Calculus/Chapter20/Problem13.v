From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_13 : forall n x,
  P(4 * n + 2, 0, fun x => sin (x^2)) x = sum_f_R0 (fun k => (-1)^k / INR (fact (2 * k + 1)) * x^(4 * k + 2)) n.
Abort.
