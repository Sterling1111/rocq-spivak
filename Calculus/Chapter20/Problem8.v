From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_8_a : forall n x,
  P(4 * n + 2, 0, fun x => sin (x^2)) x = sum_f_R0 (fun k => (-1)^k / INR (fact (2 * k + 1)) * x^(4 * k + 2)) n.
Abort.

Lemma lemma_20_8_b : forall x,
  ⟦ Der ^ 11 0 ⟧ (fun x => sin (x^2)) = 0 /\
  ⟦ Der ^ 13 0 ⟧ (fun x => sin (x^2)) = 0 /\
  ⟦ Der ^ 10 0 ⟧ (fun x => sin (x^2)) = fact 10 / fact 5 /\
  ⟦ Der ^ 14 0 ⟧ (fun x => sin (x^2)) = - fact 14 / fact 7.
Abort.
