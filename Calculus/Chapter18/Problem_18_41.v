From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_41 : forall x n,
  x > 0 ->
  exp x = sum_f_R0 (fun k => x^k / INR (fact k)) n + exp x * x^(n+1) / INR (fact (n+1)).
Admitted.
