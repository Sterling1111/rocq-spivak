From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_9_a : forall x,
  P(9, 0, fun x => exp ((x^2))) x = 1 + x^2 + x^4 / 2 + x^6 / 6 + x^8 / 24.
Abort.

Lemma lemma_20_9_b : forall x n,
  P(n, 0, fun x => exp ((x^2))) x = sum_f_R0 (fun k => 1 / INR (fact k) * x^(2 * k)) (n / 2)%nat.
Abort.

Lemma lemma_20_9_c : forall k,
  ⟦ Der ^ (2 * k) 0 ⟧ (fun x => exp ((x^2))) = INR (fact (2 * k)) / INR (fact k) /\
  ⟦ Der ^ (2 * k + 1) 0 ⟧ (fun x => exp ((x^2))) = 0.
Abort.
