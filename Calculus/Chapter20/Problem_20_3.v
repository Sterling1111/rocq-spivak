From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_3_i : exists n,
  Rabs (sin 1 - sum_f_R0 (fun k => (-1)^k / INR (fact (2*k + 1))) n) < 10^(-17).
Admitted.

Lemma lemma_20_3_ii : exists n,
  Rabs (exp 2 - sum_f_R0 (fun k => 2^k / INR (fact k)) n) < 10^(-5).
Admitted.

Lemma lemma_20_3_iii : exists n,
  Rabs (cos (1/10) - sum_f_R0 (fun k => (-1)^k / INR (fact (2*k)) * (1/10)^(2*k)) n) < 10^(-4).
Admitted.
