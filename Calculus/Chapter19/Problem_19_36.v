From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_36 : forall a_seq b_seq n,
  (n > 0)%nat ->
  sum_f_R0 (fun k => a_seq k * b_seq k) n =
  sum_f_R0 (fun k => (sum_f_R0 a_seq k) * (b_seq k - b_seq (k+1)%nat)) (n-1)%nat +
  (sum_f_R0 a_seq n) * b_seq n.
Admitted.
