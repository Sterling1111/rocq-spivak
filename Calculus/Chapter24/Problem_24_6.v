From Calculus.Chapter24 Require Import Prelude.

Definition f_6 (x : R) := if Req_dec_T x 0 then 1 else sin x / x.

Lemma lemma_24_6_even : forall n : nat,
  ⟦ Der^(2 * n) 0 ⟧ f_6 = (-1) ^ n / INR (2 * n + 1).
Admitted.

Lemma lemma_24_6_odd : forall n : nat,
  ⟦ Der^(2 * n + 1) 0 ⟧ f_6 = 0.
Admitted.
