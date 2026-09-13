From Calculus.Chapter24 Require Import Prelude.

Definition f_6 (x : R) := if Req_dec_T x 0 then 1 else sin x / x.

Lemma lemma_24_6_even : ∀ n : nat,
  ⟦ Der^(2 * n) 0 ⟧ f_6 = (-1) ^ n / (2 * n + 1)%nat.
Abort.

Lemma lemma_24_6_odd : ∀ n : nat,
  ⟦ Der^(2 * n + 1) 0 ⟧ f_6 = 0.
Abort.
