From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_12_a : forall n : nat,
  (n > 0)%nat ->
  1 / INR (n + 1) < log (INR (n + 1)) - log (INR n) < 1 / INR n.
Abort.

Lemma lemma_22_12_b : forall a,
  (forall n, a n = ∑ 1 n (fun k => 1 / INR k) - log (INR n)) ->
  nonincreasing a /\ (forall n, a n >= 0).
Abort.
