From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_13_a : forall f n,
  (n > 1)%nat ->
  increasing_on f (fun x => 1 <= x) ->
  (sum_f 1 (n - 1)%nat (fun k => f (INR k))) < (∫ 1 (INR n) f) /\ (∫ 1 (INR n) f) < (sum_f 2 n (fun k => f (INR k))).
Admitted.

Lemma lemma_22_13_b : forall n,
  (n > 0)%nat ->
  INR n ^ n / exp (INR (n - 1)) < INR (fact n) < INR (n + 1) ^ (n + 1) / exp (INR n) /\
  ⟦ lim ⟧ (fun n => exp ((1 / INR n) * log (INR (fact n))) / INR n) = 1 / exp 1.
Admitted.
