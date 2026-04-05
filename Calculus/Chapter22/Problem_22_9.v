From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_9_i :
  ⟦ lim ⟧ (fun n => (∑ 1 n (fun k => exp (INR k / INR n))) / INR n) = exp 1 - 1.
Admitted.

Lemma lemma_22_9_ii :
  ⟦ lim ⟧ (fun n => (sum_f 1 (2 * n)%nat (fun k => exp (INR k / INR n))) / INR n) = exp 2 - 1.
Admitted.

Lemma lemma_22_9_iii :
  ⟦ lim ⟧ (fun n => ∑ 1 n (fun k => 1 / INR (n + k)%nat)) = log 2.
Admitted.

Lemma lemma_22_9_iv :
  ⟦ lim ⟧ (fun n => ∑ 1 n (fun k => 1 / INR ((n + k)%nat ^ 2))) = 0.
Admitted.

Lemma lemma_22_9_v :
  ⟦ lim ⟧ (fun n => ∑ 1 n (fun k => INR n / INR ((n + k)%nat ^ 2))) = 1 / 2.
Admitted.

Lemma lemma_22_9_vi :
  ⟦ lim ⟧ (fun n => ∑ 1 n (fun k => INR n / INR (n^2 + k^2))) = π / 4.
Admitted.
