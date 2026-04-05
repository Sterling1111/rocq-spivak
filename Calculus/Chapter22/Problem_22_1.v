From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_1_i : ⟦ lim ⟧ (fun n => 0) = 0.
Admitted.

Lemma lemma_22_1_ii : ⟦ lim ⟧ (fun n => INR n / INR (n + 1)) = 1.
Admitted.

Lemma lemma_22_1_iii : ⟦ lim ⟧ (fun n => (INR n + 3) / (INR n ^ 3 + 4)) = 0.
Admitted.

Lemma lemma_22_1_iv : ⟦ lim ⟧ (fun n => INR (fact n) / (INR n ^ n)) = 0.
Admitted.

Lemma lemma_22_1_v : forall a, a > 0 -> ⟦ lim ⟧ (fun n => exp ((1 / INR n) * log a)) = 1.
Admitted.

Lemma lemma_22_1_vi : ⟦ lim ⟧ (fun n => exp ((1 / INR n) * log (INR n))) = 1.
Admitted.

Lemma lemma_22_1_vii : ⟦ lim ⟧ (fun n => exp ((1 / INR n) * log (INR n^2 + INR n))) = 1.
Admitted.

Lemma lemma_22_1_viii : forall a b, a >= 0 -> b >= 0 -> ⟦ lim ⟧ (fun n => exp ((1 / INR n) * log (a^n + b^n))) = Rmax a b.
Admitted.

Lemma lemma_22_1_ix : exists alpha, ⟦ lim ⟧ (fun n => INR (alpha n) / INR n) = 0.
Admitted.

Lemma lemma_22_1_x : forall p : nat, ⟦ lim ⟧ (fun n => (∑ 1 n (fun k => INR k ^ p)) / INR n ^ (S p)) = 1 / INR (S p).
Admitted.
