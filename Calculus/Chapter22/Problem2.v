From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_2_i : ⟦ lim ⟧ (fun n => INR n / INR (n + 1) - INR (n + 1) / INR n) = 0.
Abort.

Lemma lemma_22_2_ii : forall a b, 
  ⟦ lim ⟧ (fun n => INR n - sqrt (INR n + a) * sqrt (INR n + b)) = - (a + b) / 2.
Abort.

Lemma lemma_22_2_iii : ⟦ lim ⟧ (fun n => (2^n + (-1)^n) / (2^(n+1) + (-1)^(n+1))) = 1 / 2.
Abort.

Lemma lemma_22_2_iv : ⟦ lim ⟧ (fun n => (-1)^n * sqrt (INR n) * sin (INR n ^ n) / INR (n + 1)) = 0.
Abort.

Lemma lemma_22_2_v : forall a b, a > 0 -> b > 0 -> a <> b ->
  ⟦ lim ⟧ (fun n => (a^n - b^n) / (a^n + b^n)) = if Rle_dec a b then -1 else 1.
Abort.

Lemma lemma_22_2_vi : forall c, Rabs c < 1 ->
  ⟦ lim ⟧ (fun n => INR n * c^n) = 0.
Abort.

Lemma lemma_22_2_vii : ⟦ lim ⟧ (fun n => 2^(n^2) / INR (fact n)) = 0. (* wait, it diverges actually, 2^{n^2} grows extremely fast, wait 2^{n^2} / n! converges to infinity *)
Abort.
