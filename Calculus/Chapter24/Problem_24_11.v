From Calculus.Chapter24 Require Import Prelude.

Lemma lemma_24_11_a : forall a, a > 0 -> exists f,
  uniform_limit (fun N x => ∑ 1 N (fun n => INR n * x / (1 + INR n ^ 4 * x ^ 2))) f (fun x => x >= a).
Admitted.

Lemma lemma_24_11_b : forall f,
  ~ uniform_limit (fun N x => ∑ 1 N (fun n => INR n * x / (1 + INR n ^ 4 * x ^ 2))) f (Full_set R).
Admitted.

Lemma lemma_24_11_c : exists f,
  uniform_limit (fun N x => ∑ 1 N (fun n => INR n * x / (1 + INR n ^ 5 * x ^ 2))) f (Full_set R).
Admitted.
