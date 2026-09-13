From Calculus.Chapter15 Require Import Prelude.

Lemma lemma_15_33_a : ∀ k x,
  sin ((k + 1/2) * x) - sin ((k - 1/2) * x) = 2 * sin (x / 2) * cos (k * x).
Proof.
  intros k x. rewrite sum_to_product_sin_minus.
  replace (((k + 1 / 2) * x - (k - 1 / 2) * x) / 2) with (x / 2) by lra.
  replace (((k + 1 / 2) * x + (k - 1 / 2) * x) / 2) with (k * x) by lra.
  reflexivity.
Qed.

Lemma lemma_15_33_b : ∀ (n : nat) x,
  sin (x / 2) <> 0 ->
  1/2 + ∑ 1 n (λ (i : ℕ), cos (i * x)) = sin ((n + 1/2) * x) / (2 * sin (x / 2)).
Abort.

Lemma lemma_15_33_c : ∀ (n : nat) x,
  sin (x / 2) <> 0 ->
  ∑ 1 n (λ (i : ℕ), sin (i * x)) = sin ((n + 1) / 2 * x) * sin (n / 2 * x) / sin (x / 2).
Abort.
