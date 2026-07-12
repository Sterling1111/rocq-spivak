From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_32_a : ∀ a (n k : nat) x,
  x ≠ a ->
  ⟦ der ^ k x ⟧ (λ x, 1 / (x - a)^n) = (λ x, (-1)^k * ((n + k - 1)!) / ((n - 1)!) / (x - a)^(n + k)).
Proof.
  intros a n k x H1.
  induction k as [| k IH].
  - simpl. rewrite Nat.add_0_r, Rmult_1_l. solve_R. split; [apply INR_fact_neq_0 | apply pow_nonzero; lra ].
  -
Abort.

Lemma lemma_10_32_b : ∀ (k:nat) x,
  x ≠ 1 -> x ≠ -1 ->
  ⟦ der ^ k x ⟧ (λ y, 1 / (y^2 - 1)) = 
    (λ y, (-1)^k * INR (fact k) / 2 * (1 / (y - 1)^(S k) - 1 / (y + 1)^(S k))).
Abort.