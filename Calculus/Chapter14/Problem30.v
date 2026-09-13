From Calculus.Chapter14 Require Import Prelude.
From Calculus.Chapter14 Require Import Problem28.
From Lib Require Import Exponential.

Lemma lemma_14_30_a : ∃ L1 L2,
  ⟦ lim 0⁺ ⟧ (λ ε, ∫ ε 1 (λ x, 1 / √x)) = L1 /\
  ⟦ lim ∞ ⟧ (λ N, ∫ 1 N (λ x, 1 / x^2)) = L2.
Proof.
  exists 2, 1. split.
  - replace 2 with (2 * √1) by (rewrite sqrt_1; lra).
    apply lemma_14_28_a. lra.
  - intros ε H1. exists (Rmax 1 (1 / ε)). intros N H2.
    assert (H3 : N > 1 /\ 0 < 1 / N < ε) by solve_R.
    assert (H4 : ∫ 1 N (λ x, 1 / x^2) = 1 - 1 / N).
    {
      replace (1 - 1 / N) with ((λ x, -1 / x) N - (λ x, -1 / x) 1) by (cbn beta; lra).
      apply FTC2 with (g := λ x, -1 / x); [lra | auto_cont | auto_diff].
    }
    rewrite H4. solve_R.
Qed.

Lemma lemma_14_30_b : ∀ r,
  ~ ((∃ L1, ⟦ lim 0⁺ ⟧ (λ ε, ∫ ε 1 (λ x, x ^^ r)) = L1) /\
     (∃ L2, ⟦ lim ∞ ⟧ (λ N, ∫ 1 N (λ x, x ^^ r)) = L2)).
Abort.
