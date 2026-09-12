From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_13_a : ∀ a, 0 < a < 1 ->
  ⟦ lim ∞ ⟧ (λ x, a ^^ x) = 0.
Proof.
Abort.

Lemma lemma_18_13_b : ∀ n : nat,
  ⟦ lim ∞ ⟧ (λ x, x / (log x) ^ n) = ∞.
Proof.
Abort.

Lemma lemma_18_13_c : ∀ n : nat,
  ⟦ lim ∞ ⟧ (λ x, (log x) ^ n / x) = 0.
Proof.
Abort.

Lemma lemma_18_13_d : ∀ n : nat,
  ⟦ lim 0⁺ ⟧ (λ x, x * (log x) ^ n) = 0.
Proof.
Abort.

Lemma lemma_18_13_e :
  ⟦ lim 0⁺ ⟧ (λ x, x ^^ x) = 1.
Proof.
Abort.
