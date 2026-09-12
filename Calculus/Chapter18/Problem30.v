From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_30 : ∀ n : nat,
  ⟦ lim ∞ ⟧ (λ x, e ^^ x / x ^ n) = ∞.
Proof.
  intros n.
Abort.
