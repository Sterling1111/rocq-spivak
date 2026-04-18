From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_34 : ∀ f L,
  ⟦ lim 0⁺ ⟧ (λ x, f (1 / x)) = L <-> ⟦ lim ∞ ⟧ f = L.
Proof.
  intros f L. split.
  - intros H1 N H2.
Abort.