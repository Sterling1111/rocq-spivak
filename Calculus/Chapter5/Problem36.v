From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_36_b : ∀ (f : R -> R) L,
  ⟦ lim ∞ ⟧ f = L <-> ⟦ lim -∞ ⟧ (fun x => f (-x)) = L.
Proof. Abort.

Lemma lemma_5_36_c : ∀ (f : R -> R) L,
  ⟦ lim 0⁻ ⟧ (fun x => f (1 / x)) = L <-> ⟦ lim -∞ ⟧ f = L.
Proof. Abort.
