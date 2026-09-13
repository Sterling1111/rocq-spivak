From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_61_a : ∀ f f' a L1 L2,
  (∃ δ, δ > 0 /\ ∀ x, 0 < |x - a| < δ -> ⟦ der x ⟧ f = f') ->
  ~ continuous_at f' a ->
  ⟦ lim a⁺ ⟧ f' = L1 ->
  ⟦ lim a⁻ ⟧ f' = L2 ->
  False.
Abort.
