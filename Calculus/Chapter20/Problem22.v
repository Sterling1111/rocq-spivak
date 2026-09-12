From Calculus.Chapter20 Require Import Prelude.

Section DerivativeBounds.
Variables f f' f'' : ℝ -> ℝ.
Hypothesis H1 : ⟦ der ⟧ f (0,∞) = f'.
Hypothesis H2 : ⟦ der ⟧ f' (0,∞) = f''.

Lemma lemma_20_22_a : ∀ M0 M2,
  (∀ x, x > 0 -> |f x| <= M0) -> (∀ x, x > 0 -> |f'' x| <= M2) ->
  ∀ x h, x > 0 -> h > 0 -> |f' x| <= 2*M0/h + h*M2/2.
Abort.
Lemma lemma_20_22_b : ∀ M0 M2,
  (∀ x, x > 0 -> |f x| <= M0) -> (∀ x, x > 0 -> |f'' x| <= M2) ->
  ∀ x, x > 0 -> |f' x| <= 2 * sqrt (M0*M2).
Abort.
Lemma lemma_20_22_c : bounded_on f'' (0,∞) ->
  (⟦ lim ∞ ⟧ f = 0) -> ⟦ lim ∞ ⟧ f' = 0.
Abort.
Lemma lemma_20_22_d : ∀ L M,
  (⟦ lim ∞ ⟧ f = L) -> (⟦ lim ∞ ⟧ f'' = M) -> M = 0 /\ ⟦ lim ∞ ⟧ f' = 0.
Abort.
End DerivativeBounds.
