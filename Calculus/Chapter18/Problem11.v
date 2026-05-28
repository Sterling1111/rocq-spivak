From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_11 : forall F,
  (forall x, x ∈ [2, ∞) -> F x = ∫ 2 x (λ t, 1 / log t)) ->
  ~ bounded_on F [2, ∞).
Proof.
Abort.