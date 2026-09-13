From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_22 : ∀ x,
  log (exp x) = x.
Proof.
  apply log_exp.
Qed.

Lemma lemma_18_22_a : ∀ A c,
  c < 0 -> ⟦ der ⟧ A = (λ t, c * A t) ->
  ∀ t, A t = A 0 * exp (c * t).
Abort.

Lemma lemma_18_22_b : ∀ A c,
  c < 0 -> ⟦ der ⟧ A = (λ t, c * A t) ->
  let tau := - log 2 / c in
  tau > 0 /\ ∀ t, A (t + tau) = A t / 2.
Abort.
