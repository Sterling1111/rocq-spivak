From Calculus.Chapter7 Require Import Prelude.

Lemma lemma_7_15_a : forall φ n,
  continuous φ ->
  (exists k, n = (2 * k + 1)%nat) ->
  ⟦ lim ∞ ⟧ (λ x, φ x / x ^ n) = 0 ->
  ⟦ lim -∞ ⟧ (λ x, φ x / x ^ n) = 0 ->
  exists x, x ^ n + φ x = 0.
Proof.
  intros φ n H1 [k H2] H3 H4.
Abort.

Lemma lemma_7_15_b : forall φ n,
  continuous φ ->
  (exists k, n = (2 * k)%nat) ->
  ⟦ lim ∞ ⟧ (λ x, φ x / x ^ n) = 0 ->
  ⟦ lim -∞ ⟧ (λ x, φ x / x ^ n) = 0 ->
  exists y, forall x, y ^ n + φ y <= x ^ n + φ x.
Proof.
  intros φ n H1 [k H2] H3 H4.
Abort.