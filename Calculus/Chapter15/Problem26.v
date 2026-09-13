From Calculus.Chapter15 Require Import Prelude.

Lemma lemma_15_26_a : ∀ c d,
  c < d ->
  ⟦ lim ∞ ⟧ (λ l, ∫ c d (λ x, sin (l * x))) = 0.
Proof.
  intros c d H1 ε H2.
  exists (2 / ε). intros l H3.
  assert (H4 : 0 < l) by (pose proof Rdiv_pos_pos 2 ε ltac:(lra) H2; lra).
  assert (H5 : ∫ c d (λ x, sin (l * x)) = (- cos (l * d) / l) - (- cos (l * c) / l)).
  { apply FTC2 with (g := λ x, - cos (l * x) / l); auto; [auto_cont | auto_diff]. }
  rewrite H5.
  pose proof cos_bounds (l * c) as H6.
  pose proof cos_bounds (l * d) as H7.
  assert (H8 : 2 / l < ε) by solve_R.
  assert (H9 : - (2 / l) <= - cos (l * d) / l - - cos (l * c) / l <= 2 / l) by solve_R.
  solve_R.
Qed.

Lemma lemma_15_26_b : ∀ s a b,
  a < b ->
  integrable_on a b s ->
  (∃ (parts : list R) (vals : list R), True) ->
  ⟦ lim ∞ ⟧ (λ l, ∫ a b (λ x, s x * sin (l * x))) = 0.
Abort.

Lemma lemma_15_26_c : ∀ f a b,
  a < b ->
  integrable_on a b f ->
  ⟦ lim ∞ ⟧ (λ l, ∫ a b (λ x, f x * sin (l * x))) = 0.
Abort.
