From Calculus.Chapter13 Require Import Prelude.
From Calculus.Chapter13 Require Import Problem36.

Lemma lemma_13_37 : ∀ f a b,
  a < b ->
  integrable_on a b f ->
  |∫ a b f| <= ∫ a b (λ x, |f x|).
Proof.
  intros f a b H1 H2.
  pose proof lemma_13_36_b f a b H1 H2 as H3.
  assert (H4 : ∫ a b f <= ∫ a b (λ x, |f x|)).
  { apply integral_le; auto; try lra. intros x H4. apply Rle_abs. }
  assert (H5 : integrable_on a b (λ x, -1 * f x)).
  { apply integrable_mult_scalar; auto. }
  assert (H6 : ∫ a b (λ x, -1 * f x) <= ∫ a b (λ x, |f x|)).
  { apply integral_le; auto; try lra. intros x H6. solve_R. }
  rewrite integral_mult_scalar in H6; auto. solve_R.
Qed.
