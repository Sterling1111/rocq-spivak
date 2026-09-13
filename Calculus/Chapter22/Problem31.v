From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_31_a : ∀ f a b,
  continuous_on f [a, b] ->
  has_upper_bound (λ y, ∃ x, x ∈ [a, b] /\ f x = y).
Proof.
  intros f a b H1. destruct (Rlt_dec a b) as [H2 | H2].
  - destruct (continuous_on_interval_bounded_above f a b H2 H1) as [M H3].
    exists M. intros y [x [H4 H5]]. subst y. specialize (H3 x H4). lra.
  - exists (f a). intros y [x [H3 H4]].
    assert (x = a) by solve_R. subst. lra.
Qed.

Lemma lemma_22_31_b : ∀ f a b,
  continuous_on f [a, b] ->
  uniformly_continuous_on f [a, b].
Proof.
  intros f a b H1. destruct (Rle_dec a b) as [H2 | H2].
  - apply continuous_on_imp_uniformly_continuous_on; auto.
  - intros ε H3. exists 1. split; [lra |]. intros x y H4 H5 H6. solve_R.
Qed.
