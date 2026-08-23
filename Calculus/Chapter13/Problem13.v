From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_13_a : forall f a b,
  a <= b ->
  integrable_on a b f ->
  (∀ x, x ∈ [a, b] -> f x >= 0) ->
  ∫ a b f >= 0.
Proof.
  intros f a b H1 H2 H3.
  apply Rle_ge, integral_nonneg; auto.
  intros x.
  specialize (H3 x).
  solve_R.
Qed.

Lemma lemma_13_13_b : forall f g a b,
  a <= b ->
  integrable_on a b f ->
  integrable_on a b g ->
  (forall x, x ∈ [a, b] -> f x >= g x) ->
  ∫ a b f >= ∫ a b g.
Proof.
  intros f g a b H1 H2 H3 H4.

  set (h := (f - g)%function).

  assert (H5 : ∀ x, x ∈ [a, b] -> h x >= 0).
  { intros x H5. unfold h. specialize (H4 x H5). lra. }

  assert (H6 : ∫ a b h = ∫ a b f - ∫ a b g).
  { unfold h. apply integral_minus; auto. }

  assert (H7 : integrable_on a b h).
  { apply integrable_minus; auto. }

  pose proof lemma_13_13_a h a b H1 H7 H5 as H8.

  lra.
Qed.

Lemma lemma_13_13_b' : forall f g a b,
  a <= b ->
  integrable_on a b f ->
  integrable_on a b g ->
  (forall x, x ∈ [a, b] -> f x >= g x) ->
  ∫ a b f >= ∫ a b g.
Proof.
  intros f g a b H1 H2 H3 H4.
  apply Rle_ge, integral_le; auto.
  intro x.
  specialize (H4 x); solve_R.
Qed.