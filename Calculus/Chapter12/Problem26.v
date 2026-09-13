From Calculus.Chapter12 Require Import Prelude.

Lemma lemma_12_26_a : ∀ f,
  non_decreasing f ->
  ~ increasing f ->
  ∃ a b c, a < b /\ ∀ x, a < x < b -> f x = c.
Proof.
  intros f H1 H2.
  unfold increasing, increasing_on in H2.
  apply not_all_ex_not in H2 as [a H2].
  apply not_all_ex_not in H2 as [b H2].
  assert (H3 : a < b /\ f b <= f a).
  {
    split.
    - apply NNPP. intros H3. apply H2.
      intros H4 H5 H6. lra.
    - apply Rnot_lt_le. intros H3. apply H2. auto.
  }
  exists a, b, (f a). split; [lra |].
  intros x H4.
  pose proof H1 a x ltac:(apply Full_intro) ltac:(apply Full_intro) ltac:(lra) as H5.
  pose proof H1 x b ltac:(apply Full_intro) ltac:(apply Full_intro) ltac:(lra) as H6.
  lra.
Qed.

Lemma lemma_12_26_b : ∀ f f',
  differentiable f ->
  ⟦ der ⟧ f = f' ->
  non_decreasing f ->
  ∀ x, f' x >= 0.
Proof.
  intros f f' H1 H2 H3 x.
  destruct (Rlt_dec (f' x) 0) as [H4 | H4]; [ | lra].
  destruct (limit_neg_neighborhood (λ h, (f (x + h) - f x) / h) 0 (f' x)
    (H2 x) H4) as [δ [H5 H6]].
  specialize (H6 (δ / 2) ltac:(solve_R)).
  pose proof H3 x (x + δ / 2) ltac:(apply Full_intro) ltac:(apply Full_intro) ltac:(lra) as H7.
  assert (H8 : 0 <= (f (x + δ / 2) - f x) / (δ / 2)).
  { unfold Rdiv. apply Rmult_le_pos; [lra | left; apply Rinv_0_lt_compat; lra]. }
  lra.
Qed.

Lemma lemma_12_26_c : ∀ f f',
  differentiable f ->
  ⟦ der ⟧ f = f' ->
  (∀ x, f' x >= 0) ->
  non_decreasing f.
Proof.
  intros f f' H1 H2 H3.
  apply derivative_nonneg_imp_nondecreasing with (f' := f'); auto.
Qed.
