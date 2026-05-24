From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_28_a : ∀ f,
  f = (λ x, (|x|)^3) ->
  ⟦ der ⟧ f = (λ x, 3 * x * |x|) /\
  ⟦ der ^ 2 ⟧ f = (λ x, 6 * |x|) /\
  ~ differentiable_at (λ x, ⟦ Der ^ 2 x ⟧ f) 0.
Proof.
  intros f H1.
  assert (H2 : ⟦ der ⟧ f = (λ x : ℝ, 3 * x * |x|)).
  {
    rewrite H1. intros x. destruct (Rtotal_order x 0) as [H2 | [H2 | H2]];
    try solve [auto_diff].
    apply limit_eq with (f1 := λ h, h * |h|); try auto_limit.
    exists 1; split; [lra |]. intros y H3. solve_R.
  }
  assert (H3 : ⟦ der ^ 2 ⟧ f = (λ x : ℝ, 6 * |x|)).
  {
    rewrite H1 in *. exists (λ x : ℝ, 3 * x * |x|). split.
    + apply nth_derivative_1; auto.
    + intros x. destruct (Rtotal_order x 0) as [H3 | [H3 | H3]]; 
      try solve [auto_diff].
      apply limit_eq with (f1 := λ h, 3 * |h|); try auto_limit.
      exists 1; split; [lra|]. intros y H4; solve_R.
  }
  repeat split; auto.
  intros H4.
  replace (λ x : ℝ, ⟦ Der^2 x ⟧ f) with (λ x : ℝ, 6 * |x|) in H4.
  2 : {
    extensionality x. apply nth_derivative_imp_nth_derive in H3.
    unfold nth_derive_at. rewrite H3. reflexivity.
  }

  destruct H4 as [L H4].

  apply limit_iff in H4 as [H4 H5].

  assert (H6 : ⟦ lim 0⁺ ⟧ (λ h : ℝ, (6 * |0 + h| - 6 * |0|) / h) = 6).
  {
    apply limit_right_eq with (f1 := λ _, 6); [| auto_limit].
    exists 1; split; [lra|]. intros x H6. solve_R.
  }

  assert (H7 : ⟦ lim 0⁻ ⟧ (λ h : ℝ, (6 * |0 + h| - 6 * |0|) / h) = -6).
  {
    apply limit_left_eq with (f1 := λ _, -6); [| auto_limit].
    exists 1; split; [lra|]. intros x H7. solve_R.
  }

  pose proof limit_right_unique _ _ _ _ H6 H5 as H8.
  pose proof limit_left_unique _ _ _ _ H7 H4 as H9.

  lra.
Qed.

Lemma lemma_9_28_b : ∀ f,
  (∀ x, x >= 0 -> f x = x^4) ->
  (∀ x, x <= 0 -> f x = -x^4) ->
  ⟦ der ⟧ f = (λ x, 4 * |x| ^ 3) /\
  ⟦ der ^ 2 ⟧ f = (λ x, 12 * x * |x|) /\
  ⟦ der ^ 3 ⟧ f = (λ x, 24 * |x|) /\
  ~ differentiable_at (λ x, ⟦ Der ^ 3 x ⟧ f) 0.
Proof.
  intros f H1 H2.
  assert (H3 : f = (λ x : ℝ, x * |x| ^ 3)).
  { extensionality x. specialize (H1 x). specialize (H2 x). solve_R. }
  assert (H4 : ⟦ der ⟧ f = (λ x : ℝ, 4 * |x| ^ 3)).
  {
    rewrite H3. intros x. destruct (Rtotal_order x 0) as [H4 | [H4 | H4]];
    try solve [auto_diff].
    apply limit_eq with (f1 := λ h, |h| ^ 3); try auto_limit.
    exists 1; split; [lra |]. intros y H5. solve_R.
  }
  assert (H5 : ⟦ der ^ 2 ⟧ f = (λ x : ℝ, 12 * x * |x|)).
  {
    rewrite H3 in *. exists (λ x : ℝ, 4 * |x| ^ 3). split.
    + apply nth_derivative_1; auto.
    + intros x. destruct (Rtotal_order x 0) as [H5 | [H5 | H5]];
      try solve [auto_diff].
      apply limit_eq with (f1 := λ h, 4 * h * |h|); try auto_limit.
      exists 1; split; [lra|]. intros y H6; solve_R.
  }
  assert (H6 : ⟦ der ^ 3 ⟧ f = (λ x : ℝ, 24 * |x|)).
  {
    rewrite H3 in *. exists (λ x : ℝ, 12 * x * |x|). split; auto.
    intros x. destruct (Rtotal_order x 0) as [H6 | [H6 | H6]];
    try solve [auto_diff].
    apply limit_eq with (f1 := λ h, 12 * |h|); try auto_limit.
    exists 1; split; [lra|]. intros y H7; solve_R.
  }
  repeat split; auto.
  intros H7.
  replace (λ x : ℝ, ⟦ Der^3 x ⟧ f) with (λ x : ℝ, 24 * |x|) in H7.
  2 : {
    extensionality x. apply nth_derivative_imp_nth_derive in H6.
    unfold nth_derive_at. rewrite H6. reflexivity.
  }
  destruct H7 as [L H7].
  apply limit_iff in H7 as [H7 H8].
  assert (H9 : ⟦ lim 0⁺ ⟧ (λ h : ℝ, (24 * |0 + h| - 24 * |0|) / h) = 24).
  {
    apply limit_right_eq with (f1 := λ _, 24); [| auto_limit].
    exists 1; split; [lra|]. intros x H9. solve_R.
  }
  assert (H10 : ⟦ lim 0⁻ ⟧ (λ h : ℝ, (24 * |0 + h| - 24 * |0|) / h) = -24).
  {
    apply limit_left_eq with (f1 := λ _, -24); [| auto_limit].
    exists 1; split; [lra|]. intros x H10. solve_R.
  }
  pose proof limit_right_unique _ _ _ _ H9 H8 as H11.
  pose proof limit_left_unique _ _ _ _ H10 H7 as H12.
  lra.
Qed.