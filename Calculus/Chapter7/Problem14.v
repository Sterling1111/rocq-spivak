From Calculus.Chapter7 Require Import Prelude.

Definition norm (f : ℝ -> ℝ) : ℝ :=
  epsilon (inhabits 0) (λ M,
    (∀ x, x ∈ [0, 1] -> | f x | <= M) /\
    (∀ M', (∀ x, x ∈ [0, 1] -> | f x | <= M') -> M <= M')).

Notation "‖ f ‖" := (norm f) (at level 35, format "‖ f ‖").

Lemma norm_spec_full : ∀ f,
  continuous_on f [0, 1] ->
  (∀ x, x ∈ [0, 1] -> |f x| <= ‖ f ‖) /\
  (∀ M, (∀ x, x ∈ [0, 1] -> |f x| <= M) -> ‖ f ‖ <= M).
Proof.
  intros f H1. unfold norm.

  assert (H2 : ∃ M, ∀ x, x ∈ [0, 1] -> |f x| <= M).
  {
    assert (H3 : 0 < 1) by solve_R.
    pose proof
      (continuous_on_interval_bounded_below_le f 0 1 H3 H1)
      as [M1 H4].
    pose proof
      (continuous_on_interval_bounded_below_ge f 0 1 H3 H1)
      as [M2 H5].

    exists (Rmax (|M1|) (|M2|)).
    intros x H6.
    specialize (H4 x H6).
    specialize (H5 x H6).
    solve_R.
  }

  destruct H2 as [M H2].

  set (A := λ y, exists x, x ∈ [0, 1] /\ y = |f x|).

  assert (H3 : has_upper_bound A).
  {
    exists M.
    intros y [x [H4 H5]].
    rewrite H5.
    apply H2.
    exact H4.
  }

  assert (H4 : A ≠ ∅).
  {
    apply not_Empty_In.
    exists (|f 0|).
    exists 0.
    split; [solve_R | reflexivity].
  }

  destruct (completeness_upper_bound A H3 H4) as [M' [H5 H6]].

  assert (H7 :
    ∃ M0,
      (∀ x, x ∈ [0, 1] -> |f x| <= M0) /\
      (∀ M1,
        (∀ x, x ∈ [0, 1] -> |f x| <= M1) ->
        M0 <= M1)).
  {
    exists M'.
    split.

    - intros x H7.
      apply H5.
      exists x.
      split; [exact H7 | reflexivity].

    - intros M0 H7.
      apply H6.
      intros y [x [H8 H9]].
      rewrite H9.
      apply H7.
      exact H8.
  }

  exact (epsilon_spec (inhabits 0) _ H7).
Qed.

Lemma norm_spec : ∀ f x,
  continuous_on f [0, 1] ->
  x ∈ [0, 1] ->
  |f x| <= ‖ f ‖.
Proof.
  intros f x H1 H2.
  destruct (norm_spec_full f H1) as [H3 _].
  apply H3.
  exact H2.
Qed.

Lemma norm_least : ∀ f M,
  continuous_on f [0, 1] ->
  (∀ x, x ∈ [0, 1] -> |f x| <= M) ->
  ‖ f ‖ <= M.
Proof.
  intros f M H1 H2.
  destruct (norm_spec_full f H1) as [_ H3].
  apply H3.
  exact H2.
Qed.

Lemma norm_nonneg : ∀ f,
  continuous_on f [0, 1] ->
  0 <= ‖ f ‖.
Proof.
  intros f H1.
  pose proof (norm_spec f 0 H1 ltac:(solve_R)) as H2.
  pose proof (Rabs_pos (f 0)) as H3.
  lra.
Qed.

Lemma lemma_7_14_a : ∀ f c,
  continuous_on f [0, 1] ->
  ‖ (λ x, c * (f x)) ‖ = |c| * ‖ f ‖.
Proof.
  intros f c H1.
  assert (H2 : continuous_on (λ x, c * f x) [0, 1]).
  { apply continuous_on_mult_const_l; auto. }
  assert (H3 : ‖ (λ x, c * f x) ‖ <= |c| * ‖ f ‖).
  {
    apply norm_least; auto. intros x H3. rewrite Rabs_mult.
    apply Rmult_le_compat_l; [apply Rabs_pos | apply norm_spec; auto].
  }
  destruct (Req_dec c 0) as [H4 | H4].
  - subst c. pose proof (norm_nonneg _ H2). solve_R.
  - assert (H5 : 0 < |c|) by (apply Rabs_pos_lt; auto).
    assert (H6 : ‖ f ‖ <= ‖ (λ x, c * f x) ‖ / |c|).
    {
      apply norm_least; auto. intros x H6.
      apply Rmult_le_reg_r with (r := |c|); [exact H5 |].
      field_simplify; try lra.
      pose proof (norm_spec _ x H2 H6) as H7.
      cbn in H7. rewrite Rabs_mult in H7. nra.
    }
    apply Rmult_le_compat_r with (r := |c|) in H6; [ | lra].
    field_simplify in H6; nra.
Qed.

Lemma lemma_7_14_b : ∀ f g,
  continuous_on f [0, 1] ->
  continuous_on g [0, 1] ->
  ‖ (λ x, f x + g x) ‖ <= ‖ f ‖ + ‖ g ‖.
Proof.
  intros f g H1 H2. apply norm_least.
  - apply continuous_on_plus; auto.
  - intros x H3. pose proof (norm_spec f x H1 H3) as H4.
    pose proof (norm_spec g x H2 H3) as H5.
    pose proof (Rabs_triang (f x) (g x)) as H6. lra.
Qed.

Lemma lemma_7_14_c : ∀ h f g,
  continuous_on h [0, 1] ->
  continuous_on f [0, 1] ->
  continuous_on g [0, 1] ->
  ‖ (λ x, h x - f x) ‖ <= ‖ (λ x, h x - g x) ‖ + ‖ (λ x, g x - f x) ‖.
Proof.
  intros h f g H1 H2 H3.
  replace (λ x, h x - f x) with (λ x, (h x - g x) + (g x - f x))
    by (extensionality x; ring).
  apply lemma_7_14_b; apply continuous_on_minus; auto.
Qed.
