From Calculus.Chapter8 Require Import Prelude.

Definition norm (f : ℝ -> ℝ) : ℝ :=
  epsilon (inhabits 0) (λ M,
    (∀ x, x ∈ [0, 1] -> |f x| <= M) /\
    (∀ M',
      (∀ x, x ∈ [0, 1] -> |f x| <= M') ->
      M <= M')).

Notation "‖ f ‖" := (norm f)
  (at level 35, format "‖ f ‖").

Lemma norm_spec_full : ∀ f,
  bounded_on f [0, 1] ->
  (∀ x, x ∈ [0, 1] -> |f x| <= ‖ f ‖) /\
  (∀ M,
    (∀ x, x ∈ [0, 1] -> |f x| <= M) ->
    ‖ f ‖ <= M).
Proof.
  intros f H1. unfold norm.

  assert (H2 : ∃ M, ∀ x, x ∈ [0, 1] -> |f x| <= M).
  {
    destruct H1 as [[M1 H3] [M2 H4]].

    exists (Rmax (|M1|) (|M2|)).
    intros x H5.

    specialize (H3 (f x)
      ltac:(exists x; split; [exact H5 | reflexivity])).
    specialize (H4 (f x)
      ltac:(exists x; split; [exact H5 | reflexivity])).

    solve_R.
  }

  destruct H2 as [M H2].

  set (A := λ y,
    exists x, x ∈ [0, 1] /\ y = |f x|).

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

  destruct (completeness_upper_bound A H3 H4)
    as [M' [H5 H6]].

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
  bounded_on f [0, 1] ->
  x ∈ [0, 1] ->
  |f x| <= ‖ f ‖.
Proof.
  intros f x H1 H2.
  destruct (norm_spec_full f H1) as [H3 _].
  apply H3.
  exact H2.
Qed.

Lemma norm_least : ∀ f M,
  bounded_on f [0, 1] ->
  (∀ x, x ∈ [0, 1] -> |f x| <= M) ->
  ‖ f ‖ <= M.
Proof.
  intros f M H1 H2.
  destruct (norm_spec_full f H1) as [_ H3].
  apply H3.
  exact H2.
Qed.

Lemma norm_nonneg : ∀ f,
  bounded_on f [0, 1] ->
  0 <= ‖ f ‖.
Proof.
  intros f H1.
  pose proof (norm_spec f 0 H1 ltac:(solve_R)) as H2.
  pose proof (Rabs_pos (f 0)) as H3.
  lra.
Qed.

Lemma norm_bounded : ∀ f M,
  (∀ x, x ∈ [0, 1] -> |f x| <= M) ->
  bounded_on f [0, 1].
Proof.
  intros f M H1. split; [exists (-M) | exists M];
  intros y [x [H2 H3]]; subst y; specialize (H1 x H2); solve_R.
Qed.

Lemma lemma_8_9_a : ∀ f c,
  bounded_on f [0, 1] ->
  ‖ (λ x, c * f x) ‖ = |c| * ‖ f ‖.
Proof.
  intros f c H1.
  assert (H2 : ∀ x, x ∈ [0, 1] -> |c * f x| <= |c| * ‖ f ‖).
  { intros x H2. rewrite Rabs_mult.
    apply Rmult_le_compat_l; [apply Rabs_pos | apply norm_spec; auto]. }
  pose proof norm_bounded _ _ H2 as H3.
  apply Rle_antisym.
  - apply norm_least; auto.
  - destruct (Req_dec c 0) as [H4 | H4].
    + subst c. rewrite Rabs_R0, Rmult_0_l. apply norm_nonneg; auto.
    + assert (H5 : |c| > 0) by solve_R.
      assert (H6 : ‖ f ‖ <= ‖ (λ x, c * f x) ‖ / |c|).
      { apply norm_least; auto. intros x H6.
        pose proof norm_spec (λ x, c * f x) x H3 H6 as H7.
        simpl in H7. rewrite Rabs_mult in H7.
        apply Rmult_le_reg_r with (r := |c|); auto.
        field_simplify; nra. }
      apply Rmult_le_reg_r with (r := / |c|); [solve_R |].
      field_simplify; nra.
Qed.

Lemma lemma_8_9_b : ∀ f g,
  bounded_on f [0, 1] ->
  bounded_on g [0, 1] ->
  ‖ (λ x, f x + g x) ‖ <= ‖ f ‖ + ‖ g ‖.
Proof.
  intros f g H1 H2.
  assert (H3 : ∀ x, x ∈ [0, 1] -> |f x + g x| <= ‖ f ‖ + ‖ g ‖).
  { intros x H3. pose proof norm_spec f x H1 H3 as H4.
    pose proof norm_spec g x H2 H3 as H5.
    pose proof Rabs_triang (f x) (g x) as H6. lra. }
  apply norm_least; [apply norm_bounded with (M := ‖ f ‖ + ‖ g ‖) |]; auto.
Qed.

Lemma lemma_8_9_c : ∀ h f g,
  bounded_on h [0, 1] ->
  bounded_on f [0, 1] ->
  bounded_on g [0, 1] ->
  ‖ (λ x, h x - f x) ‖ <=
    ‖ (λ x, h x - g x) ‖ +
    ‖ (λ x, g x - f x) ‖.
Proof.
  intros h f g H1 H2 H3.
  assert (H4 : bounded_on (λ x, h x - g x) [0, 1]).
  { apply norm_bounded with (M := ‖ h ‖ + ‖ g ‖). intros x H4.
    pose proof norm_spec h x H1 H4 as H5.
    pose proof norm_spec g x H3 H4 as H6. solve_R. }
  assert (H5 : bounded_on (λ x, g x - f x) [0, 1]).
  { apply norm_bounded with (M := ‖ g ‖ + ‖ f ‖). intros x H5.
    pose proof norm_spec g x H3 H5 as H6.
    pose proof norm_spec f x H2 H5 as H7. solve_R. }
  pose proof lemma_8_9_b (λ x, h x - g x) (λ x, g x - f x) H4 H5 as H6.
  cbv beta in H6.
  replace (λ x, h x - g x + (g x - f x)) with (λ x, h x - f x) in H6.
  - exact H6.
  - extensionality x. ring.
Qed.