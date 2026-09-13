From Calculus.Chapter14 Require Import Prelude.
From Lib Require Import Exponential Completeness.

Lemma lemma_14_25_a : ∀ r,
  r < -1 ->
  ∫ 1 ∞ (λ x, x ^^ r) = (1 / (-(r + 1))).
Proof.
  intros r H1. split.
  - intros x H2. apply theorem_13_3; [lra | auto_cont].
  - assert (H2 : ⟦ lim ∞ ⟧ (λ x, x ^^ (r + 1)) = 0).
    {
      intros ε H2.
      destruct (limit_Rabs_Rpower_zero (-(r + 1)) ltac:(lra) ε H2) as [δ [H3 H4]].
      exists (Rmax 1 (1 / δ)). intros x H5.
      assert (H6 : 0 < x /\ 0 < 1 / x < δ) by solve_R.
      specialize (H4 (1 / x) ltac:(solve_R)).
      replace (|1 / x|) with (1 / x) in H4 by (symmetry; apply Rabs_right; lra).
      rewrite Rpower_inv, Ropp_involutive in H4; [exact H4 | lra].
    }
    intros ε H3.
    destruct (H2 (ε * (-(r + 1))) ltac:(nra)) as [N H4].
    exists (Rmax 1 N). intros x H5.
    assert (H6 : x > 1 /\ x > N) by solve_R.
    specialize (H4 x ltac:(lra)).
    assert (H7 : ∫ 1 x (λ t, t ^^ r) = (x ^^ (r + 1) - 1) / (r + 1)).
    {
      replace ((x ^^ (r + 1) - 1) / (r + 1)) with
        ((λ t, t ^^ (r + 1) / (r + 1)) x - (λ t, t ^^ (r + 1) / (r + 1)) 1)
        by (cbn beta; rewrite Rpower_1_base; field; lra).
      apply FTC2 with (g := λ t, t ^^ (r + 1) / (r + 1));
        [lra | auto_cont | auto_diff].
    }
    rewrite H7.
    replace ((x ^^ (r + 1) - 1) / (r + 1) - 1 / -(r + 1)) with
      (x ^^ (r + 1) / (r + 1)) by (field; lra).
    rewrite Rabs_div.
    replace (|r + 1|) with (-(r + 1)) by (symmetry; apply Rabs_left; lra).
    solve_R.
Qed.

Lemma lemma_14_25_b :
  ~ (∃ L, ∫ 1 ∞ (λ x, 1 / x) = L).
Proof.
  intros [L [H1 H2]].
  assert (H3 : ∀ (n : ℕ), ∫ 1 (2^n) (λ x, 1 / x) = n * ∫ 1 2 (λ x, 1 / x)).
  {
    intros n. rewrite <- log_spec, <- log_spec; [apply corollary_18_1; lra | lra | apply pow_lt; lra].
  }
  assert (H4 : ∫ 1 2 (λ x, 1 / x) > 0).
  {
    apply integral_pos; [lra | intros x H4; solve_R | auto_cont |].
    apply theorem_13_3; [lra | auto_cont].
  }
  destruct (H2 1 ltac:(lra)) as [N H5].
  destruct (INR_unbounded (Rmax N ((|L| + 2) / ∫ 1 2 (λ x, 1 / x)))) as [n H6].
  pose proof n_lt_pow2_n n as H7.
  specialize (H5 (2^n) ltac:(solve_R)). rewrite H3 in H5. solve_R.
Qed.

Lemma lemma_14_25_c_aux : ∀ f a,
  (∀ x, x >= a -> f x >= 0) ->
  (∀ x, x > a -> integrable_on a x f) ->
  (∃ M, ∀ x, x > a -> ∫ a x f <= M) ->
  ∃ L, ∫ a ∞ f = L.
Proof.
  intros f a H1 H2 [M H3].
  set (E := λ y, ∃ x, x > a /\ y = ∫ a x f).
  assert (H4 : has_upper_bound E).
  { exists M. intros y [x [H4 H5]]. subst y. apply H3. exact H4. }
  assert (H5 : E ≠ ∅).
  { apply not_Empty_In. exists (∫ a (a + 1) f), (a + 1). split; [lra | reflexivity]. }
  destruct (completeness_upper_bound E H4 H5) as [L H6].
  exists L. split; [exact H2 |]. intros ε H7.
  destruct (exists_point_within_delta E L ε H6 H7) as [y [[N [H8 H9]] H10]].
  exists N. intros x H11.
  assert (H12 : ∫ a x f <= L).
  { apply H6. exists x. split; [lra | reflexivity]. }
  assert (H13 : 0 <= ∫ N x f).
  {
    apply integral_nonneg; [lra | |].
    - intros t H13. specialize (H1 t ltac:(solve_R)). lra.
    - apply integrable_on_sub_interval with (a := a) (b := x); [lra | apply H2; lra].
  }
  pose proof integral_split f a x N ltac:(lra) (H2 x ltac:(lra)) as H14.
  solve_R.
Qed.

Lemma lemma_14_25_c : ∀ f g,
  (∀ x, x >= 0 -> f x >= 0) ->
  (∃ L, ∫ 0 ∞ f = L) ->
  (∀ x, x >= 0 -> 0 <= g x <= f x) ->
  (∀ N, N > 0 -> integrable_on 0 N g) ->
  ∃ L, ∫ 0 ∞ g = L.
Proof.
  intros f g H1 [L [H2 H3]] H4 H5.
  apply lemma_14_25_c_aux; [intros x H6; specialize (H4 x H6); lra | exact H5 |].
  destruct (H3 1 ltac:(lra)) as [N H6].
  exists (L + 1). intros x H7.
  set (y := Rmax N x + 1).
  assert (H8 : y > N /\ y > x) by (unfold y; solve_R).
  specialize (H6 y ltac:(lra)).
  assert (H9 : ∫ 0 x g <= ∫ 0 x f).
  { apply integral_le; [lra | intros t H9; apply H4; solve_R | apply H5; lra | apply H2; lra]. }
  assert (H10 : 0 <= ∫ x y f).
  {
    apply integral_nonneg; [lra | |].
    - intros t H10. specialize (H1 t ltac:(solve_R)). lra.
    - apply integrable_on_sub_interval with (a := 0) (b := y); [lra | apply H2; lra].
  }
  pose proof integral_split f 0 y x ltac:(lra) (H2 y ltac:(lra)) as H11.
  solve_R.
Qed.

Lemma lemma_14_25_d :
  ∃ L, ∫ 0 ∞ (λ x, 1 / (1 + x^2)) = L.
Proof.
  set (f := λ x : ℝ, 1 / (1 + x^2)).
  assert (H1 : ∀ x, 0 <= f x) by (intros x; unfold f; solve_R).
  assert (H2 : ∀ a b, a <= b -> integrable_on a b f).
  { intros a b H2. apply theorem_13_3; [exact H2 | unfold f; auto_cont]. }
  apply lemma_14_25_c_aux; [intros x H3; specialize (H1 x); lra | intros x H3; apply H2; lra |].
  exists (∫ 0 1 f + 1). intros x H3.
  destruct (Rle_dec x 1) as [H4 | H4].
  - destruct (Req_dec x 1) as [H5 | H5]; [subst x; lra |].
    pose proof integral_split f 0 1 x ltac:(lra) (H2 0 1 ltac:(lra)) as H6.
    pose proof integral_nonneg x 1 f ltac:(lra) ltac:(intros t H7; apply H1) (H2 x 1 H4) as H7.
    lra.
  - assert (H5 : ∫ 1 x f <= ∫ 1 x (λ t, 1 / t^2)).
    {
      apply integral_le; [lra | | apply H2; lra | apply theorem_13_3; [lra | auto_cont]].
      intros t H5. unfold f. solve_R.
    }
    assert (H6 : ∫ 1 x (λ t, 1 / t^2) = 1 - 1 / x).
    {
      replace (1 - 1 / x) with ((λ t, -1 / t) x - (λ t, -1 / t) 1) by (cbn beta; field; lra).
      apply FTC2 with (g := λ t, -1 / t); [lra | auto_cont | auto_diff].
    }
    pose proof integral_split f 0 x 1 ltac:(lra) (H2 0 x ltac:(lra)) as H7.
    rewrite H6 in H5. solve_R.
Qed.
