From Calculus.Chapter13 Require Import Prelude.
From Calculus.Chapter13 Require Import Problem38.

Lemma lemma_13_23_a : ∀ f a b m M,
  a < b ->
  integrable_on a b f ->
  (∀ x, x ∈ [a, b] -> m <= f x <= M) ->
  ∃ μ, m <= μ <= M /\ ∫ a b f = (b - a) * μ.
Proof.
  intros f a b m M H1 H2 H3.
  pose proof theorem_13_7 a b f m M ltac:(lra) H2 H3 as [H4 H5].
  exists ((∫ a b f) / (b - a)). repeat split; [ | | solve_R ];
  (apply Rmult_le_reg_r with (r := (b - a)); field_simplify; lra).
Qed.

Lemma lemma_13_23_b : ∀ f a b,
  a < b ->
  continuous_on f [a, b] ->
  ∃ ξ, ξ ∈ [a, b] /\ ∫ a b f = (b - a) * f ξ.
Proof.
  intros f a b H1 H2.
  
  pose proof continuous_on_interval_attains_minimum f a b H1 H2 as [m [H3 H4]].
  pose proof continuous_on_interval_attains_maximum f a b H1 H2 as [M [H5 H6]].

  assert (H7 : integrable_on a b f) by (apply theorem_13_3; solve_R).

  assert (H8 : (∀ x : ℝ, x ∈ [a, b] → f m ≤ f x ≤ f M)).
  { intros x H8. specialize (H4 x H8). specialize (H6 x H8). lra. }

  pose proof lemma_13_23_a f a b (f m) (f M) H1 H7 H8 as [μ [H9 H10]].

  assert (H11 : continuous_on f [Rmin M m, Rmax M m]).
  {
    apply continuous_on_subset with (A2 := [a, b]); auto.
    intros x H11; solve_R.
  }
  
  pose proof intermediate_value_theorem_unordered f M m μ H11 ltac:(solve_R) as [x [H12 H13]].
  
  exists x; solve_R.
Qed.

Lemma lemma_13_23_c : ∀ a b,
  a < b ->
  ∃ (f : ℝ -> ℝ),
    integrable_on a b f /\ ~ continuous_on f [a, b] /\
    ~ (∃ ξ, ξ ∈ [a, b] /\ ∫ a b f = (b - a) * f ξ).
Proof.

Admitted.

Lemma lemma_13_23_d : ∀ f g a b,
  a < b ->
  continuous_on f [a, b] ->
  integrable_on a b g ->
  nonnegative_on g [a, b] ->
 ∃ ξ, ξ ∈ [a, b] /\ ∫ a b (f ⋅ g) = f ξ * ∫ a b g.
Proof.
  intros f g a b H1 H2 H3 H4.
  pose proof continuous_on_interval_attains_minimum f a b H1 H2 as [m [H5 H6]].
  pose proof continuous_on_interval_attains_maximum f a b H1 H2 as [M [H7 H8]].
  assert (H9 : integrable_on a b f) by (apply theorem_13_3; auto; lra).
  assert (H10 : integrable_on a b (f ⋅ g)) by (apply lemma_13_38_e; auto).
  assert (H11 : 0 <= ∫ a b g) by (apply integral_nonneg; auto; try lra; intros x H11; apply Rge_le, H4, H11).
  assert (H12 : f m * ∫ a b g <= ∫ a b (f ⋅ g)).
  {
    rewrite <- integral_mult_scalar; auto.
    apply integral_le; auto; try lra.
    - intros x H12. apply Rmult_le_compat_r; [apply Rge_le, H4 | apply H6]; auto.
    - apply integrable_mult_scalar; auto.
  }
  assert (H13 : ∫ a b (f ⋅ g) <= f M * ∫ a b g).
  {
    rewrite <- integral_mult_scalar; auto.
    apply integral_le; auto; try lra.
    - intros x H13. apply Rmult_le_compat_r; [apply Rge_le, H4 | apply Rge_le, H8]; auto.
    - apply integrable_mult_scalar; auto.
  }
  destruct (Req_dec (∫ a b g) 0) as [H14 | H14].
  - exists a. split; [solve_R | nra].
  - set (μ := (∫ a b (f ⋅ g)) / (∫ a b g)).
    assert (H15 : f m <= μ <= f M).
    {
      unfold μ. split; apply Rmult_le_reg_r with (r := ∫ a b g); try lra;
      field_simplify; lra.
    }
    assert (H16 : continuous_on f [Rmin M m, Rmax M m]).
    { apply continuous_on_subset with (A2 := [a, b]); auto. intros x H16. solve_R. }
    pose proof intermediate_value_theorem_unordered f M m μ H16
      ltac:(pose proof H6 M H7; solve_R) as [x [H17 H18]].
    exists x. split; [solve_R |]. rewrite H18. unfold μ. field. exact H14.
Qed.

Lemma lemma_13_23_e : ∀ f g a b,
  a < b ->
  continuous_on f [a, b] ->
  integrable_on a b g ->
  nonpositive_on g [a, b] ->
 ∃ ξ, ξ ∈ [a, b] /\ ∫ a b (f ⋅ g) = f ξ * ∫ a b g.
Proof.
  intros f g a b H1 H2 H3 H4.
  assert (H5 : integrable_on a b (λ x, -1 * g x)) by (apply integrable_mult_scalar; auto).
  assert (H6 : nonnegative_on (λ x, -1 * g x) [a, b]).
  { intros x H6. specialize (H4 x H6). lra. }
  pose proof lemma_13_23_d f (λ x, -1 * g x) a b H1 H2 H5 H6 as [x [H7 H8]].
  exists x. split; auto.
  replace (f ⋅ (λ x, -1 * g x)) with (λ x, -1 * (f x * g x)) in H8
    by (extensionality y; ring).
  rewrite !integral_mult_scalar in H8; auto.
  - lra.
  - apply lemma_13_38_e; auto. apply theorem_13_3; auto; lra.
Qed.

Lemma lemma_13_23_f : ∀ a b,
  a < b ->
  ∃ (f g : ℝ -> ℝ),
    continuous_on f [a, b] /\
    integrable_on a b g /\
    ~ (∃ ξ, ξ ∈ [a, b] /\ ∫ a b (f ⋅ g) = f ξ * ∫ a b g).
Proof.
  intros a b H1.
  set (f := λ x, x - (a+b)/2).
  exists f, f. repeat split.
  - unfold f. auto_cont.
  - apply theorem_13_3; try lra. unfold f. auto_cont.
  - intros [x [H2 H3]].
    assert (H4 : ∫ a b f = 0).
    {
      replace 0 with ((b^2/2 - (a+b)*b/2) - (a^2/2 - (a+b)*a/2)) by field.
      apply FTC2 with (g := λ x, x^2/2 - (a+b)*x/2); auto; unfold f.
      - auto_cont.
      - auto_diff.
    }
    assert (H5 : 0 < ∫ a b (f ⋅ f)).
    {
      apply integral_pos'; auto.
      - intros y H5. change (0 <= f y * f y). nra.
      - exists a. split; [solve_R | unfold f; cbn; nra].
      - apply continuous_on_mult; unfold f; auto_cont.
    }
    rewrite H4 in H3. nra.
Qed.