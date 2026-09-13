From Calculus.Chapter5 Require Import Prelude Problem14.

Section Problem15.

Variable α : R.
Hypothesis H1 : ⟦ lim 0 ⟧ (λ x, sin x / x) = α.
Hypothesis H2 : α ≠ 0.

Lemma lemma_5_15_i : ⟦ lim 0 ⟧ (λ x, sin (3 * x) / x) = 3 * α.
Proof.
  apply lemma_5_14_a; solve_R.
Qed.

Lemma lemma_5_15_ii : ∀ a b,
  b <> 0 -> ⟦ lim 0 ⟧ (λ x, sin (a * x) / sin (b * x)) = a / b.
Proof.
  intros a b H3. destruct (Req_dec a 0) as [H4 | H4].
  - rewrite H4.
    replace (0 / b) with 0 by solve_R.
    apply limit_eq with (f1 := λ x, 0).
    2 : { apply limit_const. }
    exists 1. split; [solve_R |].
    intros x H5. rewrite Rmult_0_l, sin_0, Rdiv_0_l. reflexivity.
  - apply limit_eq with (f1 := λ x, (sin (a * x) / x) / (sin (b * x) / x)).
    {
      exists (Rmin 1 (π / (2 * |b|))). split.
      - pose proof π_bounds; pose proof Rdiv_pos_pos π (2 * |b|); solve_R.
      - intros x H5. field; split; [| solve_R]. apply lemma_sin_neq_0_neighborhood; solve_R.
    }
    replace (a / b) with ((a * α) / (b * α)) by solve_R.
    apply limit_div.
    + apply lemma_5_14_a; auto.
    + apply lemma_5_14_a; auto.
    + solve_R.
Qed.

Lemma lemma_5_15_iii : ⟦ lim 0 ⟧ (λ x, (sin x)^2 / x) = 0.
Proof. Abort.

Lemma lemma_5_15_iv : ⟦ lim 0 ⟧ (λ x, (sin (2 * x))^2 / x^2) = 4 * α^2.
Proof.
  apply limit_eq with (f1 := λ x, (sin (2 * x) / x)^2).
  - exists 1. split; [lra | intros x H3; field; solve_R].
  - replace (4 * α^2) with ((2 * α)^2) by ring.
    apply limit_pow, lemma_5_14_a; auto; lra.
Qed.

Lemma lemma_5_15_v : ⟦ lim 0 ⟧ (λ x, (1 - cos x) / x^2) = α^2 / 2.
Proof.
  assert (H3 : ⟦ lim 0 ⟧ (λ x, 1 + cos x) = 2) by auto_limit.
  destruct (limit_neq_neighborhood _ _ _ 0 H3 ltac:(lra)) as [δ [H4 H5]].
  apply limit_eq with (f1 := λ x, (sin x / x)^2 / (1 + cos x)).
  - exists δ. split; auto. intros x H6. specialize (H5 x H6).
    pose proof (pythagorean_identity x) as H7.
    apply Rmult_eq_reg_r with (r := x^2 * (1 + cos x)).
    + field_simplify; solve_R.
    + apply Rmult_integral_contrapositive_currified; [apply pow_nonzero; solve_R | exact H5].
  - apply limit_div; [apply limit_pow; exact H1 | exact H3 | lra].
Qed.

Lemma lemma_5_15_vi : ⟦ lim 0 ⟧ (λ x, ((tan x)^2 + 2 * x) / (x + x^2)) = 2.
Proof.
  assert (H3 : ⟦ lim 0 ⟧ cos = 1) by auto_limit.
  destruct (limit_neq_neighborhood _ _ _ 0 H3 ltac:(lra)) as [δ [H4 H5]].
  apply limit_eq with (f1 := λ x, ((sin x / x) * (sin x / (cos x)^2) + 2) / (1 + x)).
  - exists (Rmin δ (1/2)). split; [solve_R | intros x H6].
    specialize (H5 x ltac:(solve_R)). unfold tan. field; solve_R.
  - apply limit_subst with (L1 := (α * (0 / 1^2) + 2) / (1 + 0)); [field |].
    apply limit_div; [| auto_limit | lra].
    apply limit_plus; [| apply limit_const].
    apply limit_mult; [exact H1 |].
    apply limit_div; [auto_limit | apply limit_pow; exact H3 | lra].
Qed.

Lemma lemma_5_15_vii : ⟦ lim 0 ⟧ (λ x, x * sin x / (1 - cos x)) = 2 / α.
Proof.
  destruct (limit_neq_neighborhood _ _ _ 0 lemma_5_15_v ltac:(solve_R)) as [δ [H3 H4]].
  apply limit_eq with (f1 := λ x, (sin x / x) / ((1 - cos x) / x^2)).
  - exists δ. split; auto. intros x H5. specialize (H4 x H5).
    assert (H6 : 1 - cos x <> 0).
    { intros H6. rewrite H6, Rdiv_0_l in H4. contradiction. }
    field; solve_R.
  - replace (2 / α) with (α / (α^2 / 2)) by (field; auto).
    apply limit_div; [exact H1 | exact lemma_5_15_v | solve_R].
Qed.

Lemma lemma_5_15_viii (x : R) : ⟦ lim 0 ⟧ (λ h, (sin (x + h) - sin x) / h) = α * cos x.
Proof.
  apply limit_eq with (f1 := λ h, - sin x * (h * ((1 - cos h) / h^2)) + cos x * (sin h / h)).
  - exists 1. split; [lra | intros h H3]. rewrite sin_plus. field; solve_R.
  - replace (α * cos x) with (- sin x * (0 * (α^2 / 2)) + cos x * α) by ring.
    apply limit_plus.
    + apply limit_mult; [apply limit_const |].
      apply limit_mult; [apply limit_id | exact lemma_5_15_v].
    + apply limit_mult; [apply limit_const | exact H1].
Qed.

Lemma lemma_5_15_ix : ⟦ lim 1 ⟧ (λ x, sin (x^2 - 1) / (x - 1)) = 2 * α.
Proof.
  apply limit_eq with (f1 := λ x, (x + 1) * (sin (x^2 - 1) / (x^2 - 1))).
  - exists 1. split; [lra | intros x H3; field; solve_R].
  - apply limit_mult; [auto_limit |].
    apply limit_comp with (b := 0) (f := λ h, sin h / h) (g := λ x, x^2 - 1).
    + auto_limit.
    + exact H1.
    + exists 1. split; [lra | intros x H3; solve_R].
Qed.

Lemma lemma_5_15_x : ⟦ lim 0 ⟧ (λ x, x^2 * (3 + sin x) / (x + sin x)^2) = 3 / (1 + α)^2.
Proof.
  assert (H3 : 1 + α <> 0).
  {
    intros H3. destruct (H1 (1/2) ltac:(lra)) as [δ [H4 H5]].
    set (x := Rmin δ π / 2).
    pose proof π_pos as H6.
    assert (H7 : 0 < x < π) by (unfold x; solve_R).
    specialize (H5 x ltac:(unfold x; solve_R)).
    pose proof (sin_gt_0 x H7) as H8.
    pose proof (Rdiv_pos_pos (sin x) x H8 ltac:(lra)) as H9.
    solve_R.
  }
  assert (H4 : ⟦ lim 0 ⟧ (λ x, 1 + sin x / x) = 1 + α).
  { apply limit_plus; [apply limit_const | exact H1]. }
  destruct (limit_neq_neighborhood _ _ _ 0 H4 H3) as [δ [H5 H6]].
  apply limit_eq with (f1 := λ x, (3 + sin x) / (1 + sin x / x)^2).
  - exists δ. split; auto. intros x H7. specialize (H6 x H7).
    assert (H8 : x + sin x <> 0).
    { intros H8. apply H6. replace (sin x) with (-x) by lra. field; solve_R. }
    field; solve_R.
  - apply limit_div; [auto_limit | apply limit_pow; exact H4 | solve_R].
Qed.

Lemma lemma_5_15_xi : ⟦ lim 1 ⟧ (λ x, (x^2 - 1)^3 * (sin (1 / (x - 1)))^3) = 0.
Proof.
  assert (H3 : ⟦ lim 1 ⟧ (λ x, (x^2 - 1)^3) = 0) by auto_limit.
  intros ε H4. specialize (H3 ε H4) as [δ [H5 H6]].
  exists δ. split; auto. intros x H7. specialize (H6 x H7).
  pose proof (sin_bounds (1 / (x - 1))) as H8.
  assert (H9 : |(sin (1 / (x - 1)))^3| <= 1) by solve_R.
  rewrite Rminus_0_r in *. rewrite Rabs_mult.
  pose proof (Rabs_pos ((x^2 - 1)^3)) as H10. nra.
Qed.

End Problem15.