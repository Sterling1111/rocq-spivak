From Calculus.Chapter11 Require Import Prelude.

Definition lipschitz_order (f : R -> R) (alpha : R) (D : Ensemble R) :=
  ∃ C, C > 0 /\ ∀ x y, x ∈ D -> y ∈ D -> |f x - f y| <= C * (|x - y| ^^ alpha).

Lemma lemma_11_37_a : ∀ f alpha a δ,
  alpha > 0 -> δ > 0 ->
  lipschitz_order f alpha (a - δ, a + δ) ->
  continuous_at f a.
Proof.
  intros f alpha a δ H1 H2 [C [H3 H4]] ε H5.
  pose proof limit_Rabs_Rpower_zero alpha H1 as H6.
  destruct (H6 (ε / C) ltac:(apply Rdiv_pos_pos; lra)) as [η [H7 H8]].
  exists (Rmin δ η). split; [solve_R |].
  intros x H9.
  specialize (H4 x a ltac:(solve_R) ltac:(solve_R)).
  specialize (H8 (x - a) ltac:(solve_R)).
  assert (H10 : |x - a| ^^ alpha < ε / C) by solve_R.
  apply Rmult_lt_compat_l with (r := C) in H10; try lra.
  field_simplify in H10; lra.
Qed.

Lemma lemma_11_37_b : ∀ f alpha D,
  alpha > 0 ->
  lipschitz_order f alpha D ->
  uniformly_continuous_on f D.
Proof.
  intros f alpha D H1 [C [H2 H3]] ε H4.
  pose proof limit_Rabs_Rpower_zero alpha H1 as H5.
  destruct (H5 (ε / C) ltac:(apply Rdiv_pos_pos; lra)) as [δ [H6 H7]].
  exists δ. split; auto. intros x y H8 H9 H10.
  destruct (Req_dec x y) as [H11 | H11].
  - subst. rewrite Rminus_diag, Rabs_R0. exact H4.
  - specialize (H3 x y H8 H9). specialize (H7 (x - y) ltac:(solve_R)).
    assert (H12 : |x - y| ^^ alpha < ε / C) by solve_R.
    apply Rmult_lt_compat_l with (r := C) in H12; try lra.
    field_simplify in H12; lra.
Qed.

Lemma lemma_11_37_e : ∀ f alpha a b,
  a < b ->
  alpha > 1 ->
  lipschitz_order f alpha [a, b] ->
  ∃ c, ∀ x, x ∈ [a, b] -> f x = c.
Proof.
  intros f alpha a b H1 H2 H3.
  assert (H4 : continuous_on f [a, b]).
  {
    pose proof lemma_11_37_b f alpha [a, b] ltac:(lra) H3 as H4.
    intros x H5 ε H6. destruct (H4 ε H6) as [δ [H7 H8]].
    exists δ. split; auto. intros y H9 H10. apply H8; solve_R.
  }
  destruct H3 as [C [H3 H5]].
  assert (H6 : ⟦ der ⟧ f (a, b) = λ _, 0).
  {
    apply derivative_at_imp_derivative_on; [apply differentiable_domain_open; auto |].
    intros x H6 ε H7.
    pose proof limit_Rabs_Rpower_zero (alpha - 1) ltac:(lra) as H8.
    destruct (H8 (ε / C) ltac:(apply Rdiv_pos_pos; lra)) as [δ [H9 H10]].
    exists (Rmin δ (Rmin (x - a) (b - x))). split; [solve_R |].
    intros h H11.
    specialize (H5 (x + h) x ltac:(solve_R) ltac:(solve_R)).
    replace (x + h - x) with h in H5 by lra.
    specialize (H10 h ltac:(solve_R)).
    assert (H12 : |h| > 0) by solve_R.
    assert (H13 : |(f (x + h) - f x) / h| <= C * (|h| ^^ (alpha - 1))).
    {
      rewrite Rabs_div, Rpower_minus, Rpower_1; try lra.
      apply Rmult_le_reg_r with (r := |h|); try lra.
      field_simplify; lra.
    }
    assert (H14 : |h| ^^ (alpha - 1) < ε / C) by solve_R.
    apply Rmult_lt_compat_l with (r := C) in H14; try lra.
    field_simplify in H14; solve_R.
  }
  exists (f a). intros x H7.
  destruct (Req_dec x a) as [H8 | H8]; [subst; reflexivity |].
  assert (H9 : continuous_on f [a, x]).
  { apply continuous_on_subset with (A2 := [a, b]); auto. intros y H9; solve_R. }
  assert (H10 : differentiable_on f (a, x)).
  {
    apply derivative_on_imp_differentiable_on with (f' := λ _, 0).
    apply derivative_on_subset with (D1 := (a, b)); auto.
    - apply differentiable_domain_open; solve_R.
    - intros y H10; solve_R.
  }
  pose proof mean_value_theorem f a x ltac:(solve_R) H9 H10 as [c [H11 H12]].
  pose proof derivative_on_imp_derivative_at f (λ _, 0) (a, b) c ltac:(auto_interval) H6 as H13.
  pose proof derivative_at_unique f _ _ c H13 H12 as H14.
  simpl in H14. apply Rmult_eq_compat_r with (r := x - a) in H14.
  field_simplify in H14; lra.
Qed.
