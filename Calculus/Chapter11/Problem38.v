From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_38 : forall (n : ℕ) (a : ℕ -> ℝ),
  ∑ 0 n (λ i, a i / (i + 1)) = 0 ->
  ∃ x, x ∈ (0, 1) /\ ∑ 0 n (λ i, a i * x^i) = 0.
Proof.
  intros n a H1.
  set (f := λ x, ∑ 0 n (λ i : ℕ, a i / (i + 1) * x ^ (i + 1))).
  set (f' := λ x, ∑ 0 n (λ i : ℕ, a i * x ^ i)).

  assert (H2 : f 0 = 0).
  {
    unfold f.
    replace (λ i : ℕ, a i / (i + 1) * 0 ^ (i + 1)) with (λ _ : ℕ, 0).
    2 : { extensionality i. rewrite pow_i; try lia; try lra. }
    rewrite sum_f_const; solve_R.
  }

  assert (H3 : f 1 = 0).
  {
    unfold f.
    replace (λ i : ℕ, a i / (i + 1) * 1 ^ (i + 1)) with (λ i : ℕ, a i / (i + 1)); auto.
    extensionality i. rewrite pow1. lra.
  }

  assert (H4 : ⟦ der ⟧ f = f').
  {
    unfold f, f'.
    apply derivative_sum; [lia|].
    intros k H4.
    apply derivative_ext with (f1' := λ x : ℝ, a k / (k + 1) * (INR (k + 1) * x ^ (k + 1 - 1))).
  - intros x.
    replace (k + 1 - 1)%nat with k by lia.
    replace (INR (k + 1)) with (k + 1) by (rewrite plus_INR; simpl; lra).
    assert (H5 : k + 1 <> 0) by (pose proof pos_INR k; lra).
    solve_R.
  - apply derivative_mult_const_l, derivative_pow.
  }

  assert (H5 : continuous_on f [0, 1]).
  {
    apply differentiable_on_imp_continuous_on_closed; try lra.
    apply derivative_on_imp_differentiable_on with (f' := f').
    apply derivative_imp_derivative_on; auto.
    apply differentiable_domain_closed; lra.
  }

  assert (H6 : differentiable_on f (0, 1)).
  {
    apply derivative_on_imp_differentiable_on with (f' := f').
    apply derivative_imp_derivative_on; auto.
    apply differentiable_domain_open; lra.
  }

  pose proof rolles_theorem f 0 1 ltac:(lra) H5 H6 ltac:(lra) as [x [H7 H8]].

  exists x; split; auto.

  exact (derivative_at_unique f f' (λ _, 0) x (H4 x) H8).
Qed.