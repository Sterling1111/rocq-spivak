From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_4_a : ∀ (n : nat) (a : nat -> R),
  (n > 0)%nat ->
  minimum_point (λ x, ∑ 1 n (λ i, (x - a i)^2)) ℝ ( (∑ 1 n a) / n ).
Proof.
  intros n a H1.
  set (f := λ x, ∑ 1 n (λ i, (x - a i)^2)).
  set (f' := λ x, 2 * (n * x - ∑ 1 n a)).
  assert (H2 : ⟦ der ⟧ f = f').
  {
    unfold f. apply derivative_ext with (f1' := λ x, ∑ 1 n (λ i, 2 * (x - a i))).
    - intros x. unfold f'. rewrite <- r_mult_sum_f_i_n_f_l, <- sum_f_minus, sum_f_const; try lia.
      replace (n - 1 + 1)%nat with n by lia. ring.
    - apply derivative_sum; try lia. intros k H2. auto_diff.
  }
  assert (H3 : 0 < n) by (apply lt_0_INR; lia).
  apply first_derivative_test_min with (f' := f'); auto.
  - intros x H4. unfold f'. apply Rmult_lt_compat_l with (r := (n : ℝ)) in H4; try lra.
    field_simplify in H4; lra.
  - intros x H4. unfold f'. apply Rmult_lt_compat_l with (r := (n : ℝ)) in H4; try lra.
    field_simplify in H4; lra.
Qed.
