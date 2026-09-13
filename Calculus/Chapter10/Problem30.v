From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_30 : ∀ (n k : nat) x,
  (n > 0)%nat -> 
  x <> 0 ->
  ⟦ Der ^ k x ⟧ (λ t, 1 / t ^ n) = (-1)^k * ((fact (n + k - 1))%nat / (fact (n - 1))%nat) * (1 / x ^ (n + k)) /\
  ⟦ Der ^ k x ⟧ (λ t, 1 / t ^ n) = (-1)^k * (fact k)%nat * ((n + k - 1) ∁ k) * (1 / x ^ (n + k)).
Proof.
  intros n k x H1 H2.
  assert (H3 : ∀ k x, x <> 0 ->
    ⟦ Der ^ k x ⟧ (λ t, 1 / t^n) =
    (-1)^k * ((fact (n + k - 1))%nat / (fact (n - 1))%nat) * (1 / x^(n + k))).
  {
    intros j. induction j as [| j IH]; intros y H3.
    - rewrite nth_derive_at_0, Nat.add_0_r. simpl pow.
      field. split; auto using pow_nonzero, INR_fact_neq_0.
    - change (⟦ Der y ⟧ (⟦ Der ^ j ⟧ (λ t, 1 / t^n)) =
        (-1)^(S j) * ((fact (n + S j - 1))%nat / (fact (n - 1))%nat) * (1 / y^(n + S j))).
      apply derivative_at_imp_derive_at with
        (f' := λ t, (-1)^(S j) * ((fact (n + S j - 1))%nat / (fact (n - 1))%nat) * (1 / t^(n + S j))).
      apply derivative_at_eq with
        (f1 := λ t, (-1)^j * ((fact (n + j - 1))%nat / (fact (n - 1))%nat) * (1 / t^(n + j))).
      + exists (|y| / 2). split; [solve_R |].
        intros t H4. symmetry. apply IH. solve_R.
      + set (C := (-1)^j * ((fact (n + j - 1))%nat / (fact (n - 1))%nat)).
        apply derivative_at_ext_val with (f' := λ t, C * ((0 * t^(n + j) - ((n + j)%nat * t^(n + j - 1)) * 1) / (t^(n + j) * t^(n + j)))).
        * apply derivative_at_mult_const_l. apply derivative_at_div.
          -- apply derivative_at_const.
          -- apply derivative_at_pow.
          -- apply pow_nonzero; auto.
        * replace (n + S j - 1)%nat with (S (n + j - 1)) by lia.
          replace (n + S j)%nat with (S (S (n + j - 1))) by lia.
          rewrite fact_simpl, mult_INR. unfold C. simpl pow.
          replace (((n + j)%nat : ℝ)) with (((S (n + j - 1))%nat : ℝ)) by (f_equal; lia).
          replace (y^(n + j)) with (y * y^(n + j - 1)).
          2 : { change (y^(S (n + j - 1)) = y^(n + j)). f_equal; lia. }
          field. repeat split; auto using pow_nonzero, INR_fact_neq_0.
  }
  split; [apply H3; auto |]. rewrite H3; auto.
  rewrite Choose_N_eq_Choose_R, Binomial_R.n_choose_k_def by lia.
  replace (n + k - 1 - k)%nat with (n - 1)%nat by lia.
  field. repeat split; auto using pow_nonzero, INR_fact_neq_0.
Qed.
