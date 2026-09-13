From Calculus.Chapter20 Require Import Prelude.
From Lib Require Import Binomial.

Local Lemma sin_taylor_polynomial : ∀ n x,
  P(2*n+1,0,sin) x = ∑ 0 n (λ k, (-1)^k * x^(2*k+1) / (fact (2*k+1))).
Proof.
  intros n x.
  assert (H1 : ∀ k, ⟦ Der ^ (2*k) 0 ⟧ sin = 0 /\
    ⟦ Der ^ (2*k+1) 0 ⟧ sin = (-1)^k).
  {
    intros k. destruct (Nat.Even_or_Odd k) as [[m H2] | [m H2]]; subst k.
    - replace (2*(2*m))%nat with (4*m)%nat by lia.
      unfold nth_derive_at. rewrite nth_derive_sin_4n, nth_derive_sin_4n_1, sin_0, cos_0.
      rewrite pow_neg1_even; [split; lra | exists m; lia].
    - replace (2*(2*m+1))%nat with (4*m+2)%nat by lia.
      replace (4*m+2+1)%nat with (4*m+3)%nat by lia.
      unfold nth_derive_at. rewrite nth_derive_sin_4n_2, nth_derive_sin_4n_3, sin_0, cos_0.
      rewrite pow_neg1_odd; [split; lra | exists m; lia].
  }
  induction n as [| n IH].
  - rewrite sum_f_0_0. compute_tp.
    rewrite (derivative_imp_derive _ _ derivative_sin), cos_0. lra.
  - unfold Taylor_polynomial in *.
    replace (2*S n+1)%nat with (S (S (2*n+1))) by lia.
    repeat rewrite sum_f_i_Sn_f; try lia. rewrite IH.
    replace (S (2*n+1)) with (2*S n)%nat by lia.
    replace (S (2*S n)) with (2*S n+1)%nat by lia.
    destruct (H1 (S n)) as [H2 H3]. rewrite H2, H3, Rminus_0_r.
    unfold Rdiv. ring.
Qed.

Lemma lemma_20_3_i :
  |sin 1 - ∑ 0 9 (λ k, (-1)^k / (fact (2*k+1)))| < / 10^17.
Proof.
  assert (H1 : ∃ δ, δ > 0 /\ nth_differentiable_on 20 sin (0-δ,1+δ)).
  {
    exists 1. split; [lra |]. apply nth_differentiable_imp_nth_differentiable_on.
    - apply differentiable_domain_open; lra.
    - apply inf_differentiable_sin.
  }
  destruct (Taylors_Theorem 19 0 1 sin ltac:(lra) H1) as [t [H2 H3]].
  assert (H4 : P(19,0,sin) 1 = ∑ 0 9 (λ k, (-1)^k / (fact (2*k+1)))) by
    (etransitivity; [exact (sin_taylor_polynomial 9 1) |]; apply sum_f_equiv; try lia;
     intros k H; rewrite ?pow1; unfold Rdiv; ring).
  unfold Taylor_remainder in H3. rewrite H4 in H3.
  unfold nth_derive_at in H3.
  replace (19+1)%nat with (4*5)%nat in H3 by lia. rewrite nth_derive_sin_4n in H3.
  replace (((fact (4*5))%nat : ℝ)) with 2432902008176640000 in H3 by
    (rewrite INR_fact_eq_IZR_Z_fact; reflexivity).
  pose proof (sin_bounds t) as H5. rewrite H3. solve_R.
Qed.

Lemma lemma_20_3_ii :
  |sin 2 - ∑ 0 9 (λ k, (-1)^k * 2^(2*k+1) / (fact (2*k+1)))| < / 10^12.
Proof.
  assert (H1 : ∃ δ, δ > 0 /\ nth_differentiable_on 20 sin (0-δ,2+δ)).
  {
    exists 1. split; [lra |]. apply nth_differentiable_imp_nth_differentiable_on.
    - apply differentiable_domain_open; lra.
    - apply inf_differentiable_sin.
  }
  destruct (Taylors_Theorem 19 0 2 sin ltac:(lra) H1) as [t [H2 H3]].
  assert (H4 : P(19,0,sin) 2 = ∑ 0 9 (λ k, (-1)^k * 2^(2*k+1) / (fact (2*k+1)))) by
    (etransitivity; [exact (sin_taylor_polynomial 9 2) |]; apply sum_f_equiv; try lia;
     intros k H; rewrite ?pow1; unfold Rdiv; ring).
  unfold Taylor_remainder in H3. rewrite H4 in H3.
  unfold nth_derive_at in H3.
  replace (19+1)%nat with (4*5)%nat in H3 by lia. rewrite nth_derive_sin_4n in H3.
  replace (((fact (4*5))%nat : ℝ)) with 2432902008176640000 in H3 by
    (rewrite INR_fact_eq_IZR_Z_fact; reflexivity).
  pose proof (sin_bounds t) as H5. rewrite H3. solve_R.
Qed.

Lemma lemma_20_3_iii :
  |sin (1/2) - ∑ 0 8 (λ k, (-1)^k * (1/2)^(2*k+1) / (fact (2*k+1)))| < / 10^20.
Proof.
  assert (H1 : ∃ δ, δ > 0 /\ nth_differentiable_on 18 sin (0-δ,(1/2)+δ)).
  {
    exists 1. split; [lra |]. apply nth_differentiable_imp_nth_differentiable_on.
    - apply differentiable_domain_open; lra.
    - apply inf_differentiable_sin.
  }
  destruct (Taylors_Theorem 17 0 (1/2) sin ltac:(lra) H1) as [t [H2 H3]].
  assert (H4 : P(17,0,sin) (1/2) = ∑ 0 8 (λ k, (-1)^k * (1/2)^(2*k+1) / (fact (2*k+1)))) by
    (etransitivity; [exact (sin_taylor_polynomial 8 (1/2)) |]; apply sum_f_equiv; try lia;
     intros k H; rewrite ?pow1; unfold Rdiv; ring).
  unfold Taylor_remainder in H3. rewrite H4 in H3.
  unfold nth_derive_at in H3.
  replace (17+1)%nat with (4*4+2)%nat in H3 by lia. rewrite nth_derive_sin_4n_2 in H3.
  replace (((fact (4*4+2))%nat : ℝ)) with 6402373705728000 in H3 by
    (rewrite INR_fact_eq_IZR_Z_fact; reflexivity).
  pose proof (sin_bounds t) as H5. rewrite H3. solve_R.
Qed.

Lemma lemma_20_3_iv :
  |e - ∑ 0 8 (λ k, / (fact k))| < / 10^4.
Proof.
  assert (H1 : ∃ δ, δ > 0 /\ nth_differentiable_on 9 exp (0-δ,1+δ)).
  {
    exists 1. split; [lra |]. apply nth_differentiable_imp_nth_differentiable_on.
    - apply differentiable_domain_open; lra.
    - apply inf_differentiable_exp.
  }
  destruct (Taylors_Theorem 8 0 1 exp ltac:(lra) H1) as [t [H2 H3]].
  assert (H4 : P(8,0,exp) 1 = ∑ 0 8 (λ k, / (fact k))) by
    (unfold Taylor_polynomial; apply sum_f_equiv; try lia; intros k H;
     unfold nth_derive_at; rewrite nth_derive_exp, exp_0; rewrite ?Rminus_0_r, ?pow1; unfold Rdiv; ring).
  unfold Taylor_remainder in H3. rewrite H4 in H3.
  unfold nth_derive_at in H3. rewrite nth_derive_exp in H3.
  assert (H5 : 0 < exp t < 3).
  { pose proof (exp_pos t). pose proof (exp_increasing t 1 ltac:(solve_R) ltac:(solve_R) ltac:(solve_R)).
    pose proof e_bound_1_3. lra. }
  replace (((fact (8+1))%nat : ℝ)) with 362880 in H3 by
    (rewrite INR_fact_eq_IZR_Z_fact; reflexivity).
  unfold e. rewrite H3. solve_R.
Qed.

Lemma lemma_20_3_v :
  |exp 2 - ∑ 0 14 (λ k, 2^k / (fact k))| < / 10^5.
Proof.
  assert (H1 : ∃ δ, δ > 0 /\ nth_differentiable_on 15 exp (0-δ,2+δ)).
  {
    exists 1. split; [lra |]. apply nth_differentiable_imp_nth_differentiable_on.
    - apply differentiable_domain_open; lra.
    - apply inf_differentiable_exp.
  }
  destruct (Taylors_Theorem 14 0 2 exp ltac:(lra) H1) as [t [H2 H3]].
  assert (H4 : P(14,0,exp) 2 = ∑ 0 14 (λ k, 2^k / (fact k))) by
    (unfold Taylor_polynomial; apply sum_f_equiv; try lia; intros k H;
     unfold nth_derive_at; rewrite nth_derive_exp, exp_0; rewrite ?Rminus_0_r, ?pow1; unfold Rdiv; ring).
  unfold Taylor_remainder in H3. rewrite H4 in H3.
  unfold nth_derive_at in H3. rewrite nth_derive_exp in H3.
  assert (H5 : 0 < exp t < 9).
  {
    pose proof (exp_pos t) as H6. pose proof e_bound_1_3 as H7.
    pose proof (exp_increasing t 2 ltac:(solve_R) ltac:(solve_R) ltac:(solve_R)) as H8.
    replace 2 with (1+1) in H8 by lra.
    rewrite theorem_18_3 in H8. nra.
  }
  replace (((fact (14+1))%nat : ℝ)) with 1307674368000 in H3 by
    (rewrite INR_fact_eq_IZR_Z_fact; reflexivity).
  rewrite H3. solve_R.
Qed.
