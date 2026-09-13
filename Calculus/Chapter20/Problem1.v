From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_1_i : ∀ x,
  P(3, 0, λ x, exp (exp x)) x = exp 1 * (1 + x + x^2 + 5 / 6 * x^3).
Proof.
  compute_tp.
Qed.

Lemma lemma_20_1_ii : ∀ x,
  P(3, 0, λ x, exp (sin x)) x = 1 + x + x^2 / 2.
Proof.
  compute_tp.
Qed.  

Lemma lemma_20_1_iii : ∀ n x,
  P(2 * n, π / 2, sin) x = ∑ 0 n (λ k, (-1)^k / (fact (2 * k)) * (x - π / 2)^(2 * k)).
Proof.
  intros n x.
  assert (H1 : ∀ k, ⟦ Der ^ (2*k) π / 2 ⟧ sin = (-1)^(k) /\
    ⟦ Der ^ (2*k+1) π / 2 ⟧ sin = 0).
  {
    intros k. destruct (Nat.Even_or_Odd k) as [[m H2] | [m H2]]; subst k.
    - replace (2*(2*m))%nat with (4*m)%nat by lia.
      replace (2*(2*m)+1)%nat with (4*m+1)%nat by lia.
      unfold nth_derive_at. rewrite nth_derive_sin_4n, nth_derive_sin_4n_1.
      rewrite sin_π_over_2, cos_π_over_2.
      rewrite pow_neg1_even; [split; lra | exists m; lia].
    - replace (2*(2*m+1))%nat with (4*m+2)%nat by lia.
      replace (2*(2*m+1)+1)%nat with (4*m+3)%nat by lia.
      replace (4*m+2+1)%nat with (4*m+3)%nat by lia.
      unfold nth_derive_at. rewrite nth_derive_sin_4n_2, nth_derive_sin_4n_3.
      rewrite sin_π_over_2, cos_π_over_2.
      rewrite pow_neg1_odd; [split; lra | exists m; lia].
  }
  unfold Taylor_polynomial. induction n as [| n IH].
  - repeat rewrite sum_f_0_0. destruct (H1 0%nat) as [H2 H3].
    simpl in H2. simpl. rewrite H2. ring.
  - replace (2 * S n)%nat with (S (S (2*n))) by lia.
    repeat rewrite sum_f_i_Sn_f; try lia.
    rewrite IH.
    replace (S (2*n)) with (2*n+1)%nat by lia.
    replace (S (2*n+1)) with (2*S n)%nat by lia.
    destruct (H1 n) as [H2 H3]. destruct (H1 (S n)) as [H4 H5].
    rewrite H3, H4. unfold Rdiv. ring.
Qed.

Lemma lemma_20_1_iv : ∀ n x,
  P(2 * n, π, cos) x = ∑ 0 n (λ k, (-1)^(k+1) / (fact (2 * k)) * (x - π)^(2 * k)).
Proof.
  intros n x.
  assert (H1 : ∀ k, ⟦ Der ^ (2*k) π ⟧ cos = (-1)^(k+1) /\
    ⟦ Der ^ (2*k+1) π ⟧ cos = 0).
  {
    intros k. destruct (Nat.Even_or_Odd k) as [[m H2] | [m H2]]; subst k.
    - replace (2*(2*m))%nat with (4*m)%nat by lia.
      replace (2*(2*m)+1)%nat with (4*m+1)%nat by lia.
      unfold nth_derive_at. rewrite nth_derive_cos_4n, nth_derive_cos_4n_1.
      rewrite cos_π, sin_π.
      rewrite pow_neg1_odd; [split; lra | exists m; lia].
    - replace (2*(2*m+1))%nat with (4*m+2)%nat by lia.
      replace (2*(2*m+1)+1)%nat with (4*m+3)%nat by lia.
      replace (4*m+2+1)%nat with (4*m+3)%nat by lia.
      unfold nth_derive_at. rewrite nth_derive_cos_4n_2, nth_derive_cos_4n_3.
      rewrite cos_π, sin_π.
      rewrite pow_neg1_even; [split; lra | exists (S m); lia].
  }
  unfold Taylor_polynomial. induction n as [| n IH].
  - repeat rewrite sum_f_0_0. destruct (H1 0%nat) as [H2 H3].
    simpl in H2. simpl. rewrite H2. ring.
  - replace (2 * S n)%nat with (S (S (2*n))) by lia.
    repeat rewrite sum_f_i_Sn_f; try lia.
    rewrite IH.
    replace (S (2*n)) with (2*n+1)%nat by lia.
    replace (S (2*n+1)) with (2*S n)%nat by lia.
    destruct (H1 n) as [H2 H3]. destruct (H1 (S n)) as [H4 H5].
    rewrite H3, H4. unfold Rdiv. ring.
Qed.

Lemma lemma_20_1_v : ∀ n x,
  P(n, 1, exp) x = ∑ 0 n (λ k, exp 1 / (fact k) * (x - 1)^k).
Proof.
  compute_tp.
  apply sum_f_equiv; try lia.
  intros k H1. rewrite nth_derive_exp. lra.
Qed.

Lemma lemma_20_1_vi : ∀ n x,
  (n > 0)%nat ->
  P(n, 2, log) x = log 2 + ∑ 0 (n-1) (λ k, (-1)^(k) / ((k+1) * 2^(k+1)) * (x - 2)^(k+1)).
Proof.
  intros n x H1. unfold Taylor_polynomial.
  rewrite sum_f_Si; try lia.
  rewrite (sum_f_reindex (λ k, ⟦ Der ^ k 2 ⟧ log / (fact k) * (x-2)^k) 1 n 1); try lia.
  replace (1 - 1)%nat with 0%nat by lia.
  rewrite nth_derive_at_0. simpl fact. simpl INR. simpl pow.
  rewrite Rdiv_1_r, Rmult_1_r, Rplus_comm.
  f_equal. apply sum_f_equiv; try lia. intros k H2.
  replace (k + 1)%nat with (S k) by lia.
  replace log with ln by (extensionality y; apply ln_eq_log).
  rewrite nth_derive_ln; try lra.
  replace (fact (S k)) with (S k * fact k)%nat by reflexivity.
  rewrite mult_INR, S_INR. field. repeat split;
    try apply INR_fact_neq_0; try (apply pow_nonzero; lra).
  pose proof pos_INR k. lra.
Qed.

Lemma lemma_20_1_vii : ∀ x,
  P(4, 0, λ x, x^5 + x^3 + x) x = x^3 + x.
Proof.
  compute_tp.
Qed.

Lemma lemma_20_1_viii : ∀ x,
  P(4, 1, λ x, x^5 + x^3 + x) x = 3 + 9*(x-1) + 13*(x-1)^2 + 11*(x-1)^3 + 5*(x-1)^4.
Proof.
  compute_tp. 
Qed.

Lemma lemma_20_1_ix : ∀ n x,
  P(2 * n + 1, 0, λ x, 1 / (1 + x^2)) x = ∑ 0 n (λ k, (-1)^k * x^(2 * k)).
Proof.
  compute_tp.
Abort.

Lemma lemma_20_1_x : ∀ n x,
  P(n, 0, λ x, 1 / (1 + x)) x = ∑ 0 n (λ k, (-1)^k * x^k).
Proof.
  compute_tp.
  apply sum_f_equiv; try lia.
  intros k H1.
  induction k as [| k IH]; [ solve_R |].
Abort.