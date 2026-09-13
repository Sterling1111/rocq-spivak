From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_17_a : ∀ g g' a n M δ,
  δ > 0 -> M >= 0 -> ⟦ der ⟧ g (a-δ,a+δ) = g' ->
  (∀ x, |x-a| < δ -> |g' x| <= M * |x-a|^n) ->
  ∀ x, |x-a| < δ -> |g x - g a| <= M * |x-a|^(S n) / (S n).
Abort.

Lemma lemma_20_17_b : ∀ g g' a n δ,
  δ > 0 -> ⟦ der ⟧ g (a-δ,a+δ) = g' ->
  (⟦ lim a ⟧ (λ x, g' x / (x-a)^n) = 0) ->
  ⟦ lim a ⟧ (λ x, (g x - g a) / (x-a)^(S n)) = 0.
Abort.

Lemma lemma_20_17_c : ∀ f f' a n,
  (0 < n)%nat -> nth_differentiable n f -> ⟦ der ⟧ f = f' ->
  ⟦ der ⟧ (λ x, f x - P(n,a,f) x) = (λ x, f' x - P(n-1,a,f') x).
Proof.
  intros f f' a n H1 H2 H3. apply derivative_minus; auto.
  unfold Taylor_polynomial.
  apply derivative_ext with (f1' := λ x, ∑ 0 n
    (λ k, ⟦ Der ^ k a ⟧ f / (fact k) * k * (x-a)^(k-1))).
  - intros x. rewrite sum_f_Si; try lia.
    rewrite (sum_f_reindex
      (λ k, ⟦ Der ^ k a ⟧ f / (fact k) * k * (x-a)^(k-1)) 1 n 1); try lia.
    replace (1-1)%nat with 0%nat by lia.
    cbn beta. simpl nth_derive_at at 1. simpl fact. simpl INR. simpl pow.
    rewrite Rmult_0_r, Rmult_0_l, Rplus_0_r.
    apply sum_f_equiv; try lia. intros k H4.
    replace (k+1)%nat with (S k) by lia.
    replace (S k - 1)%nat with k by lia.
    unfold nth_derive_at. rewrite nth_derive_succ, (derivative_imp_derive f f' H3).
    replace (fact (S k)) with (S k * fact k)%nat by reflexivity.
    rewrite mult_INR. field. split; [apply INR_fact_neq_0 | apply not_0_INR; lia].
  - apply derivative_sum; try lia. intros k H4. auto_diff; apply INR_fact_neq_0.
Qed.

Lemma lemma_20_17_d : ∀ n a f,
  (0 < n)%nat -> nth_differentiable_at n f a ->
  ⟦ lim a ⟧ (λ x, R(n,a,f) x / (x-a)^n) = 0.
Proof.
  intros n a f H1 H2. apply theorem_20_1; auto.
Qed.
