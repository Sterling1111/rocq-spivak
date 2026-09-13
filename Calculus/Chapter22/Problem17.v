From Calculus.Chapter22 Require Import Prelude Problem16.

Lemma lemma_22_17_a : ∀ a L,
  ⟦ lim ⟧ (λ n, a (n + 1)%nat - a n) = L ->
  ⟦ lim ⟧ (λ n, a n / n) = L.
Proof.
  intros a L H1.
  set (d := λ n, a n-a (n-1)%nat).
  assert (H2 : ⟦ lim ⟧ d = L).
  { intros ε H2. destruct (H1 ε H2) as [N H3].
    exists (Rmax 1 (N+1)). intros n H4.
    assert (H5 : (0 < n)%nat) by (apply INR_lt; solve_R).
    specialize (H3 (n-1)%nat).
    replace (n-1+1)%nat with n in H3 by lia.
    apply H3. rewrite minus_INR; [simpl; solve_R | lia]. }
  pose proof (lemma_22_16 d L H2) as H3.
  assert (H4 : ∀ n, (0 < n)%nat -> ∑ 1 n d = a n-a 0%nat).
  { intros n H4. induction n as [| n IH]; [lia |].
    destruct n as [| n].
    - rewrite sum_f_n_n. unfold d. reflexivity.
    - rewrite sum_f_i_Sn_f; [| lia]. rewrite IH; [| lia].
      unfold d. replace (S (S n)-1)%nat with (S n) by lia. ring. }
  assert (H5 : ⟦ lim ⟧ (λ (n : ℕ), a 0%nat * (1/n)) = 0).
  { replace 0 with (a 0%nat*0) by ring.
    apply limit_of_sequence_mul_const. apply theorem_34_12. }
  pose proof (limit_of_sequence_add _ _ _ _ H3 H5) as H6.
  rewrite Rplus_0_r in H6.
  intros ε H7. destruct (H6 ε H7) as [N H8].
  exists (Rmax N 1). intros n H9. specialize (H8 n ltac:(solve_R)).
  rewrite H4 in H8; [| apply INR_lt; solve_R].
  replace ((a n-a 0%nat)/n+a 0%nat*(1/n)) with (a n/n) in H8
    by (unfold Rdiv; ring). exact H8.
Qed.

Lemma lemma_22_17_b : ∀ f L,
  continuous f ->
  ⟦ lim ∞ ⟧ (λ x, f (x + 1) - f x) = L ->
  ⟦ lim ∞ ⟧ (λ x, f x / x) = L.
Abort.
