From Calculus.Chapter22 Require Import Prelude.

Fixpoint row_position (n : ℕ) : ℕ * ℕ :=
  match n with
  | O => pair 1%nat 1%nat
  | S k => match row_position k with
           | pair m j => if Nat.ltb j m then pair m (S j) else pair (S m) 1%nat
           end
  end.

Definition integer_rows (n : ℕ) : ℝ :=
  snd (row_position (S n)).

Definition fraction_rows (n : ℕ) : ℝ :=
  match row_position n with pair m j => j / (S m) end.

Lemma lemma_22_3_a : ∀ (a : sequence) L,
  (∀ n, ∃ k : ℤ, a n = k) ->
  ⟦ lim ⟧ a = L ->
  ∃ N, ∀ n, (n >= N)%nat -> a n = L.
Proof.
  intros a L H1 H2.
  destruct (H2 (1/2) ltac:(lra)) as [N H3].
  destruct (INR_unbounded N) as [k H4].
  assert (H5 : ∀ n, (k <= n)%nat -> a n = a k).
  {
    intros n H5. pose proof (le_INR _ _ H5) as H6.
    pose proof (H3 n ltac:(lra)) as H7. pose proof (H3 k H4) as H8.
    destruct (H1 n) as [i H9]. destruct (H1 k) as [j H10].
    rewrite H9, H10 in *. assert (H11 : -1 < i-j < 1) by solve_R.
    assert (H12 : (j-1 < i < j+1)%Z).
    { split; apply lt_IZR; rewrite ?minus_IZR, ?plus_IZR; simpl; lra. }
    assert (i = j) by lia. subst i. reflexivity.
  }
  assert (H6 : L = a k).
  { apply limit_of_sequence_unique with (a := a); auto.
    intros ε H6. exists (k : ℝ). intros n H7.
    apply INR_lt in H7. rewrite H5; [solve_R | lia]. }
  exists k. intros n H7. rewrite H6. apply H5. lia.
Qed.

Lemma lemma_22_3_b : ∀ b L,
  subsequence b (λ n, (-1)^n) ->
  (⟦ lim ⟧ b = L <->
    (L = 1 \/ L = -1) /\
    ∃ N, ∀ n, (n >= N)%nat -> b n = L).
Proof.
  intros b L [f [H1 H2]].
  assert (H3 : ∀ n, b n = 1 \/ b n = -1).
  { intros n. rewrite H2. apply pow_neg1_n. }
  split.
  - intros H4. destruct (lemma_22_3_a b L) as [N H5]; auto.
    + intros n. destruct (H3 n) as [H5 | H5]; [exists 1%Z | exists (-1)%Z]; auto.
    + split; [rewrite <- (H5 N ltac:(lia)); apply H3 | exists N; auto].
  - intros [H4 [N H5]] ε H6. exists (N : ℝ). intros n H7.
    apply INR_lt in H7. rewrite H5; [solve_R | lia].
Qed.

Lemma lemma_22_3_b_limits : ∀ L,
  (∃ b, subsequence b (λ n, (-1)^n) /\ ⟦ lim ⟧ b = L) <->
  L = 1 \/ L = -1.
Proof.
  intros L. split.
  - intros [b [H1 H2]]. apply lemma_22_3_b in H2; tauto.
  - intros [H1 | H1]; subst L.
    + exists (λ _, 1). split; [| apply limit_of_const_sequence].
      exists (λ n, (2*n)%nat). split.
      * intros n m H1. repeat rewrite mult_INR. simpl. lra.
      * intros n. symmetry. apply pow_neg1_even. exists n. lia.
    + exists (λ _, -1). split; [| apply limit_of_const_sequence].
      exists (λ n, (2*n+1)%nat). split.
      * intros n m H1. repeat rewrite plus_INR. repeat rewrite mult_INR. simpl. lra.
      * intros n. symmetry. apply pow_neg1_odd. exists n. lia.
Qed.

Lemma lemma_22_3_c : ∀ b L,
  subsequence b integer_rows ->
  (⟦ lim ⟧ b = L <->
    ∃ k : ℕ, (0 < k)%nat /\ L = k /\
      ∃ N, ∀ n, (n >= N)%nat -> b n = k).
Abort.

Lemma lemma_22_3_c_limits : ∀ L,
  (∃ b, subsequence b integer_rows /\ ⟦ lim ⟧ b = L) <->
  ∃ k : ℕ, (0 < k)%nat /\ L = k.
Abort.

Lemma lemma_22_3_d : ∀ alpha,
  (∃ b, subsequence b fraction_rows /\ ⟦ lim ⟧ b = alpha) <->
  0 <= alpha <= 1.
Abort.
