From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_4_a : ∀ a b L,
  cauchy_sequence a ->
  subsequence b a ->
  ⟦ lim ⟧ b = L ->
  ⟦ lim ⟧ a = L.
Proof.
  intros a b L H1 [f [H2 H3]] H4 ε H5.
  destruct (H1 (ε/2) ltac:(lra)) as [N1 H6].
  destruct (H4 (ε/2) ltac:(lra)) as [N2 H7].
  assert (H8 : ∀ n, (n <= f n)%nat).
  { intros n. induction n as [| n IH]; [lia |].
    pose proof (H2 n (S n) ltac:(solve_R)) as H8.
    apply INR_lt in H8. lia. }
  exists (Rmax N1 N2). intros n H9.
  destruct (INR_unbounded (Rmax N1 N2)) as [k H10].
  pose proof (le_INR _ _ (H8 k)) as H11.
  specialize (H6 n (f k) ltac:(solve_R) ltac:(solve_R)).
  specialize (H7 k ltac:(solve_R)). rewrite H3 in H7. solve_R.
Qed.

Lemma lemma_22_4_b : ∀ a b L,
  ⟦ lim ⟧ a = L ->
  subsequence b a ->
  ⟦ lim ⟧ b = L.
Proof.
  intros a b L H1 [f [H2 H3]] ε H4.
  destruct (H1 ε H4) as [N H5].
  assert (H6 : ∀ n, (n <= f n)%nat).
  { intros n. induction n as [| n IH]; [lia |].
    pose proof (H2 n (S n) ltac:(solve_R)) as H6.
    apply INR_lt in H6. lia. }
  exists N. intros n H7. rewrite H3. apply H5.
  pose proof (le_INR _ _ (H6 n)). lra.
Qed.
