From Calculus.Chapter22 Require Import Prelude.
From Lib Require Import StdlibCompat.
From Stdlib Require Import Reals.SeqSeries.

Lemma lemma_22_16 : ∀ a L,
  ⟦ lim ⟧ a = L ->
  ⟦ lim ⟧ (λ n, (∑ 1 n a) / n) = L.
Proof.
  intros a L H1.
  assert (H2 : Un_cv (λ n, a (S n)) L).
  { apply limit_s_compat. intros ε H2. destruct (H1 ε H2) as [N H3].
    exists N. intros n H4. apply H3. rewrite S_INR. lra. }
  pose proof (Cesaro_1 _ _ H2) as H3. apply limit_s_compat in H3.
  intros ε H4. destruct (H3 ε H4) as [N H5].
  exists (Rmax N 1). intros n H6. specialize (H5 n ltac:(solve_R)).
  assert (H7 : (0 < n)%nat) by (apply INR_lt; solve_R).
  unfold sum_f. replace (n-1)%nat with (Nat.pred n) by lia.
  replace (λ x, a (x+1)%nat) with (λ x, a (S x)) by
    (extensionality x; f_equal; lia). exact H5.
Qed.
