From Calculus.Chapter5 Require Import Prelude.
From Calculus.Chapter5 Require Import Problem10.

Lemma lemma_5_17_a : ∀ l,
  ¬ ⟦ lim 0 ⟧ (λ x, 1 / x) = l.
Proof.
  intros l H1.
  specialize (H1 1 ltac:(solve_R)) as [δ [H2 H3]].
  set (x := Rmin (δ / 2) (1 / (|l| + 2))).
  assert (x > 0) as H4.
  {
    unfold x.
    pose proof Rdiv_pos_pos δ 2 H2 ltac:(lra) as H4.
    pose proof Rdiv_pos_pos 1 ((|l| + 2)) ltac:(lra) ltac:(solve_R) as H5.
    solve_R.
  }
  assert (H5 : 0 < |(x - 0)| < δ) by (unfold x in *; solve_R).
  specialize (H3 x H5) as H6.
  assert (H7 : 1 / x ≥ |l| + 2).
  {
    replace (1 / x) with (/ x) by solve_R.
    replace (|l| + 2) with (/ (1 / (|l| + 2))) by solve_R.
    apply Rle_ge, Rinv_le_contravar; auto.
    unfold x; apply Rmin_r.
  }
  solve_R.
Qed.

Lemma lemma_5_17_b : ∀ l,
  ¬ ⟦ lim 1 ⟧ (λ x, 1 / (x - 1)) = l.
Proof.
  intros l1 H1.
  apply (lemma_5_17_a l1).
  intros ε H2.
  specialize (H1 ε H2) as [δ [H3 H4]].
  exists δ. split; auto.
  intros x H5.
  specialize (H4 (x + 1) ltac:(solve_R)).
  rewrite Rplus_minus_r in H4.
  exact H4.
Qed.