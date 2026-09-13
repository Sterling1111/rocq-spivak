From Calculus.Chapter7 Require Import Prelude.

Lemma lemma_7_13_b : ∀ f,
  (∀ a b c, a < b ->
   (f a < c < f b \/ f b < c < f a) -> ∃ x, x ∈ [a, b] /\ f x = c) ->
  (∀ y, ∃! x, f x = y) ->
  continuous f.
Proof.
  intros f H1 H2.
  assert (H3 : ∀ x y, f x = f y -> x = y).
  {
    intros x y H3. destruct (H2 (f x)) as [z [H4 H5]].
    pose proof (H5 x eq_refl) as H6.
    pose proof (H5 y ltac:(lra)) as H7. congruence.
  }
  assert (H4 : ∀ a x c,
    (f a < c < f x \/ f x < c < f a) ->
    ∃ y, y ∈ [Rmin a x, Rmax a x] /\ f y = c).
  {
    intros a x c H4. destruct (Rtotal_order a x) as [H5 | [H5 | H5]].
    - rewrite Rmin_left, Rmax_right by lra. apply H1; auto.
    - subst x. lra.
    - rewrite Rmin_right, Rmax_left by lra. apply H1; auto. tauto.
  }
  intros a ε H5.
  destruct (H2 (f a + ε / 2)) as [u [H6 H7]].
  destruct (H2 (f a - ε / 2)) as [v [H8 H9]].
  assert (H10 : u <> a /\ v <> a) by (split; intros H10; subst; lra).
  exists (Rmin (|u - a|) (|v - a|)). split; [solve_R |].
  intros x H11. destruct (Rlt_dec (|f x - f a|) ε) as [H12 | H12]; auto.
  assert (H13 : f x >= f a + ε \/ f x <= f a - ε) by solve_R.
  destruct H13 as [H13 | H13].
  - destruct (H4 a x (f a + ε / 2) ltac:(left; lra)) as [y [H14 H15]].
    assert (H16 : y = u) by (apply H3; lra). subst y. solve_R.
  - destruct (H4 a x (f a - ε / 2) ltac:(right; lra)) as [y [H14 H15]].
    assert (H16 : y = v) by (apply H3; lra). subst y. solve_R.
Qed.
