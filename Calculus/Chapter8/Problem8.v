From Calculus.Chapter8 Require Import Prelude.

Section section_8_8.

Variable f : ℝ → ℝ.
Hypothesis H1 : ∀ a b, a < b -> f a < f b.

Lemma lemma_8_8_a : ∀ a,
  ∃ L1 L2,
    ⟦ lim a⁺ ⟧ f = L1 /\
    ⟦ lim a⁻ ⟧ f = L2.
Proof.
  intros a.
  set (A := λ y, ∃ x, x < a /\ y = f x).
  set (B := λ y, ∃ x, a < x /\ y = f x).
  assert (H2 : has_upper_bound A).
  { exists (f a). intros y [x [H2 H3]]. subst y. specialize (H1 x a H2). lra. }
  assert (H3 : A ≠ ∅).
  { apply not_Empty_In. exists (f (a - 1)), (a - 1). split; [lra | reflexivity]. }
  assert (H4 : has_lower_bound B).
  { exists (f a). intros y [x [H4 H5]]. subst y. specialize (H1 a x H4). lra. }
  assert (H5 : B ≠ ∅).
  { apply not_Empty_In. exists (f (a + 1)), (a + 1). split; [lra | reflexivity]. }
  destruct (completeness_upper_bound A H2 H3) as [L2 H6].
  destruct (completeness_lower_bound B H4 H5) as [L1 [H7 H8]].
  exists L1, L2. split.
  - intros ε H9.
    assert (H10 : ∃ y, y ∈ B /\ y < L1 + ε).
    { apply NNPP. intros H10.
      assert (H11 : is_lower_bound B (L1 + ε)).
      { intros y H11. apply Rle_ge, Rnot_lt_le. intros H12.
        apply H10. exists y. split; auto. }
      specialize (H8 (L1 + ε) H11). lra. }
    destruct H10 as [y [[x [H10 H11]] H12]]. subst y.
    exists (x - a). split; [lra |]. intros z H11.
    pose proof H1 z x ltac:(lra) as H13.
    specialize (H7 (f z) ltac:(exists z; split; [lra | reflexivity])). solve_R.
  - intros ε H9.
    destruct (exists_point_within_delta A L2 ε H6 H9) as [y [[x [H10 H11]] H12]].
    subst y. exists (a - x). split; [lra |]. intros z H11.
    pose proof H1 x z ltac:(lra) as H13.
    destruct H6 as [H6 _].
    specialize (H6 (f z) ltac:(exists z; split; [lra | reflexivity])). solve_R.
Qed.

Lemma lemma_8_8_b : ∀ a : ℝ,
  ¬ removably_discontinuous_at f a.
Proof.
  intros a [L [H2 H3]].
  destruct (Rlt_dec L (f a)) as [H4 | H4].
  - destruct (H2 (f a - L) ltac:(lra)) as [δ [H5 H6]].
    pose proof H1 a (a + δ / 2) ltac:(lra) as H7.
    specialize (H6 (a + δ / 2) ltac:(solve_R)). solve_R.
  - destruct (H2 (L - f a) ltac:(lra)) as [δ [H5 H6]].
    pose proof H1 (a - δ / 2) a ltac:(lra) as H7.
    specialize (H6 (a - δ / 2) ltac:(solve_R)). solve_R.
Qed.

Lemma lemma_8_8_c :
  (∀ a b c,
    a < b ->
    f a <= c <= f b ->
    ∃ x, x ∈ [a, b] /\ f x = c) ->
  continuous f.
Proof.
  intros H2 a ε H3.
  pose proof H1 (a - 1) a ltac:(lra) as H4.
  pose proof H1 a (a + 1) ltac:(lra) as H5.
  destruct (H2 (a - 1) a (Rmax (f (a - 1)) (f a - ε / 2))
    ltac:(lra) ltac:(solve_R)) as [x [H6 H7]].
  destruct (H2 a (a + 1) (Rmin (f (a + 1)) (f a + ε / 2))
    ltac:(lra) ltac:(solve_R)) as [y [H8 H9]].
  assert (H10 : x < a).
  { assert (H10 : f x < f a) by (rewrite H7; solve_R).
    assert (H11 : x <= a) by solve_R.
    destruct (Req_dec x a); [subst; lra | lra]. }
  assert (H11 : a < y).
  { assert (H11 : f a < f y) by (rewrite H9; solve_R).
    assert (H12 : a <= y) by solve_R.
    destruct (Req_dec y a); [subst; lra | lra]. }
  exists (Rmin (a - x) (y - a)). split; [solve_R |].
  intros z H12.
  pose proof H1 x z ltac:(solve_R) as H13.
  pose proof H1 z y ltac:(solve_R) as H14.
  rewrite H7 in H13. rewrite H9 in H14. solve_R.
Qed.

End section_8_8.