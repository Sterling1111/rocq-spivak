From Calculus.Chapter8 Require Import Prelude.

Definition shadow_point (f : R -> R) (x : R) :=
  ∃ y, y > x /\ f y > f x.

Lemma lemma_8_20_a : ∀ f a b,
  continuous f ->
  (∀ x, a < x < b -> shadow_point f x) ->
  ~ shadow_point f a ->
  ~ shadow_point f b ->
  f a > f b ->
  ∀ x, a <= x <= b -> f x <= f a.
Proof. Abort.

Lemma lemma_8_20_b : ∀ f a b,
  continuous f ->
  a < b ->
  (∀ x, a < x < b -> shadow_point f x) ->
  ~ shadow_point f a ->
  ~ shadow_point f b ->
  f a = f b.
Proof.
  intros f a b H1 H2 H3 H4 H5.
  assert (H6 : ∀ x, a < x < b -> f x <= f b).
  { intros x H6. apply Rnot_lt_le. intros H7.
    set (A := λ y, x <= y <= b /\ f x <= f y).
    assert (H8 : has_upper_bound A).
    { exists b. intros y [[H8 H9] H10]. exact H9. }
    assert (H9 : A ≠ ∅).
    { apply not_Empty_In. exists x. repeat split; lra. }
    destruct (completeness_upper_bound A H8 H9) as [c H10].
    assert (H11 : x <= c <= b).
    { destruct H10 as [H10 H11]. split.
      - apply H10. repeat split; lra.
      - apply H11. intros y [[H12 H13] H14]. exact H13. }
    assert (H12 : f x <= f c).
    { apply Rnot_lt_le. intros H12.
      destruct (H1 c (f x - f c) ltac:(lra)) as [δ [H13 H14]].
      destruct (exists_point_within_delta A c δ H10 H13) as [y [H15 H16]].
      destruct H15 as [H15 H17].
      assert (H18 : y <> c) by (intros H18; subst; lra).
      specialize (H14 y ltac:(solve_R)). solve_R. }
    assert (H13 : c < b).
    { destruct (Req_dec c b); [subst; lra | lra]. }
    destruct (H3 c ltac:(lra)) as [y [H14 H15]].
    destruct (Rle_dec y b) as [H16 | H16].
    - destruct H10 as [H10 _].
      specialize (H10 y ltac:(repeat split; lra)). lra.
    - apply H5. exists y. split; lra. }
  assert (H7 : f a <= f b).
  { apply Rnot_lt_le. intros H7.
    destruct (H1 a (f a - f b) ltac:(lra)) as [δ [H8 H9]].
    set (x := a + Rmin δ (b - a) / 2).
    assert (H10 : a < x < b) by (unfold x; solve_R).
    specialize (H6 x H10).
    specialize (H9 x ltac:(unfold x; solve_R)). solve_R. }
  destruct (Rlt_dec (f a) (f b)) as [H8 | H8]; [| lra].
  exfalso. apply H4. exists b. split; lra.
Qed.
