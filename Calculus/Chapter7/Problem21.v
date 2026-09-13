From Calculus.Chapter7 Require Import Prelude.

Definition exactly_twice (f : R -> R) (y : R) :=
  ∃ x1 x2, x1 <> x2 /\ f x1 = y /\ f x2 = y /\
  ∀ x, f x = y -> x = x1 \/ x = x2.

Definition takes_0_or_2 (f : R -> R) (y : R) :=
  (∀ x, f x <> y) \/ exactly_twice f y.

Local Lemma takes_0_or_2_neg : ∀ f,
  (∀ y, takes_0_or_2 f y) -> ∀ y, takes_0_or_2 (λ x, - f x) y.
Proof.
  intros f H1 y. destruct (H1 (-y)) as [H2 | [a [b [H2 [H3 [H4 H5]]]]]].
  - left. intros x H3. apply (H2 x). lra.
  - right. exists a, b. repeat split; auto; try lra.
    intros x H6. apply H5. lra.
Qed.

Local Lemma takes_0_or_2_three_crossings : ∀ f a b c d t,
  continuous f -> (∀ y, takes_0_or_2 f y) ->
  a < b -> b < c -> c < d ->
  f a < t < f b -> f c < t < f d -> False.
Proof.
  intros f a b c d t H1 H2 H3 H4 H5 H6 H7.
  destruct (intermediate_value_theorem f a b t H3
    ltac:(apply continuous_imp_continuous_on; auto) ltac:(lra)) as [x [H8 H9]].
  destruct (intermediate_value_theorem_decreasing f b c t H4
    ltac:(apply continuous_imp_continuous_on; auto) ltac:(lra)) as [y [H10 H11]].
  destruct (intermediate_value_theorem f c d t H5
    ltac:(apply continuous_imp_continuous_on; auto) ltac:(lra)) as [z [H12 H13]].
  assert (H14 : a < x < b).
  { assert (x <> a /\ x <> b) by (split; intros H14; subst x; lra). solve_R. }
  assert (H15 : b < y < c).
  { assert (y <> b /\ y <> c) by (split; intros H15; subst y; lra). solve_R. }
  assert (H16 : c < z < d).
  { assert (z <> c /\ z <> d) by (split; intros H16; subst z; lra). solve_R. }
  destruct (H2 t) as [H17 | [u [v [H17 [H18 [H19 H20]]]]]].
  - apply (H17 x). exact H9.
  - destruct (H20 x H9), (H20 y H11), (H20 z H13); lra.
Qed.

Local Lemma takes_0_or_2_attains_maximum : ∀ f a b c,
  continuous f -> (∀ y, takes_0_or_2 f y) ->
  a < c < b -> f a = f b -> f a < f c ->
  ∃ y, ∀ x, f x <= f y.
Proof.
  intros f a b c H1 H2 H3 H4 H5.
  assert (H6 : ∀ x, x < a \/ b < x -> f x <= f a).
  {
    intros x H6. destruct (Rle_dec (f x) (f a)) as [H7 | H7]; auto.
    exfalso. set (t := (f a + Rmin (f x) (f c)) / 2).
    assert (H8 : f a < t /\ t < f x /\ t < f c) by (unfold t; solve_R).
    destruct H6 as [H6 | H6].
    - apply (takes_0_or_2_three_crossings (λ x, - f x) x a c b (-t));
        try lra; [apply continuous_neg; auto | apply takes_0_or_2_neg; auto].
    - apply (takes_0_or_2_three_crossings f a c b x t); auto; lra.
  }
  destruct (continuous_on_interval_attains_maximum f a b ltac:(lra)
    ltac:(apply continuous_imp_continuous_on; auto)) as [y [H7 H8]].
  exists y. intros x. destruct (Rle_dec a x) as [H9 | H9].
  - destruct (Rle_dec x b) as [H10 | H10].
    + specialize (H8 x ltac:(solve_R)). lra.
    + pose proof (H6 x ltac:(right; lra)) as H11.
      pose proof (H8 a ltac:(solve_R)) as H12. lra.
  - pose proof (H6 x ltac:(left; lra)) as H10.
    pose proof (H8 a ltac:(solve_R)) as H11. lra.
Qed.

Local Lemma takes_0_or_2_extremum : ∀ f,
  continuous f -> (∀ y, takes_0_or_2 f y) ->
  ∃ y, (∀ x, f x <= f y) \/ (∀ x, f y <= f x).
Proof.
  intros f H1 H2.
  destruct (H2 (f 0)) as [H3 | [u [v [H3 [H4 [H5 H6]]]]]].
  { exfalso. apply (H3 0). reflexivity. }
  set (a := Rmin u v). set (b := Rmax u v). set (c := (a + b) / 2).
  assert (H7 : a < c < b) by (unfold c, a, b; solve_R).
  assert (H8 : f a = f 0 /\ f b = f 0).
  { unfold a, b, Rmin, Rmax. destruct (Rle_dec u v); auto. }
  assert (H9 : f c <> f a).
  {
    intros H9. destruct (H6 c ltac:(lra)) as [H10 | H10];
      unfold c, a, b in *; solve_R.
  }
  destruct (Rlt_dec (f a) (f c)) as [H10 | H10].
  - destruct (takes_0_or_2_attains_maximum f a b c H1 H2 H7 ltac:(lra) H10) as [y H11].
    exists y. auto.
  - destruct (takes_0_or_2_attains_maximum (λ x, - f x) a b c
      ltac:(apply continuous_neg; auto) (takes_0_or_2_neg f H2) H7 ltac:(lra) ltac:(lra)) as [y H11].
    exists y. right. intros x. specialize (H11 x). lra.
Qed.

Local Lemma takes_0_or_2_no_maximum : ∀ f,
  continuous f -> (∀ y, takes_0_or_2 f y) ->
  (∃ y, ∀ x, f x <= f y) -> False.
Proof.
  intros f H1 H2 [y H3].
  destruct (H2 (f y)) as [H4 | [u [v [H4 [H5 [H6 H7]]]]]].
  { apply (H4 y). reflexivity. }
  set (a := Rmin u v). set (b := Rmax u v). set (c := (a + b) / 2).
  assert (H8 : a < c < b) by (unfold c, a, b; solve_R).
  assert (H9 : f a = f y /\ f b = f y).
  { unfold a, b, Rmin, Rmax. destruct (Rle_dec u v); auto. }
  assert (H10 : f (a - 1) < f y /\ f c < f y).
  {
    pose proof (H3 (a - 1)) as H10. pose proof (H3 c) as H11.
    assert (H12 : f (a - 1) <> f y).
    { intros H12. destruct (H7 (a - 1) H12); unfold a in *; solve_R. }
    assert (H13 : f c <> f y).
    { intros H13. destruct (H7 c H13); unfold c, a, b in *; solve_R. }
    lra.
  }
  set (t := (Rmax (f (a - 1)) (f c) + f y) / 2).
  apply (takes_0_or_2_three_crossings f (a - 1) a c b t); auto; unfold t; solve_R.
Qed.

Lemma lemma_7_21_a : ~ (∃ f,
  continuous f /\ ∀ y, exactly_twice f y).
Proof.
  intros [f [H1 H2]].
  assert (H3 : ∀ y, takes_0_or_2 f y) by (intros y; right; auto).
  destruct (takes_0_or_2_extremum f H1 H3) as [y [H4 | H4]].
  - destruct (H2 (f y + 1)) as [x [z [H5 [H6 H7]]]].
    specialize (H4 x). lra.
  - destruct (H2 (f y - 1)) as [x [z [H5 [H6 H7]]]].
    specialize (H4 x). lra.
Qed.

Lemma lemma_7_21_b : ~ (∃ f,
  continuous f /\ ∀ y, takes_0_or_2 f y).
Proof.
  intros [f [H1 H2]].
  destruct (takes_0_or_2_extremum f H1 H2) as [y [H3 | H3]].
  - apply (takes_0_or_2_no_maximum f H1 H2). exists y. exact H3.
  - apply (takes_0_or_2_no_maximum (λ x, - f x)
      ltac:(apply continuous_neg; auto) (takes_0_or_2_neg f H2)).
    exists y. intros x. specialize (H3 x). lra.
Qed.
