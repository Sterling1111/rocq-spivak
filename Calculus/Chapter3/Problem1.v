From Calculus.Chapter3 Require Export Prelude.

Local Definition f (x : R) := 1 / (1 + x).

Lemma lemma_3_1_i_domain : ∀ x,
  (1 + x <> 0 /\ 1 + f x <> 0) <-> (x <> -1 /\ x <> -2).
Proof.
  intros x. unfold f. split.
  - intros [H1 H2]. split; intro H3; subst; solve_R.
  - intros [H1 H2]. split; [lra |]. intro H3.
    assert (H4 : 1 + x <> 0) by lra.
    assert (H5 : 1 / (1 + x) * (1 + x) = 1) by (field; lra). nra.
Qed.

Lemma lemma_3_1_i : ∀ x, x <> -1 -> x <> -2 ->
  f (f x) = (1 + x) / (2 + x).
Proof.
  intros x H1 H2. unfold f. field; lra.
Qed.

Lemma lemma_3_1_ii : ∀ x, x <> 0 -> x <> -1 ->
  f (1 / x) = x / (x + 1).
Proof.
  intros x H1 H2. unfold f. field; lra.
Qed.

Lemma lemma_3_1_iii : ∀ c x, c * x <> -1 ->
  f (c * x) = 1 / (1 + c * x).
Proof.
  reflexivity.
Qed.

Lemma lemma_3_1_iv : ∀ x y, x + y <> -1 ->
  f (x + y) = 1 / (1 + x + y).
Proof.
  intros x y H1. unfold f. f_equal. lra.
Qed.

Lemma lemma_3_1_v : ∀ x y, x <> -1 -> y <> -1 ->
  f x + f y = (2 + x + y) / ((1 + x) * (1 + y)).
Proof.
  intros x y H1 H2. unfold f. field; lra.
Qed.

Lemma lemma_3_1_vi : ∀ c, ∃ x,
  x <> -1 /\ c * x <> -1 /\ f (c * x) = f x.
Proof.
  intros c. exists 0. rewrite Rmult_0_r. repeat split; try lra.
Qed.

Lemma lemma_3_1_vii : ∀ c,
  (∃ x y, x <> y /\ x <> -1 /\ y <> -1 /\
    c * x <> -1 /\ c * y <> -1 /\
    f (c * x) = f x /\ f (c * y) = f y) <-> c = 1.
Proof.
  intros c. split.
  - intros [x [y [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]]]].
    unfold f in H6, H7.
    assert (H8 : c * x = x).
    { apply (f_equal Rinv) in H6. unfold Rdiv in H6.
      repeat rewrite Rmult_1_l in H6. rewrite !Rinv_inv in H6. nra. }
    assert (H9 : c * y = y).
    { apply (f_equal Rinv) in H7. unfold Rdiv in H7.
      repeat rewrite Rmult_1_l in H7. rewrite !Rinv_inv in H7. nra. }
    nra.
  - intros H1. subst c. exists 0, 1. repeat split; try (f_equal; ring); lra.
Qed.
