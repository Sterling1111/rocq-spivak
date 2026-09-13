From Calculus.Chapter8 Require Import Prelude.

Lemma lemma_8_1_i :
  let A := (λ x : ℝ, ∃ n : ℕ, n ≠ 0%nat /\ x = 1 / n) in
  is_lub A 1 /\ 1 ∈ A /\
  is_glb A 0 /\ 0 ∉ A.
Proof.
  intros A.
  assert (H1 : 1 ∈ A) by (exists 1%nat; split; [lia | simpl; field]).
  repeat split.
  - intros x [n [H2 H3]]. subst. solve_R.
  - intros M H2. apply H2, H1.
  - exact H1.
  - intros x [n [H2 H3]]. subst. solve_R.
  - intros m H2. apply Rle_ge, Rnot_lt_le. intros H3.
    destruct (exists_nat_gt_inv_scale 0 1 m ltac:(lra) H3) as [n [H4 H5]].
    specialize (H2 (1 / n) ltac:(exists n; split; [lia | reflexivity])).
    rewrite Rminus_0_r in H5. lra.
  - intros [n [H2 H3]]. solve_R.
Qed.

Lemma lemma_8_1_ii :
  let A := (λ x : ℝ, ∃ n : ℤ, n ≠ 0%Z /\ x = 1 / n) in
  is_lub A 1 /\ 1 ∈ A /\
  is_glb A (-1) /\ (-1) ∈ A.
Proof.
  intros A.
  assert (H1 : 1 ∈ A) by (exists 1%Z; split; [lia | simpl; field]).
  assert (H2 : -1 ∈ A) by (exists (-1)%Z; split; [lia | simpl; field]).
  repeat split.
  - intros x [n [H3 H4]]. subst. solve_R.
  - intros M H3. apply H3, H1.
  - exact H1.
  - intros x [n [H3 H4]]. subst. apply Rle_ge.
    assert (H5 : (-n ≠ 0)%Z) by lia.
    assert (H6 : 1 / (-n)%Z <= 1) by solve_R.
    rewrite opp_IZR in H6. rewrite Rdiv_opp_r in H6. lra.
  - intros m H3. apply H3, H2.
  - exact H2.
Qed.

Lemma lemma_8_1_iii :
  let A := (λ x : ℝ,
    x = 0 \/ ∃ n : ℕ, n ≠ 0%nat /\ x = 1 / n) in
  is_lub A 1 /\ 1 ∈ A /\
  is_glb A 0 /\ 0 ∈ A.
Proof.
  intros A.
  assert (H1 : 1 ∈ A) by (right; exists 1%nat; split; [lia | simpl; field]).
  assert (H2 : 0 ∈ A) by (left; reflexivity).
  repeat split.
  - intros x [H3 | [n [H3 H4]]]; subst; solve_R.
  - intros M H3. apply H3, H1.
  - exact H1.
  - intros x [H3 | [n [H3 H4]]]; subst; solve_R.
  - intros m H3. apply H3, H2.
  - exact H2.
Qed.

Lemma lemma_8_1_iv :
  let A := (λ x : ℝ,
    0 ≤ x /\ x ≤ √2 /\ rational x) in
  is_lub A (√2) /\ (√2) ∉ A /\
  is_glb A 0 /\ 0 ∈ A.
Proof.
  intros A.
  pose proof sqrt_lt_R0 2 ltac:(lra) as H1.
  assert (H2 : 0 ∈ A).
  { repeat split; try lra. exists 0%Z, 1%Z. simpl. field. }
  repeat split.
  - intros x [H3 [H4 H5]]. exact H4.
  - intros M H3. apply Rnot_lt_le. intros H4.
    destruct (exists_rational_between (Rmax 0 M) (√2) ltac:(solve_R)) as [x [H5 H6]].
    assert (H7 : x ∈ A) by (repeat split; solve_R).
    specialize (H3 x H7). solve_R.
  - intros [H3 [H4 H5]]. exact (sqrt_2_irrational H5).
  - intros x [H3 [H4 H5]]. lra.
  - intros m H3. apply H3, H2.
  - unfold A, Ensembles.In in H2; tauto.
  - unfold A, Ensembles.In in H2; tauto.
  - unfold A, Ensembles.In in H2; tauto.
Qed.

Lemma lemma_8_1_v :
  let A := (λ x : ℝ, x * x + x + 1 ≥ 0) in
  (∀ r : ℝ, ¬ is_lub A r) /\
  (∀ r : ℝ, ¬ is_glb A r).
Proof.
  intros A.
  assert (H1 : ∀ x, x ∈ A).
  { intros x. unfold A, Ensembles.In. pose proof Rle_0_sqr (x + 1 / 2); nra. }
  split; intros r [H2 H3].
  - specialize (H2 (r + 1) (H1 (r + 1))). lra.
  - specialize (H2 (r - 1) (H1 (r - 1))). lra.
Qed.

Lemma lemma_8_1_vi :
  let A := (λ x : ℝ, x * x + x - 1 < 0) in
  is_lub A ((-1 + √5) / 2) /\
  ((-1 + √5) / 2) ∉ A /\
  is_glb A ((-1 - √5) / 2) /\
  ((-1 - √5) / 2) ∉ A.
Proof. Abort.

Lemma lemma_8_1_vii :
  let A := (λ x : ℝ,
    x < 0 /\ x * x + x - 1 < 0) in
  is_lub A 0 /\ 0 ∉ A /\
  is_glb A ((-1 - √5) / 2) /\
  ((-1 - √5) / 2) ∉ A.
Proof.
  intros A.
  pose proof sqrt_sqrt 5 ltac:(lra) as H1.
  pose proof sqrt_pos 5 as H2.
  set (l := (-1 - √5) / 2).
  assert (H3 : l < 0) by (unfold l; lra).
  assert (H4 : ∀ x, x ∈ A <-> l < x < 0).
  { intros x. unfold A, Ensembles.In. split; intros [H4 H5].
    - split; [| exact H4]. apply Rnot_le_lt. intros H6.
      pose proof Rmult_le_pos (l - x) ((-1 + √5) / 2 - x)
        ltac:(lra) ltac:(nra) as H7.
      unfold l in H7. nra.
    - split; [exact H5 |].
      pose proof Rmult_lt_0_compat (x - l) ((-1 + √5) / 2 - x)
        ltac:(lra) ltac:(nra) as H6.
      unfold l in H6. nra. }
  repeat split.
  - intros x H5. apply H4 in H5. lra.
  - intros M H5. apply Rnot_lt_le. intros H6.
    assert (H7 : (Rmax l M / 2) ∈ A) by (apply H4; solve_R).
    specialize (H5 _ H7). solve_R.
  - intros H5. apply H4 in H5. lra.
  - intros x H5. apply H4 in H5. fold l. lra.
  - intros m H5. fold l. apply Rle_ge, Rnot_lt_le. intros H6.
    assert (H7 : ((l + Rmin m 0) / 2) ∈ A) by (apply H4; solve_R).
    specialize (H5 _ H7). solve_R.
  - fold l. intros H5. apply H4 in H5. lra.
Qed.

Lemma lemma_8_1_viii :
  let A := (λ x : ℝ,
    ∃ n : ℕ,
      n ≠ 0%nat /\
      x = 1 / n + (-1 : ℝ) ^ n) in
  is_lub A (3 / 2) /\ (3 / 2) ∈ A /\
  is_glb A (-1) /\ (-1) ∉ A.
Proof. Abort.
