From Calculus.Chapter1 Require Import Prelude.

Lemma lemma_1_12_i : ∀ x y,
  |x * y| = |x| * |y|.
Proof.
  solve_R.
Qed.

Lemma lemma_1_12_ii : ∀ x,
  |1 / x| = 1 / |x|.
Proof.
  intros x. pose proof Rinv_neg x. pose proof Rinv_pos x. 
  solve_abs.
  unfold Rdiv. destruct r0. nra.
  rewrite H1. unfold Rdiv. rewrite Rinv_0. nra.
Qed.

Lemma lemma_1_12_iii : ∀ x y,
  y <> 0 -> |x| / |y| = |x / y|.
Proof.
  intros x y H1. pose proof Rinv_neg y. pose proof Rinv_pos y.
  solve_abs. destruct r; nra.
Qed.

Lemma lemma_1_12_iv : ∀ x y,
  |x - y| <= |x| + |y|.
Proof.
  solve_R.
Qed.

Lemma lemma_1_12_v : ∀ x y,
  |x| - |y| <= |x - y|.
Proof.
  solve_R.
Qed.

Lemma lemma_1_12_vi : ∀ x y,
  |(|x| - |y|)| <= |x - y|.
Proof.
  solve_R.
Qed.

Lemma lemma_1_12_vii : ∀ x y z,
  |x + y + z| <= |x| + |y| + |z|.
Proof.
  solve_R.
Qed.

Lemma lemma_1_12_viii' : ∀ x y z,
  |x + y + z| = |x| + |y| + |z| <-> (x >= 0 /\ y >= 0 /\ z >= 0) \/ (x <= 0 /\ y <= 0 /\ z <= 0).
Proof.
  solve_R.
Qed.