From Calculus.Chapter3 Require Export Prelude.

Lemma lemma_3_3_i : ∀ x, 0 <= 1 - x^2 <-> -1 <= x <= 1.
Proof.
  intros x. split; nra.
Qed.

Lemma lemma_3_3_ii : ∀ x,
  (0 <= 1 - x^2 /\ 0 <= 1 - sqrt (1 - x^2)) <-> -1 <= x <= 1.
Proof.
  intros x. pose proof (sqrt_pos (1 - x^2)). split; intros H1; solve_R.
Qed.

Lemma lemma_3_3_iii : ∀ x,
  (x - 1 <> 0 /\ x - 2 <> 0) <-> (x <> 1 /\ x <> 2).
Proof.
  intros x. split; intros [H1 H2]; split; lra.
Qed.

Lemma lemma_3_3_iv : ∀ x,
  (0 <= 1 - x^2 /\ 0 <= x^2 - 1) <-> x = -1 \/ x = 1.
Proof.
  intros x. split; intros H1; [nra | destruct H1; subst; split; nra].
Qed.

Lemma lemma_3_3_v : ~ ∃ x : R, 0 <= 1 - x /\ 0 <= x - 2.
Proof.
  intros [x [H1 H2]]. lra.
Qed.
