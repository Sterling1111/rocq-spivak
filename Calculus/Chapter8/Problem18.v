From Calculus.Chapter8 Require Import Prelude.

Definition almost_upper_bound (A : Ensemble ℝ) (x : ℝ) :=
  Finite_set (λ y, y ∈ A /\ y >= x).

Definition almost_lower_bound (A : Ensemble ℝ) (x : ℝ) :=
  Finite_set (λ y, y ∈ A /\ y <= x).

Definition lim_sup (A : Ensemble ℝ) (l : ℝ) :=
  is_glb (λ x, almost_upper_bound A x) l.

Lemma lemma_8_18_b_1 : ∀ A,
  Infinite_set A -> has_upper_bound A -> has_lower_bound A ->
  (λ x, almost_upper_bound A x) ≠ ∅.
Proof.
  intros A H1 [M H2] H3.
  apply not_Empty_In. exists (M + 1).
  unfold almost_upper_bound, Finite_set. exists [].
  rewrite list_to_ensemble_nil. apply set_equal_def. intros x. split.
  - intros H4. inversion H4.
  - intros [H4 H5]. specialize (H2 x H4). lra.
Qed.

Lemma lemma_8_18_b_2 : ∀ A,
  Infinite_set A -> has_upper_bound A -> has_lower_bound A ->
  has_lower_bound (λ x, almost_upper_bound A x).
Proof.
  intros A H1 H2 [m H3]. exists m.
  intros x H4. apply Rle_ge, Rnot_lt_le. intros H5.
  apply H1. change (Finite_set (λ y, y ∈ A /\ y >= x)) in H4.
  assert (H6 : (λ y, y ∈ A /\ y >= x) = A).
  { apply set_equal_def. intros y. split.
    - intros [H6 H7]. exact H6.
    - intros H6. split; auto. specialize (H3 y H6). lra. }
  rewrite H6 in H4. exact H4.
Qed.

Lemma lemma_8_18_c : ∀ A l,
  Infinite_set A -> has_upper_bound A -> has_lower_bound A ->
  lim_sup A l -> True.
Proof. Abort.
