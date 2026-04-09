From Calculus.Chapter8 Require Import Prelude.

Lemma lemma_8_12_a : ∀ A B sup_A,
  A ≠ ∅ -> B ≠ ∅ -> (∀ x y, x ∈ A -> y ∈ B -> x <= y) ->
  is_lub A sup_A -> ∀ y, y ∈ B -> sup_A <= y.
Proof.
  intros A B sup_A H1 H2 H3 [H4 H5] y H6.
  apply H5.
  intros x H7.
  apply (H3 x y H7 H6).
Qed.

Lemma lemma_8_12_b : ∀ A B sup_A inf_B,
  A ≠ ∅ -> B ≠ ∅ -> (∀ x y, x ∈ A -> y ∈ B -> x <= y) ->
  is_lub A sup_A -> is_glb B inf_B -> sup_A <= inf_B.
Proof.
  intros A B sup_A inf_B H1 H2 H3 [H4 H5] [H6 H7].
  apply Rge_le, H7.
  intros y H8.
  apply Rle_ge, H5.
  intros x H9.
  apply (H3 x y H9 H8).
Qed.