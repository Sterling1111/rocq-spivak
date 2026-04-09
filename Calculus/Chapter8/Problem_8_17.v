From Calculus.Chapter8 Require Import Prelude.

Lemma lemma_8_17_a : ∀ a,
  let A := (fun x => x < a) in
  (∀ x y, x ∈ A -> y < x -> y ∈ A) /\
  (A ≠ ∅) /\
  (A ≠ (fun x => True)) /\
  (∀ x, x ∈ A -> ∃ x', x' ∈ A /\ x < x').
Proof.
  intros a A. repeat split.
  - intros x y H1 H2. unfold A in *; solve_R.
  - apply not_Empty_In. exists (a - 1); unfold A; solve_R.
  - intros H1. assert (H2 : a ∈ A). { rewrite H1. exact I. }
    unfold A in *; solve_R.
  - intros x H1. exists ((x + a) / 2). unfold A in *; solve_R.
Qed.

Lemma lemma_8_17_b : ∀ A,
  (∀ x y, x ∈ A -> y < x -> y ∈ A) ->
  A ≠ ∅ ->
  A ≠ (fun x => True) ->
  (∀ x, x ∈ A -> ∃ x', x' ∈ A /\ x < x') ->
  has_upper_bound A ->
  ∀ sup_A, is_lub A sup_A ->
  (∀ x, x ∈ A <-> x < sup_A).
Proof.
  intros A H1 H2 H3 H4 H5 sup_A [H6 H7] x. split.
  - intros H8. assert (H9 : x <= sup_A) by exact (H6 x H8).
    pose proof classic (x = sup_A) as [H10 | H10]; [|lra].
    subst x. destruct (H4 sup_A H8) as [x' [H11 H12]].
    assert (H13 : x' <= sup_A) by exact (H6 x' H11). lra.
  - intros H8. pose proof classic (x ∈ A) as [H9 | H9]; auto.
    exfalso. assert (H10 : is_upper_bound A x).
    { intros y H11. pose proof classic (y <= x) as [H12 | H12]; auto.
      apply Rnot_le_lt in H12.
      assert (H13 : x ∈ A) by exact (H1 y x H11 H12).
      contradiction. }
    specialize (H7 x H10). lra.
Qed.