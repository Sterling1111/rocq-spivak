From Calculus.Chapter8 Require Import Prelude.

Lemma lemma_8_2_a : ∀ A sup_A sup_B,
  let B := (λ x, -x ∈ A) in
  is_lub A sup_A ->
  is_lub B sup_B ->
  A ≠ ∅ ->
  has_lower_bound A ->
  B ≠ ∅ /\ has_upper_bound B /\ is_glb A (-sup_B).
Proof.
  intros A sup_A sup_B B H1 H2 H3 H4.
  repeat split.
  - apply not_Empty_In in H3 as [x H5].
    apply not_Empty_In. exists (-x). unfold B, Ensembles.In. replace (- - x) with x by lra. exact H5.
  - destruct H4 as [x H5].
    exists (-x). intros y H6. unfold B, Ensembles.In in H6.
    specialize (H5 (-y) H6). lra.
  - intros x H5. destruct H2 as [H6 _].
    assert (H7: -x ∈ B). { unfold B, Ensembles.In. replace (- - x) with x by lra. exact H5. }
    specialize (H6 (-x) H7). lra.
  - intros x H5. destruct H2 as [_ H6].
    assert (H7: is_upper_bound B (-x)).
    { intros y H8. unfold B, Ensembles.In in H8. specialize (H5 (-y) H8). lra. }
    specialize (H6 (-x) H7). lra.
Qed.

Lemma lemma_8_2_b : ∀ A sup_A sup_B,
  let B := (λ x, is_lower_bound A x) in
  is_lub A sup_A ->
  is_lub B sup_B ->
  A ≠ ∅ ->
  has_lower_bound A ->
  B ≠ ∅ /\ has_upper_bound B /\ is_glb A sup_B.
Proof.
  intros A sup_A sup_B B H1 H2 H3 H4.
  repeat split.
  - apply not_Empty_In. destruct H4 as [x H5]. exists x. exact H5.
  - apply not_Empty_In in H3 as [x H5].
    exists x. intros y H6. unfold B, Ensembles.In in H6. specialize (H6 x H5). lra.
  - intros x H5. destruct H2 as [_ H6].
    assert (H7: is_upper_bound B x).
    { intros y H8. unfold B, Ensembles.In in H8. specialize (H8 x H5). lra. }
    specialize (H6 x H7). lra.
  - intros x H5. destruct H2 as [H6 _].
    specialize (H6 x H5). lra.
Qed.