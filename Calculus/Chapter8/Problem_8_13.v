From Calculus.Chapter8 Require Import Prelude.

Notation "A + B" := (fun z => ∃ x y, x ∈ A /\ y ∈ B /\ z = x + y) (at level 50, left associativity) : set_scope.

Lemma lemma_8_13 : ∀ A B sup_A sup_B sup_AB,
  A ≠ ∅ -> B ≠ ∅ -> has_upper_bound A -> has_upper_bound B ->
  is_lub A sup_A -> is_lub B sup_B -> 
  is_lub (A + B)%set sup_AB ->
  sup_AB = sup_A + sup_B.
Proof.
  intros A B sup_A sup_B sup_AB H1 H2 H3 H4 H5 H6 H7.
  apply Rle_antisym.
  - destruct H7 as [_ H8]. apply H8. intros z H9. destruct H9 as [x [y [H10 [H11 H12]]]].
    destruct H5 as [H13 _]. destruct H6 as [H14 _].
    specialize (H13 x H10). specialize (H14 y H11). lra.
  - apply Rnot_lt_le. intros H8.
    set (ε := sup_A + sup_B - sup_AB).
    assert (H9 : ε > 0) by (unfold ε; lra).
    assert (H10 : ∃ x, x ∈ A /\ sup_A - ε/2 < x).
    { pose proof classic (∃ x, x ∈ A /\ sup_A - ε/2 < x) as [H10 | H10]; auto.
      exfalso.
      assert (H11 : is_upper_bound A (sup_A - ε/2)).
      { intros x1 H11. pose proof classic (sup_A - ε/2 < x1) as [H12 | H12]; [|lra].
        exfalso. apply H10. exists x1. split; auto. }
      destruct H5 as [_ H12]. specialize (H12 (sup_A - ε/2) H11). lra. }
    destruct H10 as [x [H11 H12]].
    assert (H13 : ∃ y, y ∈ B /\ sup_B - ε/2 < y).
    { pose proof classic (∃ y, y ∈ B /\ sup_B - ε/2 < y) as [H13 | H13]; auto.
      exfalso.
      assert (H14 : is_upper_bound B (sup_B - ε/2)).
      { intros y1 H14. pose proof classic (sup_B - ε/2 < y1) as [H15 | H15]; [|lra].
        exfalso. apply H13. exists y1. split; auto. }
      destruct H6 as [_ H15]. specialize (H15 (sup_B - ε/2) H14). lra. }
    destruct H13 as [y [H14 H15]].
    assert (H16 : (x + y)%R ∈ (A + B)%set).
    { exists x. exists y. split; [exact H11 | split; [exact H14 | reflexivity]]. }
    destruct H7 as [H17 _].
    specialize (H17 (x + y) H16).
    unfold ε in *. lra.
Qed.

Lemma lemma_8_13' : ∀ A B sup_A sup_B sup_AB,
  A ≠ ∅ -> B ≠ ∅ -> has_upper_bound A -> has_upper_bound B ->
  is_lub A sup_A -> is_lub B sup_B -> 
  is_lub (A + B)%set sup_AB ->
  sup_AB = sup_A + sup_B.
Proof.
  intros A B sup_A sup_B sup_AB H1 H2 H3 H4 H5 H6 H7.
  apply Rle_antisym.
  - destruct H7 as [_ H8]. apply H8. intros z H9. destruct H9 as [x [y [H10 [H11 H12]]]].
    destruct H5 as [H13 _]. destruct H6 as [H14 _].
    specialize (H13 x H10). specialize (H14 y H11). lra.
  - destruct H6 as [_ H8].
    assert (H9 : is_upper_bound B (sup_AB - sup_A)).
    { intros y H10. destruct H5 as [_ H11].
      assert (H12 : is_upper_bound A (sup_AB - y)).
      { intros x H13. destruct H7 as [H14 _].
        assert (H15 : (x + y)%R ∈ (A + B)%set).
        { exists x. exists y. split; [exact H13 | split; [exact H10 | reflexivity]]. }
        specialize (H14 (x + y) H15). lra. }
      specialize (H11 (sup_AB - y) H12). lra. }
    specialize (H8 (sup_AB - sup_A) H9). lra.
Qed.