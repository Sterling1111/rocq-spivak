From Calculus.Chapter7 Require Import Prelude.

Lemma lemma_7_12_a : ∀ f,
  continuous_on f [0, 1] ->
  (∀ x, x ∈ [0, 1] -> f x ∈ [0, 1]) ->
  ∃ x, x ∈ [0, 1] /\ f x = 1 - x.
Proof.
  intros f H1 H2.
  set (g := fun x : ℝ => f x - 1 + x).
  assert (H3 : continuous_on g [0, 1]).
  { unfold g. apply continuous_on_plus; [ | auto_cont ]. apply continuous_on_minus; [ | auto_cont ]; auto. }
  assert (H4 : g 0 <= 0). { unfold g. pose proof (H2 0 ltac:(solve_R)). solve_R. }
  assert (H5 : g 1 >= 0). { unfold g. pose proof (H2 1 ltac:(solve_R)). solve_R. }
  pose proof intermediate_value_theorem_zero_le g 0 1 ltac:(solve_R) H3 ltac:(solve_R) as [x [H6 H7]].
  exists x. unfold g in H7; solve_R.
Qed.

Lemma lemma_7_12_b : ∀ f g,
  continuous_on f [0, 1] ->
  (∀ x, x ∈ [0, 1] -> f x ∈ [0, 1]) ->
  continuous_on g [0, 1] ->
  ((g 0 = 0 /\ g 1 = 1) \/ (g 0 = 1 /\ g 1 = 0)) ->
  ∃ x, x ∈ [0, 1] /\ f x = g x.
Proof.
  intros f g H1 H2 H3 H4.
  pose (h := fun x => f x - g x).
  assert (H5 : continuous_on h [0, 1]).
  { apply continuous_on_eq with (f1 := fun x => f x - g x); auto. apply continuous_on_minus; auto. }
  destruct H4 as [[H6 H7] | [H6 H7]].
  - assert (H8 : h 0 >= 0). { change (h 0) with (f 0 - g 0). pose proof (H2 0 ltac:(solve_R)). solve_R. }
    assert (H9 : h 1 <= 0). { change (h 1) with (f 1 - g 1). pose proof (H2 1 ltac:(solve_R)). solve_R. }
    pose proof intermediate_value_theorem_zero_le (fun x => - h x) 0 1 ltac:(solve_R) ltac:(apply continuous_on_neg; auto) ltac:(solve_R) as [x [H10 H11]].
    exists x. split; [exact H10 | unfold h in H11; solve_R].
  - assert (H8 : h 0 <= 0). { change (h 0) with (f 0 - g 0). pose proof (H2 0 ltac:(solve_R)). solve_R. }
    assert (H9 : h 1 >= 0). { change (h 1) with (f 1 - g 1). pose proof (H2 1 ltac:(solve_R)). solve_R. }
    pose proof intermediate_value_theorem_zero_le h 0 1 ltac:(solve_R) H5 ltac:(solve_R) as [x [H10 H11]].
    exists x. split; [exact H10 | unfold h in H11; solve_R].
Qed.