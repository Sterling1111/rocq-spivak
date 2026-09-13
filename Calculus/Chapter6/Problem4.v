From Calculus.Chapter6 Require Import Prelude.

Lemma lemma_6_4 :
  ∃ f, (∀ x, ~ continuous_at f x) /\ continuous (λ x, |f x|).
Proof.
  set (f := λ x : R, if excluded_middle_informative (rational x) then 1 else -1).
  exists f. split.
  - intros a H1. specialize (H1 (1/2) ltac:(lra)) as [δ [H2 H3]].
    destruct (exists_irrational_between a (a + δ) ltac:(lra)) as [x [H4 H5]].
    destruct (exists_rational_between a (a + δ) ltac:(lra)) as [y [H6 H7]].
    specialize (H3 x ltac:(solve_R)) as H8.
    specialize (H3 y ltac:(solve_R)) as H9.
    unfold f in H8, H9.
    destruct (excluded_middle_informative (rational x)); try contradiction.
    destruct (excluded_middle_informative (rational y)); try contradiction.
    solve_R.
  - intros a. apply continuous_at_ext with (f := λ _, 1).
    + intros x. unfold f. destruct (excluded_middle_informative (rational x)); solve_R.
    + auto_cont.
Qed.
