From Calculus.Chapter6 Require Import Prelude.

Lemma lemma_6_5 : ∀ a,
  ∃ f, continuous_at f a /\ (∀ x, x <> a -> ~ continuous_at f x).
Proof.
  intros a. set (f := λ x : R, if excluded_middle_informative (rational x) then x else a).
  exists f. split.
  - intros ε H1. exists ε. split; [lra | intros x H2].
    unfold f. destruct (excluded_middle_informative (rational x));
      destruct (excluded_middle_informative (rational a)); solve_R.
  - intros b H1 H2. specialize (H2 (|b - a| / 4) ltac:(solve_R)) as [δ [H3 H4]].
    set (δ' := Rmin δ (|b - a| / 4)).
    destruct (exists_irrational_between b (b + δ') ltac:(unfold δ'; solve_R)) as [x [H5 H6]].
    destruct (exists_rational_between b (b + δ') ltac:(unfold δ'; solve_R)) as [y [H7 H8]].
    unfold δ' in *.
    specialize (H4 x ltac:(solve_R)) as H9.
    specialize (H4 y ltac:(solve_R)) as H10.
    unfold f in H9, H10.
    destruct (excluded_middle_informative (rational x)); try contradiction.
    destruct (excluded_middle_informative (rational y)); try contradiction.
    solve_R.
Qed.
