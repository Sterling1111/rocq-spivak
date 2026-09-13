From Calculus.Chapter12 Require Import Prelude.

Lemma lemma_12_6 : ∀ a b c d,
  (∀ x, c * x + d <> 0) ->
  (one_to_one (λ x, (a * x + b) / (c * x + d)) <-> a * d - b * c <> 0).
Proof.
  intros a b c d H1. split.
  - intros H2 H3.
    assert (H4 : (a * 0 + b) / (c * 0 + d) = (a * 1 + b) / (c * 1 + d)).
    {
      pose proof H1 0 as H4.
      pose proof H1 1 as H5.
      apply Rmult_eq_reg_r with (r := (c * 0 + d) * (c * 1 + d)).
      - field_simplify; nra.
      - apply Rmult_integral_contrapositive_currified; auto.
    }
    specialize (H2 0 1 ltac:(apply Full_intro) ltac:(apply Full_intro) H4).
    lra.
  - intros H2 x y H3 H4 H5.
    pose proof H1 x as H6.
    pose proof H1 y as H7.
    apply Rmult_eq_compat_r with (r := (c * x + d) * (c * y + d)) in H5.
    field_simplify in H5; try assumption.
    assert (H8 : (a * d - b * c) * (x - y) = 0) by nra.
    apply Rmult_integral in H8 as [H8 | H8]; lra.
Qed.
