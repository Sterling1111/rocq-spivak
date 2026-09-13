From Calculus.Chapter10 Require Import Prelude.

Definition double_root (f : ℝ -> ℝ) (a : ℝ) : Prop :=
  ∃ g, (∀ x, f x = (x - a)^2 * g x).

Lemma lemma_10_24_a : ∀ f a,
  (∃ g, ∀ x, f x = (x - a) * g x) ->
  (double_root f a <-> f a = 0 /\ ⟦ Der a ⟧ f = 0).
Proof. Abort.

Lemma lemma_10_24_b : ∀ a b c,
  a ≠ 0 ->
  (double_root (λ x, a * x^2 + b * x + c) (- b / (2 * a)) <-> b^2 - 4 * a * c = 0).
Proof.
  intros a b c H1. split.
  - intros [g H2]. specialize (H2 (- b / (2 * a))).
    replace (- b / (2 * a) - - b / (2 * a)) with 0 in H2 by ring.
    assert (H3 : a * (- b / (2 * a))^2 + b * (- b / (2 * a)) + c = 0) by nra.
    apply Rmult_eq_compat_r with (r := 4 * a) in H3.
    field_simplify in H3; nra.
  - intros H2. exists (λ _, a). intros x.
    apply Rmult_eq_reg_r with (r := 4 * a); [| nra].
    field_simplify; nra.
Qed.
