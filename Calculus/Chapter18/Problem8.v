From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_8_a : ∀ x,
  (cosh x)^2 - (sinh x)^2 = 1.
Proof.
  intros x.
  assert (H1 : exp x * exp (-x) = 1).
  { rewrite <- theorem_18_3. replace (x + -x) with 0 by lra. apply exp_0. }
  unfold cosh, sinh. nra.
Qed.

Lemma lemma_18_8_b : ∀ x,
  (tanh x)^2 + 1 / (cosh x)^2 = 1.
Proof.
  intros x.
  pose proof lemma_18_8_a x as H1.
  pose proof cosh_pos x as H2.
  unfold tanh.
  apply Rmult_eq_reg_r with (r := (cosh x)^2).
  - field_simplify; nra.
  - nra.
Qed.

Lemma lemma_18_8_c : ∀ x y,
  sinh (x + y) = sinh x * cosh y + cosh x * sinh y.
Proof.
  intros x y. unfold sinh, cosh.
  replace (- (x + y)) with (-x + -y) by lra.
  repeat rewrite theorem_18_3. field.
Qed.

Lemma lemma_18_8_d : ∀ x y,
  cosh (x + y) = cosh x * cosh y + sinh x * sinh y.
Proof.
  intros x y. unfold sinh, cosh.
  replace (- (x + y)) with (-x + -y) by lra.
  repeat rewrite theorem_18_3. field.
Qed.

Lemma lemma_18_8_e :
  ⟦ der ⟧ sinh = cosh.
Proof.
  auto_diff.
Qed.

Lemma lemma_18_8_f :
  ⟦ der ⟧ cosh = sinh.
Proof.
  auto_diff.
Qed.

Lemma lemma_18_8_g :
  ⟦ der ⟧ tanh = λ x, 1 / (cosh x)^2.
Proof.
  auto_diff.
Qed.