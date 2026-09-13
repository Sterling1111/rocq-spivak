From Calculus.Chapter5 Require Import Prelude Problem14 Problem34.

Lemma lemma_5_40_a (r : R) (n : nat) : True. Proof. Abort.

Lemma lemma_5_40_b (r : R) : ⟦ lim ∞ ⟧ (λ x, 2 * r * x * sin (π / x)) = 2 * π * r.
Proof.
  apply lemma_5_34.
  apply limit_right_eq with (f1 := λ x, 2 * r * (sin (π * x) / x)).
  - exists 1. split; [lra | intros x H1].
    replace (π / (1 / x)) with (π * x) by (field; lra).
    field; lra.
  - apply limit_iff.
    apply limit_subst with (L1 := 2 * r * (π * 1)); [ring |].
    apply limit_mult_const_l, lemma_5_14_a.
    + apply limit_sin_x_over_x.
    + pose proof π_pos. lra.
Qed.
