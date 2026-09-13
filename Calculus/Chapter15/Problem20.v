From Calculus.Chapter15 Require Import Prelude.

Lemma lemma_15_20 :
  ⟦ lim ∞ ⟧ (λ x, x * sin (1 / x)) = 1.
Proof.
  intros ε H1.
  destruct (limit_sin_x_over_x ε H1) as [δ [H2 H3]].
  exists (1 / δ). intros x H4.
  assert (H5 : 0 < x) by (pose proof Rdiv_pos_pos 1 δ ltac:(lra) H2; lra).
  assert (H6 : 0 < 1 / x < δ) by solve_R.
  specialize (H3 (1 / x) ltac:(solve_R)).
  replace (sin (1 / x) / (1 / x)) with (x * sin (1 / x)) in H3 by (field; solve_R).
  exact H3.
Qed.
