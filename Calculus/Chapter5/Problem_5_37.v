From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_37_a : ⟦ lim 3 ⟧ (λ x, 1 / (x - 3)^2) = ∞.
Proof.
  unfold limit_to_pinf.
  intros N.
  exists ( 1 / √(Rmax 1 N) ).
  assert (H1 : √(Rmax 1 N) > 0) by (apply sqrt_lt_R0; solve_R).
  split; [apply Rdiv_pos_pos; lra |].
  intros x [H2 H3].
  assert (H4 : (x - 3) * (x - 3) < 1 / √Rmax 1 N * (1 / √Rmax 1 N)) by solve_R.
  replace ((1 / √(Rmax 1 N)) * (1 / √(Rmax 1 N))) with (1 / (√ (Rmax 1 N) * √(Rmax 1 N))) in H4 by solve_R.
  rewrite sqrt_sqrt in H4; [ | solve_R].
  assert (H5 : / (1 / Rmax 1 N) < / ((x - 3) * (x - 3))).
  { apply Rinv_lt_contravar; try lra. apply Rmult_lt_0_compat; solve_R. }
  replace (/ (1 / Rmax 1 N)) with (Rmax 1 N) in H5 by solve_R.
  replace (1 / (x - 3) ^ 2) with (/ ((x - 3) * (x - 3))) by solve_R.
  solve_R.
Qed.