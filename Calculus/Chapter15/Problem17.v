From Calculus.Chapter15 Require Import Prelude.
From Calculus.Chapter15 Require Import Problem16.

Lemma lemma_15_17 : forall u,
  -π < u < π ->
  cos (u/2) <> 0 ->
  let x := tan (u/2) in
  sin u = 2*x/(1+x^2) /\
  cos u = (1-x^2)/(1+x^2).
Proof.
  intros u H1 H2 x. 
  pose proof lemma_15_16 x as [H3 H4].
  split.
  - replace u with (2 * arctan x). 2 : { unfold x. rewrite arctan_tan; solve_R. }
    rewrite sin_2x, H3, H4.
    assert (H5 : (√(1 + x ^ 2)) * (√(1 + x ^ 2)) = 1 + x ^ 2) by (apply sqrt_sqrt; nra).
    field_simplify; try nra.
    rewrite pow2_sqrt; solve_R.
  - replace u with (2 * arctan x).
    2 : { unfold x. rewrite arctan_tan; solve_R. }
    rewrite cos_2x_1, H3, H4.
    assert (H5 : √(1 + x^2) * √(1 + x^2) = 1 + x^2) by (apply sqrt_sqrt; nra).
    field_simplify; try nra.
    rewrite pow2_sqrt; solve_R.
Qed.