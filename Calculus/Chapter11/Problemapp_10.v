From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_app_10_a : ∀ f a b,
  a < b ->
  convex_on f (a, b) ->
  continuous_on f (a, b).
Proof.
  intros f a b H1 H2 x H3 ε H4.
  set (u := (a + x) / 2).
  set (v := (x + b) / 2).
  set (l := (f x - f u) / (x - u)).
  set (r := (f v - f x) / (v - x)).
  set (K := |l| + |r| + 1).
  assert (H5 : a < u < x /\ x < v < b) by (unfold u, v; solve_R).
  assert (H6 : K > 0) by (unfold K; solve_R).
  assert (H7 : f u = f x - l * (x - u)) by (unfold l; field; lra).
  assert (H8 : f v = f x + r * (v - x)) by (unfold r; field; lra).
  assert (H9 : ∀ p q s, p ∈ (a, b) -> q ∈ (a, b) -> s ∈ (a, b) -> p < q < s ->
    (f q - f p) * (s - p) < (f s - f p) * (q - p)).
  {
    intros p q s H9 H10 H11 H12.
    pose proof H2 p q s H9 H10 H11 H12 as H13.
    apply Rmult_lt_compat_r with (r := (q - p) * (s - p)) in H13; try nra.
    field_simplify in H13; lra.
  }
  exists (Rmin (Rmin (x - u) (v - x)) (ε / K)). split; [solve_R |].
  intros y H10 H11.
  assert (H12 : u < y < v) by solve_R.
  assert (H13 : |y - x| * K < ε).
  {
    assert (H13 : |y - x| < ε / K) by solve_R.
    apply Rmult_lt_compat_r with (r := K) in H13; try lra.
    field_simplify in H13; lra.
  }
  destruct (Rlt_dec x y) as [H14 | H14].
  - pose proof H9 x y v H3 H10 ltac:(solve_R) ltac:(lra) as H15.
    pose proof H9 u x y ltac:(solve_R) H3 H10 ltac:(lra) as H16.
    rewrite H8 in H15. rewrite H7 in H16.
    assert (H17 : l * (y - x) < f y - f x).
    { apply Rmult_lt_reg_r with (r := x - u); nra. }
    assert (H18 : f y - f x < r * (y - x)).
    { apply Rmult_lt_reg_r with (r := v - x); nra. }
    unfold K in H13. solve_abs.
  - assert (H15 : y < x) by solve_R.
    pose proof H9 u y x ltac:(solve_R) H10 H3 ltac:(lra) as H16.
    pose proof H9 y x v H10 H3 ltac:(solve_R) ltac:(lra) as H17.
    rewrite H7 in H16. rewrite H8 in H17.
    assert (H18 : r * (y - x) < f y - f x).
    { apply Rmult_lt_reg_r with (r := v - x); nra. }
    assert (H19 : f y - f x < l * (y - x)).
    { apply Rmult_lt_reg_r with (r := x - u); nra. }
    unfold K in H13. solve_abs.
Qed.
