From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_13_a : ∀ f x,
  -1 < x < 1 ->
  f = (λ x, √ (1 - x^2)) ->
  ⟦ der x ⟧ f = (fun x => - x / √ (1 - x^2)).
Proof.
  intros f x H1 H2.
  subst.
  auto_diff.
Qed.

Lemma lemma_10_13_b : ∀ (a : ℝ) (f : ℝ -> ℝ),
  let g := tangent_line f a in
  -1 < a < 1 ->
  f = (λ x, sqrt (1 - x^2)) ->
  ∀ x, -1 < x < 1 -> f x = g x -> x = a.
Proof.
  intros a f g H1 H2 x H3 H4.
  assert (H5 : ∀ x, -1 < x < 1 -> g x = √(1 - a ^ 2) - a / √(1 - a ^ 2) * (x - a)).
  {
    intros y H5.
    unfold g, tangent_line.
    assert (H6 : (⟦ Der a ⟧ f) = - a / √(1 - a ^ 2)).
    {
      assert (H6 : differentiable_at f a).
      { rewrite H2. apply (derivative_at_imp_differentiable_at _ (λ x, - x / √(1 - x ^ 2))); auto_diff. }
      apply (derive_at_spec f (λ x, - x / √(1 - x ^ 2)) a H6); rewrite H2; auto_diff.
    }
    rewrite H6. rewrite H2. nra.
   }
   specialize (H5 x H3). rewrite H2 in H4. rewrite <- H4 in H5.

  assert (H6 : √(1 - x ^ 2) * √(1 - a ^ 2) = 1 - a * x).
  {
    apply Rmult_eq_compat_r with (r := sqrt (1 - a^2)) in H5.
    rewrite Rmult_minus_distr_r, sqrt_sqrt in H5; try nra.
    replace (a / sqrt (1 - a^2) * (x - a) * sqrt (1 - a^2)) with (a * (x - a)) in H5 by (field; nra).
    lra.
  }

  assert (H7 : √(1 - x ^ 2) * √(1 - x ^ 2) * (√(1 - a ^ 2) * √(1 - a ^ 2)) = (1 - a * x) * (1 - a * x)).
  { rewrite <- H6. lra. }

  (do 2 rewrite sqrt_sqrt in H7); try nra.
Qed.