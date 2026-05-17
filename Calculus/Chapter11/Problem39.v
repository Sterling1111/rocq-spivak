From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_39 : forall m,
  ~ (exists x y, 0 <= x /\ x < y /\ y <= 1 /\
     x^3 - 3*x + m = 0 /\ y^3 - 3*y + m = 0).
Proof.
  intros m [x [y [H1 [H2 [H3 [H4 H5]]]]]].
  
  set (f := fun t : ℝ => t^3 - 3*t + m).
  set (f' := fun t : ℝ => 3 * t^2 - 3).

  assert (H6 : ⟦ der ⟧ f = f') by (unfold f, f'; auto_diff).

  assert (H7 : continuous_on f [x, y]) by (unfold f; auto_cont).

  assert (H8 : differentiable_on f (x, y)).
  { apply derivative_on_imp_differentiable_on with (f' := f'). auto_diff. }

  assert (H9 : f x = f y) by (unfold f; lra).

  pose proof rolles_theorem f x y H2 H7 H8 H9 as [c [H10 H11]].

  pose proof derivative_at_unique f f' (fun _ => 0) c (H6 c) H11 as H12.

  unfold f' in H12.
  
  solve_R.
Qed.