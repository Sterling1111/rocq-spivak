From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_44 : forall f f' f'' g a b,
  a < b ->
  ⟦ der ⟧ f = f' ->
  ⟦ der ⟧ f' = f'' ->
  (forall x, f'' x + f' x * g x - f x = 0) ->
  f a = 0 -> f b = 0 ->
  forall x, x ∈ [a, b] -> f x = 0.
Proof.
  intros f f' f'' g a b H1 H2 H3 H4 H5 H6 x H7.

  assert (H8 : continuous_on f [a, b]).
  {
    apply continuous_imp_continuous_on, differentiable_imp_continuous,
    derivative_imp_differentiable with (f' := f'); auto.
  }

  pose proof continuous_on_interval_attains_maximum f a b H1 H8 as [y [H9 H10]].

  assert (H11 : f y <= 0).
  {
    assert (y = a \/ y = b \/ y ∈ (a, b)) as [H11 | [H11 | H11]] by solve_R.
    - subst; lra.
    - subst; lra.
    - assert (H12 : local_maximum_point f [a, b] y).
      {
        split; [exact H9 |]. exists 1; split; [ lra |].
        split; [apply In_Intersection_def; split; [exact H9 | solve_R] |].
        intros z H12. apply In_Intersection_def in H12 as [H12 H13].
        specialize (H10 z H12). solve_R.
      }
    assert (∃ δ, δ > 0 /\ ∀ z, |z - y| < δ -> z ∈ [a, b]) as [δ [H13 H14]].
    { exists (Rmin (y - a) (b - y)). split; [solve_R |]. intros z H13. solve_R. }

    assert (H15 : ⟦ der ⟧ f (y - δ, y + δ) = f') by auto_diff.

    pose proof local_max_imp_second_derivative_nonpos f f' f'' [a, b] y δ H13 H9 H14 H15 (H3 y) H12 as H16.

    assert (H17 : local_maximum_point f (a, b) y).
    {
      split; [solve_R |]. exists δ. split; [solve_R |]. 
      split; [ apply In_Intersection_def; solve_R | ].
      intros z H17. apply In_Intersection_def in H17.
      specialize (H10 z). solve_R.
    }

    assert (H18 : differentiable_at f y).
    { apply derivative_at_imp_differentiable_at with (f' := f'); auto. }

    pose proof derivative_at_local_maximum_point_zero f a b y H17 H18 as H19.
    pose proof derivative_at_unique f f' (fun _ => 0) y (H2 y) H19 as H20. simpl in H20.

    specialize (H4 y). rewrite H20, Rmult_0_l, Rplus_0_r in H4. lra.
  } 

  pose proof continuous_on_interval_attains_minimum f a b H1 H8 as [z [H12 H13]].

  assert (H14 : f z >= 0).
  {
    assert (z = a \/ z = b \/ z ∈ (a, b)) as [H14 | [H14 | H14]] by solve_R.
    - subst; lra.
    - subst; lra.
    - assert (H15 : local_minimum_point f [a, b] z).
      {
        split; [exact H12 |]. exists 1; split; [ lra |].
        split; [apply In_Intersection_def; split; [exact H12 | solve_R] |].
        intros w H15. apply In_Intersection_def in H15 as [H15 H16].
        specialize (H13 w H15). solve_R.
      }
      assert (∃ δ, δ > 0 /\ ∀ w, |w - z| < δ -> w ∈ [a, b]) as [δ [H16 H17]].
      { exists (Rmin (z - a) (b - z)). split; [solve_R |]. intros w H16. solve_R. }
      assert (H18 : ⟦ der ⟧ f (z - δ, z + δ) = f') by auto_diff.
      
      pose proof local_min_imp_second_derivative_nonneg f f' f'' [a, b] z δ H16 H12 H17 H18 (H3 z) H15 as H19.
      
      assert (H20 : local_minimum_point f (a, b) z).
      {
        split; [solve_R |]. exists δ. split; [solve_R |]. 
        split; [ apply In_Intersection_def; solve_R | ].
        intros w H20. apply In_Intersection_def in H20.
        specialize (H13 w). solve_R.
      }
      
      assert (H21 : differentiable_at f z).
      { apply derivative_at_imp_differentiable_at with (f' := f'); auto. }
      
      pose proof derivative_at_local_minimum_point_zero f a b z H20 H21 as H22.
      pose proof derivative_at_unique f f' (fun _ => 0) z (H2 z) H22 as H23. simpl in H23.
      
      specialize (H4 z). rewrite H23, Rmult_0_l, Rplus_0_r in H4. lra.
  }
  specialize (H10 x H7).
  specialize (H13 x H7).
  lra.
Qed.