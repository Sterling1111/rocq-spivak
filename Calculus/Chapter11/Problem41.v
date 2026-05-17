From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_41_a : 
  let f := (λ x, x^2 - cos x) in
  exists x1 x2, x1 <> x2 /\ 
  f x1 = 0 /\ f x2 = 0 /\
  (forall x, f x = 0 -> x = x1 \/ x = x2).
Proof.
  intros f.

  set (f' := λ y, 2 * y + sin y).
  set (f'' := λ y, 2 + cos y).

  assert (H1 : f 0 < 0).
  { unfold f. simpl. rewrite Rmult_0_l, Rminus_0_l, cos_0. lra. }
  assert (H2 : f 1 > 0).
  { unfold f. simpl. pose proof cos_1_bounds as H2. lra. }
  assert (H3 : f (-1) > 0).
  {
    unfold f. simpl. replace (-1) with (-(1)) by lra.
    pose proof cos_1_bounds as H3. rewrite cos_even_odd. lra.
  }

  assert (exists x1, -1 < x1 < 0 /\ f x1 = 0) as [x1 [H4 H5]].
  {
    pose proof (intermediate_value_theorem_decreasing f (-1) 0 0 ltac:(lra)) ltac:(unfold f; auto_cont) ltac:(lra) as [x [H6 H7]].
    exists x. split; auto.
    assert (x = -1 \/ x = 0 \/ x ∈ (-1, 0)) as [H8 | [H8 | H8]]; subst; solve_R.
  }

  assert (exists x2, 0 < x2 < 1 /\ f x2 = 0) as [x2 [H6 H7]].
  {
    pose proof (intermediate_value_theorem f 0 1 0 ltac:(lra)) ltac:(unfold f; auto_cont) ltac:(lra) as [x [H8 H9]].
    exists x. split; auto.
    assert (x = 0 \/ x = 1 \/ x ∈ (0, 1)) as [H10 | [H10 | H10]]; subst; solve_R.
  }
  
  exists x1, x2; repeat split; try solve [solve_R].
  intros x H8.
  
  assert (H9 : ⟦ der ⟧ f = f') by (unfold f, f'; auto_diff).
  assert (H10 : ⟦ der ⟧ f' = f'') by (unfold f', f''; auto_diff).
  
  destruct (classic (x = x1 \/ x = x2)) as [H11 | H11]; auto.
  apply not_or_and in H11 as [H12 H13].

  assert (H14 : forall a b, a < b -> f a = 0 -> f b = 0 -> exists c, a < c < b /\ 2 * c + sin c = 0).
  {
    intros a b H15 H16 H17.
    assert (H18 : continuous_on f [a, b]) by (unfold f; auto_cont).
    assert (H19 : differentiable_on f (a, b)).
    {
      apply derivative_on_imp_differentiable_on with (f' := fun y => 2 * y + sin y).
      apply derivative_imp_derivative_on; auto.
      apply differentiable_domain_open; lra.
    }
    assert (H20 : f a = f b) by lra.
    pose proof (rolles_theorem f a b H15 H18 H19 H20) as [c [H21 H22]].
    exists c. split; [exact H21 |].
    pose proof (derivative_at_unique f (λ _, 0) (fun y => 2 * y + sin y) c H22 (H9 c)) as H23; auto.
  }
  
  assert (H15 : forall a b, a < b -> 2 * a + sin a = 0 -> 2 * b + sin b = 0 -> exists c, a < c < b /\ 2 + cos c = 0).
  {
    intros a b H16 H17 H18.
    assert (H19 : continuous_on (fun y => 2 * y + sin y) [a, b]) by auto_cont.
    assert (H20 : differentiable_on (fun y => 2 * y + sin y) (a, b)).
    {
      apply derivative_on_imp_differentiable_on with (f' := fun y => 2 + cos y).
      apply derivative_imp_derivative_on; auto.
      apply differentiable_domain_open; lra.
    }
    assert (H21 : 2 * a + sin a = 2 * b + sin b) by lra.
    pose proof (rolles_theorem (fun y => 2 * y + sin y) a b H16 H19 H20 H21) as [c [H22 H23]].
    exists c. split; [exact H22 |].
    pose proof (derivative_at_unique (fun y => 2 * y + sin y) (λ _, 0) (fun y => 2 + cos y) c H23 (H10 c)) as H24; auto.
  }
  
  assert (exists c, 2 + cos c = 0) as [c H16].
  {
    assert (x < x1 \/ x1 < x < x2 \/ x2 < x) as [H17 | [H17 | H17]] by lra.
    - pose proof (H14 x x1 H17 H8 H5) as [c1 [H18 H19]].
      pose proof (H14 x1 x2 ltac:(lra) H5 H7) as [c2 [H20 H21]].
      pose proof (H15 c1 c2 ltac:(lra) H19 H21) as [c [H22 H23]].
      exists c; exact H23.
    - pose proof (H14 x1 x ltac:(lra) H5 H8) as [c1 [H18 H19]].
      pose proof (H14 x x2 ltac:(lra) H8 H7) as [c2 [H20 H21]].
      pose proof (H15 c1 c2 ltac:(lra) H19 H21) as [c [H22 H23]].
      exists c; exact H23.
    - pose proof (H14 x1 x2 ltac:(lra) H5 H7) as [c1 [H18 H19]].
      pose proof (H14 x2 x ltac:(lra) H7 H8) as [c2 [H20 H21]].
      pose proof (H15 c1 c2 ltac:(lra) H19 H21) as [c [H22 H23]].
      exists c; exact H23.
  }
  
  pose proof (cos_bounds c) as H18.
  lra.
Qed.


Lemma lemma_11_41_b : 
  let f := (λ x, x^2 - x * sin x - cos x) in
  exists x1 x2, x1 <> x2 /\ 
  f x1 = 0 /\ f x2 = 0 /\
  (forall x, f x = 0 -> x = x1 \/ x = x2).
Proof.
  intros f.

  set (f' := λ y, y * (2 - cos y)).

  assert (H1 : f 0 < 0).
  { unfold f. simpl. simp_zero. rewrite cos_0. lra. }
  assert (H2 : f 2 > 0).
  { unfold f. simpl. pose proof (sin_bounds 2). pose proof (cos_bounds 2). lra. }
  assert (H3 : f (-2) > 0).
  {
    unfold f. simpl.
    rewrite sin_compat, cos_compat. interval.
  }

  assert (exists x1, -2 < x1 < 0 /\ f x1 = 0) as [x1 [H4 H5]].
  {
    pose proof (intermediate_value_theorem_decreasing f (-2) 0 0 ltac:(lra)) ltac:(unfold f; auto_cont) ltac:(lra) as [x [H6 H7]].
    exists x. split; auto.
    assert (x = -2 \/ x = 0 \/ x ∈ (-2, 0)) as [H8 | [H8 | H8]]; subst; solve_R.
  }

  assert (exists x2, 0 < x2 < 2 /\ f x2 = 0) as [x2 [H6 H7]].
  {
    pose proof (intermediate_value_theorem f 0 2 0 ltac:(lra)) ltac:(unfold f; auto_cont) ltac:(lra) as [x [H8 H9]].
    exists x. split; auto.
    assert (x = 0 \/ x = 2 \/ x ∈ (0, 2)) as [H10 | [H10 | H10]]; subst; solve_R.
  }
  
  exists x1, x2; repeat split; try solve [solve_R].
  intros x H8.
  
  assert (H9 : ⟦ der ⟧ f = f') by (unfold f, f'; auto_diff).
  
  destruct (classic (x = x1 \/ x = x2)) as [H10 | H10]; auto.
  apply not_or_and in H10 as [H11 H12].

  assert (H13 : forall a b, a < b -> f a = 0 -> f b = 0 -> exists c, a < c < b /\ c * (2 - cos c) = 0).
  {
    intros a b H14 H15 H16.
    assert (H17 : continuous_on f [a, b]) by (unfold f; auto_cont).
    assert (H18 : differentiable_on f (a, b)).
    { apply derivative_on_imp_differentiable_on with (f' := f'); auto_diff. }
    assert (H19 : f a = f b) by lra.
    pose proof (rolles_theorem f a b H14 H17 H18 H19) as [c [H20 H21]].
    exists c. split; [exact H20 |].
    pose proof (derivative_at_unique f (λ _, 0) f' c H21 (H9 c)) as H22; auto.
  }

  assert (H14 : forall c, c * (2 - cos c) = 0 -> c = 0).
  { intros c H15. pose proof (cos_bounds c). nra. }

  assert (x < x1 \/ x1 < x < x2 \/ x2 < x) as [H15 | [H15 | H15]] by lra.
  - pose proof (H13 x x1 H15 H8 H5) as [c [H16 H17]].
    apply H14 in H17. lra.
  - pose proof (H13 x1 x ltac:(lra) H5 H8) as [c1 [H16 H17]].
    pose proof (H13 x x2 ltac:(lra) H8 H7) as [c2 [H18 H19]].
    apply H14 in H17. apply H14 in H19. lra.
  - pose proof (H13 x2 x ltac:(lra) H7 H8) as [c [H16 H17]].
    apply H14 in H17. lra.
Qed.

Lemma lemma_11_41_c : 
  let f := (λ x, 2 * x^2 - x * sin x - cos x * cos x) in
  exists x1 x2, x1 <> x2 /\ 
  f x1 = 0 /\ f x2 = 0 /\
  (forall x, f x = 0 -> x = x1 \/ x = x2).
Proof.
  intros f.

  set (f' := λ y, 4 * y - sin y - y * cos y + 2 * sin y * cos y).
  set (f'' := λ y, 4 - 2 * cos y + y * sin y + 2 * cos y * cos y - 2 * sin y * sin y).

  assert (H1 : f 0 < 0).
  { unfold f. simpl. rewrite sin_0, cos_0. lra. }
  assert (H2 : f 2 > 0).
  { unfold f. simpl. pose proof (sin_bounds 2). pose proof (cos_bounds 2). nra. }
  assert (H3 : f (-2) > 0).
  { unfold f. simpl. pose proof (sin_bounds (-2)). pose proof (cos_bounds (-2)). nra. }

  assert (exists x1, -2 < x1 < 0 /\ f x1 = 0) as [x1 [H4 H5]].
  {
    pose proof (intermediate_value_theorem_decreasing f (-2) 0 0 ltac:(lra)) ltac:(unfold f; auto_cont) ltac:(lra) as [x [H6 H7]].
    exists x. split; auto.
    assert (x = -2 \/ x = 0 \/ x ∈ (-2, 0)) as [H8 | [H8 | H8]]; subst; solve_R.
  }

  assert (exists x2, 0 < x2 < 2 /\ f x2 = 0) as [x2 [H6 H7]].
  {
    pose proof (intermediate_value_theorem f 0 2 0 ltac:(lra)) ltac:(unfold f; auto_cont) ltac:(lra) as [x [H8 H9]].
    exists x. split; auto.
    assert (x = 0 \/ x = 2 \/ x ∈ (0, 2)) as [H10 | [H10 | H10]]; subst; solve_R.
  }
  
  exists x1, x2; repeat split; try solve [solve_R].
  intros x H8.
  
  assert (⟦ der ⟧ f = f' /\ ⟦ der ⟧ f' = f'') as [H9 H10] by (unfold f, f', f''; split; auto_diff).

  destruct (classic (x = x1 \/ x = x2)) as [H11 | H11]; auto.
  apply not_or_and in H11 as [H12 H13].

  assert (H14 : forall r, f r = 0 -> -1 <= r <= 1).
  {
    intros r H14.
    pose proof (sin_bounds r) as H15.
    pose proof (cos_bounds r) as H16.
    destruct (Rlt_le_dec 1 r) as [H17 | H17].
    - assert (r * sin r <= r) as H18 by nra.
      assert (cos r * cos r <= 1) as H19 by nra.
      assert (f r > 0) as H20 by (unfold f; nra).
      lra.
    - destruct (Rlt_le_dec r (-1)) as [H18 | H18]; try lra.
      assert (r * sin r <= - r) as H19 by nra.
      assert (cos r * cos r <= 1) as H20 by nra.
      assert (f r > 0) as H21 by (unfold f; nra).
      lra.
  }

  assert (H15 : forall a0 b0, a0 < b0 -> f a0 = 0 -> f b0 = 0 -> exists c0, a0 < c0 < b0 /\ f' c0 = 0).
  {
    intros a0 b0 H16 H17 H18.
    assert (H19 : continuous_on f [a0, b0]) by (unfold f; auto_cont).
    assert (H20 : differentiable_on f (a0, b0)).
    { apply derivative_on_imp_differentiable_on with (f' := f'); auto_diff. }
    pose proof (rolles_theorem f a0 b0 H16 H19 H20 ltac:(lra)) as [c0 [H21 H22]].
    exists c0. split; [exact H21 |].
    pose proof (derivative_at_unique f (λ _, 0) f' c0 H22 (H9 c0)) as H23; auto.
  }

  assert (H16 : forall a0 b0, a0 < b0 -> f' a0 = 0 -> f' b0 = 0 -> exists c0, a0 < c0 < b0 /\ f'' c0 = 0).
  {
    intros a0 b0 H17 H18 H19.
    assert (H20 : continuous_on f' [a0, b0]) by (unfold f'; auto_cont).
    assert (H21 : differentiable_on f' (a0, b0)).
    { apply derivative_on_imp_differentiable_on with (f' := f''); auto_diff. }

    pose proof (rolles_theorem f' a0 b0 H17 H20 H21 ltac:(lra)) as [c0 [H22 H23]].
    exists c0. split; [exact H22 |].
    pose proof (derivative_at_unique f' (λ _, 0) f'' c0 H23 (H10 c0)) as H24; auto.
  }

  assert (exists c, f'' c = 0 /\ -1 <= c <= 1) as [c [H17 H18]].
  {
    assert (x < x1 \/ x1 < x < x2 \/ x2 < x) as [H19 | [H19 | H19]] by lra.
    - pose proof (H15 x x1 H19 H8 H5) as [c1 [H20 H21]].
      pose proof (H15 x1 x2 ltac:(lra) H5 H7) as [c2 [H22 H23]].
      pose proof (H16 c1 c2 ltac:(lra) H21 H23) as [c0 [H24 H25]].
      exists c0. split; [exact H25 |].
      assert (-1 <= x) by (apply H14; auto).
      assert (x2 <= 1) by (apply H14; auto).
      lra.
    - pose proof (H15 x1 x ltac:(lra) H5 H8) as [c1 [H20 H21]].
      pose proof (H15 x x2 ltac:(lra) H8 H7) as [c2 [H22 H23]].
      pose proof (H16 c1 c2 ltac:(lra) H21 H23) as [c0 [H24 H25]].
      exists c0. split; [exact H25 |].
      assert (-1 <= x1) by (apply H14; auto).
      assert (x2 <= 1) by (apply H14; auto).
      lra.
    - pose proof (H15 x1 x2 ltac:(lra) H5 H7) as [c1 [H20 H21]].
      pose proof (H15 x2 x ltac:(lra) H7 H8) as [c2 [H22 H23]].
      pose proof (H16 c1 c2 ltac:(lra) H21 H23) as [c0 [H24 H25]].
      exists c0. split; [exact H25 |].
      assert (-1 <= x1) by (apply H14; auto).
      assert (x <= 1) by (apply H14; auto).
      lra.
  }

  pose proof (sin_bounds c).
  pose proof (cos_bounds c).
  assert (H19 : sin c * sin c + cos c * cos c = 1).
  { rewrite sin_compat, cos_compat in *. pose proof (sin2_cos2 c). unfold Rsqr in *. lra. }
  assert (H20 : c * sin c >= -1).
  { destruct (Rle_dec 0 c); destruct (Rle_dec 0 (sin c)); nra. }
  unfold f'' in H17.
  nra.
Qed.