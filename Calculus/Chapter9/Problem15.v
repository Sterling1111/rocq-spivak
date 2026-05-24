From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_15_a : forall f,
  (forall x, | f x | <= x^2) -> differentiable_at f 0.
Proof.
  intros f H1.
  exists 0.
  assert (H2 : f 0 = 0).
  { pose proof (H1 0) as H2. solve_R. }
  apply limit_eq with (f1 := λ h, f h / h).
  { exists 1; split; [lra |]. intros x H3. replace (0 + x) with x by lra. rewrite H2. lra. }

  apply limit_squeeze with (f1 := λ h, - |h|) (f3 := λ h, |h|) (a := -1) (b := 1); 
  try auto_limit.
  intros x H4.

  assert (H5 : |f x / x| <= |x|).
  {
    apply In_Union_def in H4.
    pose proof (H1 x) as H5.
    rewrite Rabs_div.
    apply Rmult_le_reg_r with (r := |x|); try solve [solve_R].
    field_simplify; solve_R.
  }
  solve_R.
Qed.

Lemma lemma_9_15_b : forall f g,
  differentiable_at g 0 -> g 0 = 0 -> ⟦ der 0 ⟧ g = (fun _ => 0) ->
  (forall x, | f x | <= | g x |) -> differentiable_at f 0.
Proof.
  intros f g H1 H2 H3 H4.
  exists 0.
  assert (H5 : f 0 = 0).
  { pose proof (H4 0) as H5. solve_R. }

  apply limit_eq with (f1 := λ h, f h / h).
  { exists 1; split; [lra |]. intros x H6. replace (0 + x) with x by lra. solve_R. }

  assert (H6 : ⟦ lim 0 ⟧ (λ h, g h / h) = 0).
  {
    destruct H1 as [L H6].
    apply limit_eq with (f1 := λ h, (g (0 + h) - g 0) / h); auto.
    exists 1; split; [lra |]. intros x H7. replace (0 + x) with x by lra. solve_R.
  }

  assert (H7 : ⟦ lim 0 ⟧ (λ h, |g h / h|) = 0).
  { rewrite <- Rabs_R0 at 2. apply limit_Rabs; auto. }

  assert (H8 : ⟦ lim 0 ⟧ (λ h : ℝ, - |(g h / h)|) = 0).
  { replace 0 with (- 0) at 2 by lra. apply limit_neg; auto. } 

  apply limit_squeeze with (f1 := λ h, - |g h / h|) (f3 := λ h, |g h / h|) (a := -1) (b := 1);
  try solve [solve_R].
  intros x H9.
  apply In_Union_def in H9.
  assert (H10 : |f x / x| <= |g x / x|).
  {
    pose proof (H4 x) as H10.
    rewrite !Rabs_div.
    apply Rmult_le_compat_r; auto.
    apply Rlt_le. apply Rinv_0_lt_compat. solve_R.
  }
  solve_R.
Qed.