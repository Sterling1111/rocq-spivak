From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_16 : forall f α,
  α > 1 -> (forall x, | f x | <= |x| ^^ α) -> differentiable_at f 0.
Proof.
  intros f α H1 H2. 
  exists 0.
  assert (H3 : f 0 = 0).
  { specialize (H2 0). rewrite Rabs_R0, Rpower_0_base in H2; solve_R. }

  apply limit_eq with (f1 := λ h, f h / h).
  { exists 1; split; [lra|]. intros x H4. simp_zero. solve_R. }

  apply limit_squeeze with (f1 := λ h, - (|h|^^(α-1))) (f3 := λ h, |h|^^(α-1)) (a := -1) (b := 1);
  try solve [solve_R].

  - apply limit_neg_Rabs_Rpower_zero; solve_R.
  - apply limit_Rabs_Rpower_zero; solve_R.
  - intros x H4.

    apply In_Union_def in H4.

    assert (H6 : |f x / x| <= |x| ^^ (α - 1)).
    {
      rewrite Rabs_div.
      pose proof (H2 x) as H7.
      apply Rmult_le_reg_r with (r := |x|); [solve_R |].
      field_simplify; [| solve_R].
      rewrite Rpower_minus, Rpower_1; field_simplify; solve_R.
    }
    solve_abs.
Qed.