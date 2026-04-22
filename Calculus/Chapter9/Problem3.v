From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_3 : forall a f f',
  a > 0 -> f = (fun x => √x) -> ⟦ der a ⟧ f = f' -> f' a = 1 / (2 * √a).
Proof.
  intros a f f' H1 H2 H3.
  assert (H4 : ⟦ der a ⟧ f = (fun x => 1 / (2 * √x))).
  {
    rewrite H2. unfold derivative_at.
    apply limit_eq with (f1 := (fun h => 1 / (√(a + h) + √a))).
    - exists a; split; [ exact H1 | intros h H5 ].
      assert (√(a + h) + √a <> 0) as H6.
      {
        pose proof sqrt_lt_R0 a H1 as H6.
        pose proof sqrt_lt_R0 (a + h) ltac:(solve_R) as H7. solve_R.
      }

      apply Rmult_eq_reg_r with (r := h); [ | solve_R ];
      apply Rmult_eq_reg_r with (r := (√(a + h) + √a)); [ | solve_R].
      field_simplify; try solve [solve_R].
      repeat rewrite pow2_sqrt; solve_R.
    - auto_limit; simp_zero; solve_R.
      + pose proof sqrt_lt_R0 a; solve_R.
      + pose proof sqrt_lt_R0 a; solve_R.
  }
  rewrite (derivative_at_unique f f' (fun x => 1 / (2 * √x)) a H3 H4); auto.
Qed.

Lemma lemma_9_3' : forall a f f',
  a > 0 -> f = (λ x, √x) -> ⟦ der a ⟧ f = f' -> f' a = 1 / (2 * √a).
Proof.
  intros a f f' H1 H2 H3.
  assert (H4 : ⟦ der a ⟧ f = λ x, 1 / (2 * √x)) by (rewrite H2; auto_diff).
  apply (derivative_at_unique f f' (λ x, 1 / (2 * √x)) a H3 H4).
Qed.

Lemma lemma_9_3'' : forall a,
  a > 0 ->
  ⟦ der a ⟧ (fun x => √x) = (fun x => 1 / (2 * sqrt x)).
Proof.
  auto_diff.
Qed.