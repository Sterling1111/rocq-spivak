From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_58 : ∀ f f' a,
  ⟦ der ⟧ f = f' ->
  increasing f' ->
  ∀ x, x <> a -> f x <> f' a * (x - a) + f a.
Proof.
  intros f f' a H1 H2 x H3 H4.
  set (g := λ y, f' a * (y - a) + f a - f y).
  assert (H5 : ⟦ der ⟧ g = λ y, f' a - f' y) by (unfold g; auto_diff).
  assert (H6 : continuous g).
  { apply differentiable_imp_continuous, derivative_imp_differentiable with (f' := λ y, f' a - f' y); auto. }
  assert (H7 : g a = g x) by (unfold g; lra).
  destruct (Rlt_dec a x) as [H8 | H8].
  - pose proof rolles_theorem g a x H8 ltac:(apply continuous_imp_continuous_on; auto)
      ltac:(apply derivative_on_imp_differentiable_on with (f' := λ y, f' a - f' y); auto_diff)
      H7 as [c [H9 H10]].
    pose proof derivative_at_unique g _ _ c (H5 c) H10 as H11.
    pose proof H2 a c ltac:(solve_R) ltac:(solve_R) ltac:(solve_R) as H12. simpl in H11. lra.
  - pose proof rolles_theorem g x a ltac:(lra) ltac:(apply continuous_imp_continuous_on; auto)
      ltac:(apply derivative_on_imp_differentiable_on with (f' := λ y, f' a - f' y); auto_diff)
      ltac:(lra) as [c [H9 H10]].
    pose proof derivative_at_unique g _ _ c (H5 c) H10 as H11.
    pose proof H2 c a ltac:(solve_R) ltac:(solve_R) ltac:(solve_R) as H12. simpl in H11. lra.
Qed.
