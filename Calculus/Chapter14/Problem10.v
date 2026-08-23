From Calculus.Chapter14 Require Import Prelude.
From Calculus.Chapter14 Require Import Problem9.


Lemma lemma_14_10 : forall f x,
  continuous f ->
  ∫ 0 x (λ u, f u * (x - u)^2) =
  2 * ∫ 0 x (λ u2, ∫ 0 u2 (λ u1, ∫ 0 u1 f)).
Proof.
  intros f x H1.
  set (F := λ u : ℝ, ∫ 0 u f).

  assert (H2 : continuous F).
  {
    apply differentiable_imp_continuous.
    eapply derivative_imp_differentiable.
    unfold F.
    apply FTC1_global.
    exact H1.
  }

  assert (H3 : integrable_on (Rmin 0 x) (Rmax 0 x) (λ u : ℝ, F u * (x - u))).
  { apply theorem_13_3; auto_cont. }

  pose proof (integration_by_parts_definite F (λ u : ℝ, (x - u)^2) f) (λ u, -2 * (x - u))
    (λ u, ∫ 0 u (λ t, f t * (x - t)^2)) 0 x H1 ltac:(auto_cont)
    ltac:(unfold F; apply FTC1_global; exact H1)
    ltac:(auto_diff)
    ltac:(apply FTC1_global; auto_cont) as H4.

  rewrite integral_mult_scalar' in H4; [| exact H3].

  unfold F in H4.
  rewrite integral_n_n in H4.
  lra.
Qed.