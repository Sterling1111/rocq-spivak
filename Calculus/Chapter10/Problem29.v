From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_29 : ∀ f,
  differentiable_at f 0 ->
  f 0 = 0 ->
  ∃ g, (∀ x, f x = x * g x) /\ continuous_at g 0.
Proof.
  intros f [L H1] H2. 
  set (g := λ x, if Req_dec_T x 0 then L else f x / x).
  assert (H3 : ∀ x, (x = 0 -> g x = L) /\ (x <> 0 -> g x = f x / x)).
  { intros x; split; intros H3; unfold g; destruct (Req_dec_T x 0); lra. }
  exists g.
  split.
  - intros x.
    destruct (Req_dec_T x 0) as [H4 | H4].
    + subst x. rewrite H2. lra.
    + destruct (H3 x) as [_ H5].
      specialize (H5 H4).
      rewrite H5.
      solve_R.
  - apply limit_eq with (f1 := λ h : ℝ, (f (0 + h) - f 0) / h).
    + exists 1; split; [ lra |].
      intros x H4.
      specialize (H3 x) as [_ H3].
      specialize (H3 ltac:(solve_R)).
      rewrite H3, Rplus_0_l.
      solve_R.
    + replace (g 0) with L by (specialize (H3 0); lra).
      exact H1.
Qed.