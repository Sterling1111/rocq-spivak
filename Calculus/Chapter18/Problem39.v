From Calculus.Chapter18 Require Import Prelude.
From Calculus.Chapter8 Require Import Problem7.

Lemma lemma_18_39 : ∀ f,
  continuous f ->
  (∀ x y, x > 0 -> y > 0 -> f (x * y) = f x + f y) ->
  (∀ x, x > 0 -> f x = 0) \/ (∀ x, x > 0 -> f x = f e * log x).
Proof.
  intros f H1 H2.
  set (g := λ x, f (e ^^ x)).
  assert (H3 : ∀ x y, g (x + y) = g x + g y).
  { intros x y. unfold g. rewrite Rpower_plus; [apply H2|]; solve_denoms. }
  pose proof lemma_8_7 g ltac:(unfold g; auto_cont) H3 as [c H4].
  assert (c = 0 \/ c <> 0) as [H5 | H5] by (apply classic); [left | right].
  - intros x H6. assert (H7 : e ^^ log x = x).
    { rewrite <- exp_Rpower. apply exp_log; auto. }
    rewrite <- H7.
    change (f (e ^^ log x)) with (g (log x)).
    rewrite H4, H5.
    lra.
  - intros x H6.
    assert (H7 : f x = g (log x)).
    { unfold g. rewrite <- exp_Rpower, exp_log; auto. }
    assert (H8 : f e = g 1).
    { unfold g. rewrite Rpower_1; solve_denoms. }
    rewrite H7, H8.
    repeat rewrite H4.
    lra.
Qed.