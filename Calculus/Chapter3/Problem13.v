From Calculus.Chapter3 Require Export Prelude.

Lemma lemma_3_13_a : ∀ f : R -> R,
  ∃ E O : R -> R, even E /\ odd O /\ ∀ x, f x = E x + O x.
Proof.
  intros f. exists (λ x, (f x + f (-x)) / 2), (λ x, (f x - f (-x)) / 2).
  repeat split; intros x; try rewrite Ropp_involutive; lra.
Qed.

Lemma lemma_3_13_b : ∀ f E1 O1 E2 O2 : R -> R,
  even E1 -> odd O1 -> (∀ x, f x = E1 x + O1 x) ->
  even E2 -> odd O2 -> (∀ x, f x = E2 x + O2 x) ->
  (∀ x, E1 x = E2 x) /\ (∀ x, O1 x = O2 x).
Proof.
  intros f E1 O1 E2 O2 H1 H2 H3 H4 H5 H6.
  split; intros x; pose proof (H3 x); pose proof (H3 (-x));
  pose proof (H6 x); pose proof (H6 (-x));
  rewrite H1, H2 in *; rewrite H4, H5 in *; lra.
Qed.
