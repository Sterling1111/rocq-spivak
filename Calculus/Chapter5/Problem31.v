From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_31 : ∀ (f : R -> R) a L1 L2,
  ⟦ lim a⁻ ⟧ f = L1 -> ⟦ lim a⁺ ⟧ f = L2 -> L1 < L2 ->
  ∃ δ, δ > 0 /\ ∀ x y, x < a < y -> |x - a| < δ -> |y - a| < δ -> f x < f y.
Proof.
  intros f a L1 L2 H1 H2 H3.
  set (ε := (L2 - L1) / 2).

  assert (H4 : ε > 0). { unfold ε. apply Rdiv_pos_pos; lra. }

  specialize (H1 ε H4) as [δ1 [H1 H5]].
  specialize (H2 ε H4) as [δ2 [H2 H6]].

  exists (Rmin δ1 δ2).

  split; [solve_R |].
  intros x y H7 H8 H9.

  specialize (H5 x ltac:(solve_R)).
  specialize (H6 y ltac:(solve_R)).

  unfold ε in *.

  solve_R.
Qed.