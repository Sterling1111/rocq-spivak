From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_10_a : ∀ a f l,
	⟦ lim a ⟧ f = l <-> ⟦ lim a ⟧ (λ x, f x - l) = 0.
Proof.
  intros a f l. split; intros H1 ε H2.
  - specialize (H1 ε H2) as [δ [H3 H4]].
    exists δ. split; auto. intros x H5. specialize (H4 x H5). solve_R.  
  - specialize (H1 ε H2) as [δ [H3 H4]].
    exists δ. split; auto. intros x H5. specialize (H4 x H5). solve_R.
Qed.

Lemma lemma_5_10_b : ∀ a f L1 L2,
  ⟦ lim 0 ⟧ f = L1 -> ⟦ lim a ⟧ (λ x, f (x - a)) = L2 -> L1 = L2.
Proof.
  intros a f L1 L2 H1 H2. apply cond_eq. intros ε H3.
  specialize (H1 (ε/2) ltac:(solve_R)) as [δ1 [H4 H5]].
  specialize (H2 (ε/2) ltac:(solve_R)) as [δ2 [H6 H7]].
  set (δ := (Rmin δ1 δ2) / 2).
  specialize (H5 δ ltac:(unfold δ in *; solve_R)).
  specialize (H7 (a + δ) ltac:(unfold δ in *; solve_R)).
  replace (a + δ - a) with δ in H7 by (solve_R).
  solve_R.
Qed.

Lemma lemma_5_10_c : ∀ f L1 L2,
  ⟦ lim 0 ⟧ f = L1 -> ⟦ lim 0 ⟧ (λ x, f (x^3)) = L2 -> L1 = L2.
Proof.
  intros f L1 L2 H1 H2. apply cond_eq. intros ε H3. specialize (H1 (ε/2) ltac:(solve_R)) as [δ1 [H4 H5]].
  specialize (H2 (ε/2) ltac:(solve_R)) as [δ2 [H6 H7]].
  set (δ := Rmin 1 (Rmin δ1 δ2) / 2).
  assert (H0 : 0 < (|((δ^3) - 0)|) < δ1).
  {
    assert (H8 : 0 < δ < 1 /\ δ < δ1) by (unfold δ; solve_R).
    assert (H9 : 0 < δ^2 < 1) by nra.
    rewrite Rminus_0_r, Rabs_pos_eq; nra.
  }
  specialize (H5 (δ^3) H0).
  specialize (H7 (δ) ltac:(unfold δ in *; solve_R)).
  solve_R.
Qed.

Lemma lemma_5_10_d : ∃ (f : R -> R) L, ⟦ lim 0 ⟧ (λ x, f (x^2)) = L /\ (∀ L', ¬ (⟦ lim 0 ⟧ f = L')).
Proof.
  exists (λ x, |x| / x), 1. split.
  - apply limit_eq with (f1 := λ _, 1).
    + exists 1. split; [lra | intros x H1].
      rewrite Rabs_pos_eq; solve_R.
    + apply limit_const.
  - intros L H1. specialize (H1 (1/2) ltac:(lra)) as [δ [H2 H3]].
    specialize (H3 (δ/2) ltac:(solve_R)) as H4.
    specialize (H3 (-δ/2) ltac:(solve_R)) as H5.
    rewrite Rabs_pos_eq with (x := δ/2) in H4; try lra.
    rewrite Rabs_left with (r := -δ/2) in H5; try lra.
    field_simplify in H4; try lra.
    field_simplify in H5; solve_R.
Qed.