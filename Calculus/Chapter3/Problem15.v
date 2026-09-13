From Calculus.Chapter3 Require Export Prelude.

Lemma lemma_3_15_a : ∀ f : R -> R, 
  ∀ x, f x = Rmax (f x) 0 + Rmin (f x) 0.
Proof.
  intros f x. solve_R.
Qed.

Lemma lemma_3_15_b : ∀ (f : R -> R) (l : list ((R -> R) * (R -> R))),
  ∃ g h : R -> R, ~ List.In (g, h) l /\
    nonnegative g /\ nonnegative h /\ ∀ x, f x = g x - h x.
Proof.
  intros f l.
  assert (H1 : ∃ M, 0 <= M /\ ∀ g h, List.In (g, h) l -> g 0 < M).
  { induction l as [|[g h] l [M [H1 IH]]].
    - exists 0. split; [lra | intros g h H2; contradiction].
    - exists (Rmax (g 0) M + 1). split; [solve_R |].
      intros g1 h1 [H2 | H2].
      + inversion H2. subst. solve_R.
      + specialize (IH g1 h1 H2). solve_R. }
  destruct H1 as [M [H1 H2]].
  exists (λ x, Rmax (f x) 0 + M), (λ x, - Rmin (f x) 0 + M).
  split.
  - intro H3. specialize (H2 _ _ H3). simpl in H2. solve_R.
  - repeat split; intro x; solve_R.
Qed.
