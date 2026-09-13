From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_23_a : ∀ (f g : R → R) (a L : R),
  ⟦ lim a ⟧ f = L → L ≠ 0 →
  (~ ∃ L1, ⟦ lim a ⟧ g = L1) →
  (~ ∃ L2, ⟦ lim a ⟧ (λ x, f x * g x) = L2).
Proof.
  intros f g a L H1 H2 H3 [L2 H4]. apply H3. exists (L2 / L).
  destruct (limit_neq_neighborhood f a L 0 H1 H2) as [δ [H5 H6]].
  apply limit_eq with (f1 := λ x, (f x * g x) / f x).
  - exists δ. split; auto. intros x H7. specialize (H6 x H7). field; auto.
  - apply limit_div; auto.
Qed.

Lemma lemma_5_23_b : ∀ (f g : R → R) (a : R),
  ⟦ lim a ⟧ (λ x, |f x|) = ∞ ->
  (~ ∃ L1, ⟦ lim a ⟧ g = L1) ->
  (~ ∃ L2, ⟦ lim a ⟧ (λ x, f x * g x) = L2).
Proof.
  intros f g a H1 H2 [L H3]. apply H2. exists 0.
  intros ε H4.
  specialize (H3 1 ltac:(lra)) as [δ1 [H5 H6]].
  specialize (H1 ((|L| + 1) / ε)) as [δ2 [H7 H8]].
  exists (Rmin δ1 δ2). split; [solve_R | intros x H9].
  specialize (H6 x ltac:(solve_R)). specialize (H8 x ltac:(solve_R)).
  assert (H10 : |f x * g x| < |L| + 1) by solve_R.
  assert (H11 : ε * |f x| > |L| + 1).
  { apply Rmult_lt_compat_r with (r := ε) in H8; auto.
    field_simplify in H8; lra. }
  rewrite Rabs_mult in H10. rewrite Rminus_0_r.
  pose proof (Rabs_pos (f x)) as H12. nra.
Qed.

Lemma lemma_5_23_c : ∀ (f : R → R) (a : R),
  (~ ∃ L, ⟦ lim a ⟧ f = L /\ L ≠ 0) ->
  (~ (⟦ lim a ⟧ (λ x, |f x|) = ∞ )) ->
  ∃ g, (~ ∃ L1, ⟦ lim a ⟧ g = L1) /\ ∃ L2, ⟦ lim a ⟧ (λ x, f x * g x) = L2.
Proof. Abort.