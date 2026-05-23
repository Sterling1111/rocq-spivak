From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_22_a : forall f f' x,
  ⟦ der x ⟧ f = f' ->
  ⟦ lim 0 ⟧ (fun h => (f (x + h) - f (x - h)) / (2 * h)) = f' x.
Proof.
  intros f f' x H1 ε H2.
  specialize (H1 (ε / 2) ltac:(lra)) as [δ [H3 H4]].
  exists δ; split; auto.
  intros y H5.
  specialize (H4 y H5) as H6.
  specialize (H4 (-y) ltac:(solve_R)) as H7.
  replace (x + - y) with (x - y) in H7 by lra.
  replace ((f (x + y) - f (x - y)) / (2 * y)) 
    with ((1/2) * ((f (x + y) - f x) / y) + (1/2) * ((f (x - y) - f x) / -y)) by solve_R.
  solve_R.
Qed.

Definition right_limit_2d (f : ℝ -> ℝ -> ℝ) (a1 a2 L : ℝ) : Prop :=
  ∀ ε, ε > 0 -> ∃ δ, δ > 0 /\ ∀ x y, 0 < x - a1 < δ -> 0 < y - a2 < δ -> |f x y - L| < ε.

Notation "⟦ 'lim' a1 ⁺ a2 ⁺ ⟧ f '=' L" := 
  (right_limit_2d f a1 a2 L)
    (at level 70, f at level 0, no associativity, format "⟦  'lim'  a1 ⁺  a2 ⁺  ⟧  f  '='  L") : limit_scope.

Lemma lemma_9_22_b : ∀ f f' x,
  ⟦ der x ⟧ f = f' ->
  ⟦ lim 0⁺ 0⁺ ⟧ (λ h k, (f (x + h) - f (x - k)) / (h + k)) = f' x.
Proof.
  intros f f' x H1 ε H2.
  specialize (H1 ε H2) as [δ [H3 H4]].
  exists δ; split; auto.
  intros h k H5 H6.
  specialize (H4 h ltac:(solve_R)) as H7.
  specialize (H4 (-k) ltac:(solve_R)) as H8.
  replace (x + - k) with (x - k) in H8 by lra.

  replace (((f (x + h) - f (x - k)) / (h + k)) - f' x)
    with ((h / (h + k)) * (((f (x + h) - f x) / h) - f' x) + (k / (h + k)) * (((f (x - k) - f x) / - k) - f' x)) by solve_R.
  
  apply Rle_lt_trans with (r2 := |((h / (h + k)) * (((f (x + h) - f x) / h) - f' x))| + 
                                 |((k / (h + k)) * (((f (x - k) - f x) / - k) - f' x))|); [solve_R |].
  replace ε with ((h / (h + k)) * ε + (k / (h + k)) * ε) by solve_R.
  apply Rplus_lt_compat.
  - rewrite Rabs_mult, Rabs_right.
    2: { apply Rdiv_ge_0; solve_R. }
    apply Rmult_lt_compat_l; [ apply Rdiv_pos_pos; lra | exact H7 ].
  - rewrite Rabs_mult, Rabs_right.
    2: { apply Rdiv_ge_0; solve_R. }
    apply Rmult_lt_compat_l; [apply Rdiv_pos_pos; lra | exact H8].
Qed.