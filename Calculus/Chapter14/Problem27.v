From Calculus.Chapter14 Require Import Prelude Problem25.

Lemma lemma_14_27_a :
  ∃ L, ∫ -∞ ∞ (λ x, 1 / (1 + x^2)) = L.
Proof.
  set (f := λ x : ℝ, 1 / (1 + x^2)).
  destruct lemma_14_25_d as [L [H1 H2]].
  assert (H3 : ⟦ der ⟧ (λ x, ∫ 0 x f) = f) by (apply FTC1_global; unfold f; auto_cont).
  assert (H4 : ⟦ der ⟧ (λ x, - ∫ 0 (-x) f) = f).
  {
    apply derivative_ext with (f1' := λ x, -(f (-x) * -1)).
    - intros x. unfold f. field. nra.
    - apply derivative_neg.
      change (⟦ der ⟧ ((λ x, ∫ 0 x f) ∘ (λ x, -x)) = (f ∘ (λ x, -x)) ⋅ (λ _, -1)).
      apply derivative_comp; [auto_diff | exact H3].
  }
  exists (L + L), 0, L, L. split; [| split; [split; assumption | reflexivity]].
  split.
  - intros x H5. apply theorem_13_3; [lra | unfold f; auto_cont].
  - intros ε H5. destruct (H2 ε H5) as [N H6].
    exists (- Rmax N 0). intros x H7.
    assert (H8 : x < 0 /\ -x > N) by solve_R.
    specialize (H6 (-x) ltac:(lra)).
    assert (H9 : ∫ x 0 f = ∫ 0 (-x) f).
    {
      replace (∫ 0 (-x) f) with ((λ t, - ∫ 0 (-t) f) 0 - (λ t, - ∫ 0 (-t) f) x)
        by (cbn beta; replace (-0) with 0 by lra; rewrite integral_n_n; lra).
      apply FTC2 with (g := λ t, - ∫ 0 (-t) f); [lra | unfold f; auto_cont |].
      apply derivative_imp_derivative_on; [apply differentiable_domain_closed; lra | exact H4].
    }
    change (|∫ x 0 f - L| < ε). rewrite H9. exact H6.
Qed.

Lemma lemma_14_27_b :
  ~ (∃ L, ∫ -∞ ∞ (λ x, x) = L).
Proof.
  intros [L [c [L1 [L2 [H1 [[H2 H3] H4]]]]]].
  destruct (H3 1 ltac:(lra)) as [N H5].
  set (x := Rmax N (Rmax c (|c| + |L2| + 3)) + 1).
  assert (H6 : x > N /\ x > c /\ x > |c| + |L2| + 3) by (unfold x; solve_R).
  specialize (H5 x ltac:(lra)).
  assert (H7 : ∫ c x (λ t, t) = x^2 / 2 - c^2 / 2).
  { apply FTC2 with (g := λ t, t^2 / 2); [lra | auto_cont | auto_diff]. }
  rewrite H7 in H5. solve_R.
Qed.

Lemma lemma_14_27_b' :
  ⟦ lim ∞ ⟧ (λ N, ∫ (-N) N (λ x, x)) = 0.
Proof.
  intros ε H1. exists 0. intros N H2.
  assert (H3 : ∫ (-N) N (λ x, x) = 0).
  {
    replace 0 with (N^2 / 2 - (-N)^2 / 2) by field.
    apply FTC2 with (g := λ x, x^2 / 2); [lra | auto_cont | auto_diff].
  }
  rewrite H3. solve_R.
Qed.

Lemma lemma_14_27_c : ∀ f L,
  ∫ -∞ ∞ f = L ->
  ⟦ lim ∞ ⟧ (λ N, ∫ (-N) N f) = L.
Abort.
