From Calculus.Chapter5 Require Import Prelude Problem34.

Lemma lemma_5_36_b : ∀ (f : R -> R) L,
  ⟦ lim ∞ ⟧ f = L <-> ⟦ lim -∞ ⟧ (λ x, f (-x)) = L.
Proof.
  intros f L. split; intros H1 ε H2;
  specialize (H1 ε H2) as [N H3]; exists (-N); intros x H4.
  - apply H3. lra.
  - specialize (H3 (-x) ltac:(lra)). rewrite Ropp_involutive in H3. exact H3.
Qed.

Lemma lemma_5_36_c : ∀ (f : R -> R) L,
  ⟦ lim 0⁻ ⟧ (λ x, f (1 / x)) = L <-> ⟦ lim -∞ ⟧ f = L.
Proof.
  intros f L.
  assert (H1 : ⟦ lim 0⁻ ⟧ (λ x, f (1 / x)) = L <->
    ⟦ lim 0⁺ ⟧ (λ x, f (- (1 / x))) = L).
  {
    split; intros H2 ε H3;
    specialize (H2 ε H3) as [δ [H4 H5]];
    exists δ; split; auto; intros x H6;
    specialize (H5 (-x) ltac:(lra)).
    - replace (1 / -x) with (- (1 / x)) in H5 by (unfold Rdiv; rewrite Rinv_opp; ring).
      exact H5.
    - replace (- (1 / -x)) with (1 / x) in H5 by (unfold Rdiv; rewrite Rinv_opp; ring).
      exact H5.
  }
  rewrite H1, (lemma_5_34 (λ x, f (-x)) L), lemma_5_36_b.
  replace (λ x, f (- -x)) with f by (extensionality x; rewrite Ropp_involutive; reflexivity).
  reflexivity.
Qed.
