From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_24 : ∀ f a b,
  continuous f ->
  ∫ a b f = ∫ a b (λ x, f (a + b - x)).
Proof.
  intros f a b H1.
  set (g := λ x : ℝ, a + b - x).
  set (g' := λ x : ℝ, -1).
  assert (H2 : continuous g') by (unfold g'; auto_cont).
  assert (H3 : ⟦ der ⟧ g = g') by (unfold g, g'; auto_diff).
  pose proof FTC1_global f a H1 as H4.
  pose proof substitution_formula f g g' (λ x, ∫ a x f) a b H1 H2 H4 H3 as H5.
  replace (g a) with b in H5 by (unfold g; lra).
  replace (g b) with a in H5 by (unfold g; lra).
  assert (H6 : (f ∘ g ⋅ g')%function = (λ x, -1 * f (a + b - x))).
  { extensionality x. unfold compose, g, g'. lra. }
  rewrite H6 in H5.
  rewrite integral_b_a_neg in H5.
  assert (H7 : a < b \/ a = b \/ b < a) by lra.
  destruct H7 as [H7 | [H7 | H7]].
  - assert (H8 : integrable_on a b (λ x : ℝ, f (a + b - x))).
    { apply theorem_13_3; auto_cont. }
    rewrite integral_mult_scalar in H5; auto.
    unfold g. 
    lra.
  - subst.
    repeat rewrite integral_n_n.
    lra.
  - assert (H8 : integrable_on b a (λ x : ℝ, f (a + b - x))).
    { apply theorem_13_3; auto_cont. }
    assert (H9 : ∫ a b (λ x : ℝ, -1 * f (a + b - x)) = - ∫ b a (λ x : ℝ, -1 * f (a + b - x))) by apply integral_b_a_neg.
    assert (H10 : ∫ a b (λ x : ℝ, f (a + b - x)) = - ∫ b a (λ x : ℝ, f (a + b - x))) by apply integral_b_a_neg.
    assert (H11 : ∫ b a (λ x : ℝ, -1 * f (a + b - x)) = -1 * ∫ b a (λ x : ℝ, f (a + b - x))).
    { apply integral_mult_scalar; auto. }
    unfold g.
    lra.
Qed.