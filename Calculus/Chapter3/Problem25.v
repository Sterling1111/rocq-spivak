From Calculus.Chapter3 Require Export Prelude.

Lemma lemma_3_25 : 
  ∃ f g : R -> R, g ∘ f = (λ x, x) /\ ~ ∃ h : R -> R, f ∘ h = (λ x, x).
Proof.
  set (f := λ x, if Rle_dec x 0 then x else x + 1).
  set (g := λ x, if Rle_dec x 0 then x else x - 1).
  exists f, g. split.
  - apply functional_extensionality. intro x. unfold compose, f, g.
    repeat destruct Rle_dec; lra.
  - intros [h H1]. apply (f_equal (λ k, k (1/2))) in H1.
    unfold compose, f in H1. destruct Rle_dec in H1; lra.
Qed.
