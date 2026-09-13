From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_22_if : ∀ (f : R → R) (L : R),
  ⟦ lim 0 ⟧ f = L → 
  (∀ g, (~ ∃ L1, ⟦ lim 0 ⟧ g = L1) → (~ ∃ L2, ⟦ lim 0 ⟧ (λ x, f x + g x) = L2)).
Proof.
  intros f L H1 g H2 [L2 H3]. apply H2. exists (L2 - L).
  apply limit_eq with (f1 := λ x, (f x + g x) - f x).
  - exists 1. split; [lra | intros x H4; lra].
  - apply limit_minus; auto.
Qed.

Lemma lemma_5_22_only_if : ∀ (f : R → R),
  (∀ g, (~ ∃ L1, ⟦ lim 0 ⟧ g = L1) → (~ ∃ L2, ⟦ lim 0 ⟧ (λ x, f x + g x) = L2)) →
  ∃ L, ⟦ lim 0 ⟧ f = L.
Proof.
  intros f H1. apply NNPP. intros H2.
  apply (H1 (λ x, - f x)).
  - intros [L H3]. apply H2. exists (-L).
    apply limit_eq with (f1 := λ x, - - f x).
    + exists 1. split; [lra | intros x H4; lra].
    + apply limit_neg; auto.
  - exists 0. apply limit_eq with (f1 := λ _, 0).
    + exists 1. split; [lra | intros x H3; lra].
    + apply limit_const.
Qed.
