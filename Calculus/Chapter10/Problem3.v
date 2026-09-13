From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_3_i : ∀ x,
  cos x <> 0 -> ⟦ der x ⟧ tan = sec ^ 2.
Proof.
  intros x H1. unfold sec.
  auto_diff.
Qed.

Lemma lemma_10_3_ii : ∀ x,
  sin x <> 0 -> ⟦ der x ⟧ cot = (λ y, - (csc y)^2).
Proof.
  auto_diff.
Qed.

Lemma lemma_10_3_iii : ∀ x,
  cos x <> 0 -> ⟦ der x ⟧ sec = (λ y, sec y * tan y).
Proof.
  auto_diff.
Qed.

Lemma lemma_10_3_iv : ∀ x,
  sin x <> 0 -> ⟦ der x ⟧ csc = (λ y, - csc y * cot y).
Proof.
  auto_diff.
Qed.