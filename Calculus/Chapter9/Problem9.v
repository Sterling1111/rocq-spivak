From Calculus.Chapter9 Require Import Prelude.
Open Scope R_scope.

Lemma lemma_9_9_i : ∀ f f' x,
  ⟦ der ⟧ f = f' -> f = (λ x, (x + 3) ^ 5) -> f' x = 5 * (x + 3)^4 /\ f' (x + 3) = 5 * (x + 3 + 3)^4.
Proof.
  intros f f' x H1 H2.
  rewrite (derivative_unique f f' (λ x, 5 * (x + 3)^4) H1 ltac:(subst; auto_diff)).
  lra.
Qed.

Lemma f_shift : ∀ (f g : R -> R) c,
  (∀ x, (f (x + c) = g x)) -> f = (λ x, g (x - c)).
Proof.
  intros f g c H1.
  extensionality x.
  specialize (H1 (x - c)).
  replace (x - c + c) with x in H1 by lra.
  apply H1.
Qed.

Lemma lemma_9_9_ii : ∀ f f' x,
  ⟦ der ⟧ f = f' -> (∀ x, f (x + 3) = x^5) -> f' x = 5 * (x - 3)^4 /\ f' (x + 3) = 5 * x^4.
Proof.
  intros f f' x H1 H2.
  pose proof f_shift f (λ x, x^5) 3 H2 as H3.
  rewrite (derivative_unique f f' (λ x, 5 * (x - 3)^4) H1 ltac:(subst; auto_diff)).
  lra.
Qed.

Lemma lemma_9_9_iii : ∀ f f' x,
  ⟦ der ⟧ f = f' -> (∀ x, f (x + 3) = (x + 5)^7) -> f' x = 7 * (x + 2)^6 /\ f' (x + 3) = 7 * (x + 5)^6.
Proof.
  intros f f' x H1 H2.
  pose proof f_shift f (λ x, (x + 5)^7) 3 H2 as H3.
  rewrite (derivative_unique f f' (λ x, 7 * (x + 2)^6) H1 ltac:(subst; auto_diff)).
  lra.
Qed.