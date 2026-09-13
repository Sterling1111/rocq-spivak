From Calculus.Chapter9 Require Import Prelude.
Open Scope R_scope.

Lemma lemma_9_10 : ∀ f f' g g',
  ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' ->
  (∀ t, (∀ y, f y = g (t + y)) -> ∀ x, f' x = g' (t + x)) /\
  (∀ x, (∀ t, f t = g (t + x)) -> f' x = g' (2 * x)).
Proof.
  intros f f' g g' H1 H2. split.
  - intros t H3 x.
    rewrite (derivative_unique f f' (λ x, g' (t + x)) H1); auto.
    replace f with (λ y, g (t + y)) by (extensionality y; auto).
    auto_diff.
  - intros x H4.
    rewrite (derivative_unique f f' (λ t, g' (t + x)) H1).
    + replace (x + x)  with (2 * x) by lra. auto.
    + replace f with (λ t, g (t + x)) by (extensionality t; auto).
      auto_diff.
Qed.