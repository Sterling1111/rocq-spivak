From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_25 : ∀ f f' a d,
  ⟦ der a ⟧ f = f' ->
  (∀ x, d x = f x - f' a * (x - a) - f a) ->
  ⟦ der a ⟧ d = λ _, 0.
Proof.
  intros f f' a d H1 H2.
  replace d with (λ x, f x - f' a * (x - a) - f a).
  2 : { extensionality x. rewrite H2. reflexivity. }
  apply derivative_at_ext_val with (f' := λ x, (f' x - f' a * (1 - 0)) - 0); try lra.
  apply derivative_at_minus; [ apply derivative_at_minus |]; auto_diff.
Qed.