From Calculus.Chapter14 Require Import Prelude.

Lemma lemma_14_24_a : ∀ f f' f'' f''',
  ⟦ der ⟧ f = f' ->
  ⟦ der ⟧ f' = f'' ->
  ⟦ der ⟧ f'' = f''' ->
  (∀ x, f' x <> 0) ->
  (∀ x, f''' x / f' x - 3/2 * (f'' x / f' x)^2 = 0) ->
  ∃ c, ∀ x, (f'' x)^2 / (f' x)^3 = c.
Proof.
  intros f f' f'' f''' H1 H2 H3 H4 H5.
  apply derivative_zero_imp_const'.
  assert (H6 : ∀ x, 2 * f' x * f''' x - 3 * (f'' x)^2 = 0).
  {
    intros x. specialize (H4 x). specialize (H5 x).
    field_simplify in H5; [| exact H4].
    apply Rmult_eq_compat_r with (r := 2 * (f' x)^2) in H5.
    field_simplify in H5; nra.
  }
  apply derivative_ext with
    (f1' := λ x, (2 * f'' x * f''' x * (f' x)^3 -
      (f'' x)^2 * (3 * (f' x)^2 * f'' x)) / ((f' x)^3)^2).
  - intros x. specialize (H4 x). specialize (H6 x).
    replace (2 * f'' x * f''' x * (f' x)^3 -
      (f'' x)^2 * (3 * (f' x)^2 * f'' x)) with
      ((f' x)^2 * f'' x * (2 * f' x * f''' x - 3 * (f'' x)^2)) by ring.
    rewrite H6. field. auto.
  - auto_diff.
Qed.

Lemma lemma_14_24_b : ∀ f f' f'' f''',
  ⟦ der ⟧ f = f' ->
  ⟦ der ⟧ f' = f'' ->
  ⟦ der ⟧ f'' = f''' ->
  (∀ x, f' x <> 0) ->
  (∀ x, f''' x / f' x - 3/2 * (f'' x / f' x)^2 = 0) ->
  ∃ a b c d, ∀ x, c * x + d <> 0 -> f x = (a * x + b) / (c * x + d).
Abort.
