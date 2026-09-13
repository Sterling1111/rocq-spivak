From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_21_a : ∀ f c a b,
  a < b -> ⟦ der ⟧ f (a,b) = (λ x, c * f x) ->
  (∀ x, a < x < b -> f x <> 0) ->
  ∃ l, l > 0 /\ ∀ x, a < x < b -> |f x| = l * exp (c*x).
Abort.

Lemma lemma_18_21_a_cor : ∀ f c a b,
  a < b -> ⟦ der ⟧ f (a,b) = (λ x, c * f x) ->
  (∀ x, a < x < b -> f x <> 0) ->
  ∃ k, ∀ x, a < x < b -> f x = k * exp (c*x).
Abort.

Lemma lemma_18_21_b : ∀ f c a b,
  a < b -> ⟦ der ⟧ f (a,b) = (λ x, c * f x) ->
  ∃ k, ∀ x, a < x < b -> f x = k * exp (c*x).
Abort.

Lemma lemma_18_21_c : ∀ f c,
  ⟦ der ⟧ f = (λ x, c * f x) ->
  ⟦ der ⟧ (λ x, f x / exp (c * x)) = (λ _, 0).
Proof.
  intros f c H1. auto_diff.
Qed.

Lemma lemma_18_21_c_interval : ∀ f c a b,
  a < b -> ⟦ der ⟧ f (a,b) = (λ x, c * f x) ->
  ∃ k, ∀ x, a < x < b -> f x = k * exp (c*x).
Abort.

Lemma lemma_18_21_d : ∀ f g g' a b,
  a < b -> ⟦ der ⟧ g (a,b) = g' ->
  ⟦ der ⟧ f (a,b) = (λ x, f x * g' x) ->
  ∃ k, ∀ x, a < x < b -> f x = k * exp (g x).
Abort.
