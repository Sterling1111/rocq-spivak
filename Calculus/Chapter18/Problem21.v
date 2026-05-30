From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_21_a : ∀ f c,
  ⟦ der ⟧ f = (fun x => c * f x) ->
  (∀ x, f x <> 0) ->
  ∃ l, l > 0 /\
    ∀ x, |f x| = l * exp (c * x).
Proof.
Abort.

Lemma lemma_18_21_a_cor : ∀ f c,
  ⟦ der ⟧ f = (fun x => c * f x) ->
  (∀ x, f x <> 0) ->
  ∃ k, ∀ x, f x = k * exp (c * x).
Abort.

Lemma lemma_18_21_b : ∀ f c,
  ⟦ der ⟧ f = (fun x => c * f x) ->
  ∃ k, ∀ x, f x = k * exp (c * x).
Abort.

Lemma lemma_18_21_c : ∀ f c,
  ⟦ der ⟧ f = (fun x => c * f x) ->
  ⟦ der ⟧ (fun x => f x / exp (c * x)) = (fun _ => 0).
Proof.
  intros f c H1. auto_diff.
Qed.

Lemma lemma_18_21_d : ∀ f g g',
  ⟦ der ⟧ g = g' ->
  ⟦ der ⟧ f = (fun x => f x * g' x) ->
  ∃ k, ∀ x, f x = k * exp (g x).
Proof.
Abort.
