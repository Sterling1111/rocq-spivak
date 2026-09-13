From Calculus.Chapter3 Require Export Prelude.

Lemma lemma_3_21_a : ∃ f g h : R -> R,
  (f ∘ (g + h))%function <> ((f ∘ g) + (f ∘ h))%function.
Proof.
  exists (λ x, x^2), (λ _, 1), (λ _, 1).
  intro H1. apply (f_equal (λ f, f 0)) in H1. unfold compose in H1. nra.
Qed.

Lemma lemma_3_21_b : ∀ f g h : R -> R,
  ((g + h) ∘ f)%function = ((g ∘ f) + (h ∘ f))%function.
Proof.
  reflexivity.
Qed.

Lemma lemma_3_21_c : ∀ (f g : R -> R) x, f (g x) <> 0 ->
  (∕ (f ∘ g))%function x = ((∕ f) ∘ g)%function x.
Proof.
  reflexivity.
Qed.

Lemma lemma_3_21_d : ∃ (f g : R -> R) (x : R),
  f (g x) <> 0 /\ g x <> 0 /\
  (∕ (f ∘ g))%function x <> (f ∘ (∕ g))%function x.
Proof.
  exists (λ _, 2), (λ _, 1), 0. unfold compose. repeat split; lra.
Qed.
